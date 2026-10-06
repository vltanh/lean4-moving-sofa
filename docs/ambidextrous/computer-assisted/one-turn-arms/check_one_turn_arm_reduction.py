#!/usr/bin/env python3
"""Floating-point companion checks for one-turn-arm-reduction.md (labels AR).

Nothing here is a certificate.  The proofs in the note are pen-and-paper; this
script replays the candidate constants, sanity-tests the arm-propagation
inequalities and the discrete exposure statements on samples, reproduces the
negative examples of Section 8 with their swallowtail mechanism and a fold-free
control, and runs the Section 9 saturated-balance diagnostic.

Conventions (as in the note): L=pi/2, f(t)=h(t), g(t)=h(t+L) on [0,L],
p=f'-g+1, q=g'+f-1, rho_f=f''+f, rho_g=g''+g, p'=rho_f-1-q, q'=rho_g-1+p.
Caps are generated from (p,q) with the translation normalisation f(0)=1 and
the height normalisation g(0)=1; f(L)=1 is equivalent to
H(L)=int_0^L (p sin t + q cos t) dt = 0.

Usage:  python3 check_one_turn_arm_reduction.py [output.json]
"""
import hashlib
import json
import platform
import sys
import time

import numpy as np
import scipy
from numpy import pi
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, fsolve

L = pi / 2


def kappa(z):
    return max(abs(z), (1.0 + abs(z)) / 2.0)


# ---------------------------------------------------------------------------
# exact candidate constants (AF2 Case 3 / Note 14)
# ---------------------------------------------------------------------------
Y = brentq(lambda y: 4 * y ** 3 + 3 * y - 1, 0.0, 1.0, xtol=1e-16)
BETA = np.arctan(Y)
SB = np.sin(BETA)
M = 1 + 4 * Y ** 2 + np.arctan(Y)
A_STAR = 1 / (3 * SB)                 # half width
Q0_STAR = 1 / (2 * SB) - 1            # q(0+) of the candidate
Z = 1 / np.tan(BETA) - 2              # switching momentum z=cot(beta)-2
RHO_MAX_STAR = 1 / (4 * np.tan(BETA))  # (1+z/2)/2 = cot(beta)/4


# ---------------------------------------------------------------------------
# ODE helpers
# ---------------------------------------------------------------------------
def make_rhs(rho):
    """rho(t,p,q) -> (rho_f, rho_g)."""
    def rhs(t, y):
        p, q, f, g, H = y
        rf, rg = rho(t, p, q)
        return [rf - 1 - q, rg - 1 + p, p + g - 1, q - f + 1, p * np.sin(t) + q * np.cos(t)]
    return rhs


def dense(rho, q0, p0=0.5):
    s = solve_ivp(make_rhs(rho), [0, L], [p0, q0, 1.0, 1.0, 0.0], dense_output=True,
                  rtol=1e-11, atol=1e-13, max_step=2e-3)
    return s.sol


def endpoint(rho, q0, p0=0.5):
    s = solve_ivp(make_rhs(rho), [0, L], [p0, q0, 1.0, 1.0, 0.0], rtol=1e-10, atol=1e-12, max_step=1e-3)
    return s.y[:, -1]


def roof(sol, x, nt=4001, chunk=400):
    """Signed interior roof sup_{0<t<L} min(R_t(x),L_t(x)): discrete argmax on nt angles,
    then golden-section refinement in the neighbouring bracket (dense interpolant)."""
    t = np.linspace(0, L, nt)[1:-1]
    Yv = sol(t)
    f, g = Yv[2], Yv[3]
    st, ct = np.sin(t), np.cos(t)
    dt = t[1] - t[0]
    best = np.empty(len(x))
    targ = np.empty(len(x))
    for i in range(0, len(x), chunk):
        xx = x[i:i + chunk, None]
        V = np.minimum((f - 1 - xx * ct) / st, (g - 1 + xx * st) / ct)
        k = V.argmax(axis=1)
        best[i:i + chunk] = V[np.arange(len(k)), k]
        targ[i:i + chunk] = t[k]
    a = np.clip(targ - dt, 1e-9, L - 1e-9)
    b = np.clip(targ + dt, 1e-9, L - 1e-9)
    gr = (np.sqrt(5) - 1) / 2

    def V(tt):
        Yt = sol(tt)
        return np.minimum((Yt[2] - 1 - x * np.cos(tt)) / np.sin(tt), (Yt[3] - 1 + x * np.sin(tt)) / np.cos(tt))

    c = b - gr * (b - a)
    d = a + gr * (b - a)
    fc, fd = V(c), V(d)
    for _ in range(60):
        m = fc > fd
        b = np.where(m, d, b)
        a = np.where(m, a, c)
        c = b - gr * (b - a)
        d = a + gr * (b - a)
        fc, fd = V(c), V(d)
    return np.maximum(V(0.5 * (a + b)), best)


def evaluate(sol, rho=None, nx=20001, nt=4001):
    """Area C, functional F (A.1), SR1 right side S, niche |N|, A=C-|N|, W, T, Psi."""
    t = np.linspace(0, L, 200001)
    p, q, f, g, H = sol(t)
    fp, gp = p + g - 1, q - f + 1
    C = 0.5 * np.trapezoid(f ** 2 - fp ** 2 + g ** 2 - gp ** 2, t)
    pm, qp = np.minimum(p, 0), np.maximum(q, 0)
    I = 0.5 * np.trapezoid((f - 1) ** 2 + (g - 1) ** 2 + (f - 1) * gp - (g - 1) * fp, t)
    S = -I + 0.5 * np.trapezoid(pm ** 2 + qp ** 2, t)
    F = C + I - 0.5 * np.trapezoid(pm ** 2 + qp ** 2, t)
    x0, x1 = f[0] - 1, 1 - g[-1]                      # axis-quadrant abscissae
    xtl, xtr = -gp[0], -fp[-1]
    lo, hi = min(xtl, x0, x1) - 0.02, max(xtr, x0, x1) + 0.02
    x = np.linspace(lo, hi, nx)
    lam_int = roof(sol, x, nt=nt)
    lam = np.where((x < x0) | (x > x1), np.maximum(lam_int, 0.0), lam_int)   # SR1 signed roof
    N = np.trapezoid(np.maximum(lam, 0), x)
    Lneg = np.trapezoid(np.maximum(-lam, 0), x)
    W = f[0] + g[-1]
    T = xtr - xtl
    out = dict(C=C, F=F, S=S, N=N, A=C - N, A_minus_F=C - N - F, int_Lambda_minus=Lneg,
               W=W, T=T, Psi=C - N - W / 2, Psi_minus_Mhalf=C - N - W / 2 - M / 2,
               q_L_plus_half=q[-1] + 0.5, f_L_minus_1=f[-1] - 1, p0=p[0], q0=q[0],
               p_min=p.min(), p_max=p.max(), q_min=q.min(), q_max=q.max(), p_L=p[-1],
               arm_right=1 + q[0], arm_left=1 - p[-1])
    if rho is not None:
        tt = t[::20]
        R = np.array([rho(a, b, c) for a, b, c in zip(tt, p[::20], q[::20])])
        out.update(rho_f_max=R[:, 0].max(), rho_g_max=R[:, 1].max(), rho_min=R.min())
    return out


# ---------------------------------------------------------------------------
# Euler-Lagrange (saturated) laws of AF (A.8)-(A.9), written in (p,q)
# ---------------------------------------------------------------------------
def af_law(t, p, q):
    if p >= 0 and q >= 0:
        return 0.0, 0.5
    if p <= 0 and q >= 0:
        return (1 + q) / 2, (1 - p) / 2
    if p <= 0 and q <= 0:
        return 0.5, 0.0
    return -q, p


def part_A():
    """Candidate: constants, closed forms, value Psi=M/2, A=F, curvature<1."""
    res = dict(Y=Y, beta=BETA, M=M, M_half=M / 2, a_star=A_STAR, W_star=2 * A_STAR,
               q0_star=Q0_STAR, arm_star=1 + Q0_STAR, z=Z, rho_max_closed_form=RHO_MAX_STAR,
               relation_A18=2 * np.arctan(2 * Y) - (pi / 4 + np.arctan(Y)),
               value_cot_beta_minus_2_plus_beta_minus_M=1 / np.tan(BETA) - 2 + BETA - M,
               sin_beta_lt_one_third=bool(SB < 1 / 3), z_in_0_2=bool(0 <= Z < 2))
    sol = dense(af_law, Q0_STAR)
    ev = evaluate(sol, rho=af_law, nx=20001, nt=4001)
    res.update({"eval_" + k: v for k, v in ev.items()})
    res["W_minus_2a_star"] = ev["W"] - 2 * A_STAR
    res["T_minus_a_star"] = ev["T"] - A_STAR
    res["rho_max_minus_closed_form"] = max(ev["rho_f_max"], ev["rho_g_max"]) - RHO_MAX_STAR
    return res


# ---------------------------------------------------------------------------
# Part B: random sanity test of the arm propagation inequalities AR5 / AR5'
# ---------------------------------------------------------------------------
def part_B(trials=300, seed=7):
    rng = np.random.default_rng(seed)
    stats = {"WR5": dict(kept=0, worst=-np.inf), "AR7": dict(kept=0, worst=-np.inf)}
    for law in ["WR5", "AR7"]:
        for _ in range(trials):
            q0 = rng.uniform(-0.95, 1.9)
            K = 10
            uf = rng.uniform(0, 1, K) ** rng.uniform(0.2, 3)
            ug = rng.uniform(0, 1, K) ** rng.uniform(0.2, 3)

            def rho(t, p, q, uf=uf, ug=ug):
                k = min(int(t / L * K), K - 1)
                rf, rg = uf[k] * kappa(q), ug[k] * kappa(p)
                if law == "AR7":
                    if p > 0 and q > 0:
                        rf, rg = 0.0, min(rg, 0.5)
                    elif p < 0 and q < 0:
                        rf, rg = min(rf, 0.5), 0.0
                return rf, rg

            def rhs(t, y):
                p, q = y
                rf, rg = rho(t, p, q)
                return [rf - 1 - q, rg - 1 + p]

            s = solve_ivp(rhs, [0, L], [0.5, q0], rtol=1e-9, atol=1e-11, max_step=2e-3)
            p, q = s.y
            if p.max() > 1 + 1e-12 or q.min() < -1 - 1e-12:
                continue                      # not realisable by a cap (Lemma AR0)
            bound = max(q0 + 1 / 24, 2 / 3) if law == "WR5" else max(q0, 1 / 8)
            stats[law]["kept"] += 1
            stats[law]["worst"] = max(stats[law]["worst"], q.max() - bound)
    return stats


# ---------------------------------------------------------------------------
# Part C: negative examples (Section 8)
# ---------------------------------------------------------------------------
def fold_rho(lam, t1, t2):
    lf, lg = lam

    def rho(t, p, q):
        if t < t1:
            rf = 0.0
        elif t < t2:
            rf = kappa(q)
        else:
            rf = lf * kappa(q)
        return rf, lg * kappa(p)
    return rho


def shoot_fold(q0, t1, t2):
    def res(lam):
        y = endpoint(fold_rho(lam, t1, t2), q0)
        return [y[1] + 0.5, y[4]]
    lam = fsolve(res, [0.5, 0.5], xtol=1e-12)
    return lam, res(lam)


def swallowtail_area(sol):
    """Signed area of the loop of B=(f-1)mu+f'nu on its active fold (p<0, B_x decreasing)."""
    t = np.linspace(1e-6, L - 1e-6, 400001)
    p, q, f, g, H = sol(t)
    fp = p + g - 1
    Bx = (f - 1) * np.cos(t) - fp * np.sin(t)
    By = (f - 1) * np.sin(t) + fp * np.cos(t)
    rev = np.where((np.diff(Bx) < 0) & (p[:-1] < 0))[0]
    if len(rev) == 0:
        return None
    c1, c2 = rev[0], rev[-1] + 1
    i1, i3 = np.arange(0, c1), np.arange(c2, len(t))
    xlo, xhi = Bx[c2], Bx[c1]
    xs = np.linspace(xlo, xhi, 20001)
    m1 = Bx[i1] >= xlo - 1e-9
    m3 = Bx[i3] <= xhi + 1e-9
    y1 = np.interp(xs, Bx[i1][m1], By[i1][m1])
    y3 = np.interp(xs, Bx[i3][m3], By[i3][m3])
    dd = y1 - y3
    k = np.where(np.sign(dd[:-1]) != np.sign(dd[1:]))[0]
    if len(k) == 0:
        return None
    xc = xs[k[0]]
    ta = i1[m1][np.argmin(np.abs(Bx[i1][m1] - xc))]
    tb = i3[m3][np.argmin(np.abs(Bx[i3][m3] - xc))]
    X, Yy = Bx[ta:tb + 1], By[ta:tb + 1]
    area = 0.5 * np.sum(X[:-1] * Yy[1:] - X[1:] * Yy[:-1]) + 0.5 * (X[-1] * Yy[0] - X[0] * Yy[-1])
    return dict(loop_signed_area=area, cusp_t=[t[c1], t[t2] if False else t[c2]], crossing_t=[t[ta], t[tb]],
                p_at_crossing=[p[ta], p[tb]])


def class_report(sol, rho):
    """Membership in the WR.4-WR.5 class, and measures of AR7 violations."""
    t = np.linspace(0, L, 40001)
    p, q, f, g, H = sol(t)
    R = np.array([rho(a, b, c) for a, b, c in zip(t, p, q)])
    rf, rg = R[:, 0], R[:, 1]
    kq = np.array([kappa(v) for v in q])
    kp = np.array([kappa(v) for v in p])
    dt = t[1] - t[0]
    A_ = (p > 0) & (q > 0)
    C_ = (p < 0) & (q < 0)
    return dict(
        WR5_violation_max=max((rf - kq).max(), (rg - kp).max()),
        rho_min=R.min(),
        active_fold_measure=float(np.sum((p < 0) & (rf > 1)) * dt),
        AR7_measure_rho_f_pos_on_pp=float(np.sum(A_ & (rf > 1e-12)) * dt),
        AR7_measure_rho_g_gt_half_on_pp=float(np.sum(A_ & (rg > 0.5 + 1e-12)) * dt),
        AR7_measure_rho_g_pos_on_mm=float(np.sum(C_ & (rg > 0.1 if False else 1e-12)) * dt),
        AR7_measure_rho_f_gt_half_on_mm=float(np.sum(C_ & (rf > 0.5 + 1e-12)) * dt),
        baek_arms_nonneg=bool(p.max() <= 1 + 1e-12 and q.min() >= -1 - 1e-12))


def part_C0(q0=1.0):
    """Fold-free control in the curvature class: rho_f=lam_f*kappa(q), rho_g=lam_g*kappa(p)."""
    def rho_of(lam):
        return lambda t, p, q: (lam[0] * kappa(q), lam[1] * kappa(p))

    def res(lam):
        y = endpoint(rho_of(lam), q0)
        return [y[1] + 0.5, y[4]]
    lam = fsolve(res, [0.6, 0.6], xtol=1e-12)
    rho = rho_of(lam)
    sol = dense(rho, q0)
    rec = dict(q0=q0, lam_f=lam[0], lam_g=lam[1], shoot_residual=list(map(float, res(lam))))
    rec.update(class_report(sol, rho))
    ev = evaluate(sol, rho=rho, nx=20001, nt=4001)
    rec.update({"eval_" + k: v for k, v in ev.items()})
    return rec


def part_C():
    out = []
    for q0, t1, t2 in [(1.5, 0.2, 0.5), (1.3, 0.25, 0.45)]:
        lam, r = shoot_fold(q0, t1, t2)
        rho = fold_rho(lam, t1, t2)
        sol = dense(rho, q0)
        rec = dict(q0=q0, t1=t1, t2=t2, lam_f=lam[0], lam_g=lam[1], shoot_residual=list(map(float, r)),
                   lam_in_unit_interval=bool(0 <= min(lam) and max(lam) <= 1))
        rec.update(class_report(sol, rho))
        e1 = evaluate(sol, rho=rho, nx=20001, nt=4001)
        e2 = evaluate(sol, rho=rho, nx=40001, nt=8001)
        rec.update({"eval_" + k: v for k, v in e1.items()})
        rec["A_minus_F_refined"] = e2["A_minus_F"]
        sw = swallowtail_area(sol)
        rec["swallowtail"] = sw
        out.append(rec)
    return out


# ---------------------------------------------------------------------------
# Part D: discrete exposure statements of AR7 on circumscribed grid polygons
# ---------------------------------------------------------------------------
def part_D(caps=6, n=48, seed=11):
    from shapely.geometry import LineString, Polygon, box
    from shapely.ops import unary_union
    rng = np.random.default_rng(seed)
    agg = {"a": [0, 0.0], "b": [0, -np.inf], "a_mirror": [0, 0.0]}
    for trial in range(caps):
        q0 = rng.uniform(0.3, 1.6)
        lam = rng.uniform(0.2, 1.0, 2)
        knots = rng.uniform(0.3, 1.0, 8) if trial % 2 else np.ones(8)

        def rho(t, p, q, knots=knots, lam=lam):
            k = knots[min(int(t / L * 8), 7)]
            return lam[0] * k * kappa(q), lam[1] * k * kappa(p)
        sol = dense(rho, q0)

        def h(theta):
            theta = np.asarray(theta, float)
            o = np.empty_like(theta)
            a = theta <= L
            o[a] = sol(theta[a])[2]
            o[~a] = sol(theta[~a] - L)[3]
            return o
        d = L / n
        c, s, T = np.cos(d), np.sin(d), np.tan(d / 2)
        th = np.arange(0, 2 * n + 1) * d
        hv = h(th)
        BIG = 30
        quads = []
        for j in range(1, n):
            mu = np.array([np.cos(th[j]), np.sin(th[j])])
            nu = np.array([-np.sin(th[j]), np.cos(th[j])])
            cor = (hv[j] - 1) * mu + (hv[j + n] - 1) * nu
            quads.append(Polygon([cor, cor - BIG * nu, cor - BIG * nu - BIG * mu, cor - BIG * mu]))
        bd = unary_union(quads).intersection(box(-BIG, 0, BIG, BIG)).boundary
        for j in range(2, n - 1):
            mu = np.array([np.cos(th[j]), np.sin(th[j])])
            nu = np.array([-np.sin(th[j]), np.cos(th[j])])
            f, g = hv[j], hv[j + n]
            cor = (f - 1) * mu + (g - 1) * nu
            p_plus = (hv[j + 1] - f * c) / s - g + 1
            p_minus = (f * c - hv[j - 1]) / s - g + 1
            d_plus = (hv[j + n + 1] - g * c) / s
            d_minus = (g * c - hv[j + n - 1]) / s
            q_plus, q_minus = f + d_plus - 1, f + d_minus - 1
            ell_c = d_plus - d_minus
            e_mu = bd.intersection(LineString([cor, cor - BIG * nu])).length
            e_nu = bd.intersection(LineString([cor, cor - BIG * mu])).length
            if p_plus > T and q_plus > T:
                agg["a"][0] += 1
                agg["a"][1] = max(agg["a"][1], e_mu)
            if p_plus > T and q_minus + T >= np.tan(d) * (p_minus + T):
                agg["b"][0] += 1
                agg["b"][1] = max(agg["b"][1], e_nu - max(2 * T - ell_c, 0.0))
            if p_minus < -T and q_minus < -T:
                agg["a_mirror"][0] += 1
                agg["a_mirror"][1] = max(agg["a_mirror"][1], e_nu)
    return {k: dict(cases=v[0], worst=v[1]) for k, v in agg.items()}


# ---------------------------------------------------------------------------
# Part E: saturated-balance diagnostic (unproved two-sided balance)
# ---------------------------------------------------------------------------
def saturated_law(t, p, q):
    if p > 0 and q > 0:
        return 0.0, 0.5
    if p < 0 and q < 0:
        return 0.5, 0.0
    if p >= 0 and q <= 0:
        return -q, p
    return kappa(q), kappa(p)            # standard regime, fold law q when q>1


def part_E():
    def hit_time(q0):
        ev = lambda t, y: y[1] + 0.5
        ev.terminal, ev.direction = True, -1
        s = solve_ivp(make_rhs(saturated_law), [0, 3 * pi], [0.5, q0, 1, 1, 0], events=ev,
                      rtol=1e-10, atol=1e-12, max_step=2e-3)
        return s.t_events[0][0] if len(s.t_events[0]) else np.inf
    qs = np.linspace(0.05, 2.5, 50)
    Ts = np.array([hit_time(v) for v in qs])
    root = brentq(lambda v: hit_time(v) - L, 0.5, 1.0, xtol=1e-12)
    return dict(q0_grid=qs.tolist(), hit_time=Ts.tolist(), strictly_increasing=bool(np.all(np.diff(Ts) > 0)),
                root_q0=root, root_minus_q0_star=root - Q0_STAR)


def main():
    t0 = time.time()
    src = open(__file__, "rb").read()
    out = dict(script_sha256=hashlib.sha256(src).hexdigest(), python=platform.python_version(),
               numpy=np.__version__, scipy=scipy.__version__)
    out["A_candidate"] = part_A()
    print("A done %.0fs" % (time.time() - t0), flush=True)
    out["B_arm_propagation_samples"] = part_B()
    print("B done %.0fs" % (time.time() - t0), flush=True)
    out["C0_fold_free_control"] = part_C0()
    out["C_negative_examples"] = part_C()
    print("C done %.0fs" % (time.time() - t0), flush=True)
    out["D_discrete_exposure"] = part_D()
    print("D done %.0fs" % (time.time() - t0), flush=True)
    out["E_saturated_balance_diagnostic"] = part_E()
    out["runtime_seconds"] = time.time() - t0

    def clean(o):
        if isinstance(o, dict):
            return {k: clean(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)):
            return [clean(v) for v in o]
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, np.bool_):
            return bool(o)
        return o
    out = clean(out)
    path = sys.argv[1] if len(sys.argv) > 1 else "one-turn-arm-reduction-checks.json"
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=False)
    print(json.dumps({k: out[k] for k in ["script_sha256", "runtime_seconds"]}))


if __name__ == "__main__":
    main()
