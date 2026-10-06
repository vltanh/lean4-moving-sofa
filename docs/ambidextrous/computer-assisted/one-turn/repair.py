"""Does the least curvature-dominated repair ever decrease Baek's ONE-TURN
functional A(U) = |U| - |N(U)| ?  (The PR's GR1 shows it can decrease the
two-turn area.)  Caps are given by support values on a fine grid of [0, pi].
Repair: on each open quarter, replace u = h - 1 by its least sin-concave
majorant with the quarter's endpoint values fixed (equivalently, the concave
envelope of u/cos in the projective coordinate tan)."""
import numpy as np
from numpy import sin, cos, pi
import polycap as pc

L = pi / 2


def sin_concave_envelope(t, u):
    """least majorant v of u on the grid t (sorted, within an interval of
    length < pi) with v + v'' <= 0, endpoints fixed: v(t)=max over s1<=t<=s2
    of the sinusoidal interpolation of u between s1 and s2."""
    n = len(t)
    v = u.copy()
    for i in range(1, n - 1):
        s1 = t[:i + 1][:, None]
        s2 = t[i:][None, :]
        u1 = u[:i + 1][:, None]
        u2 = u[i:][None, :]
        den = sin(s2 - s1)
        with np.errstate(divide="ignore", invalid="ignore"):
            val = (sin(s2 - t[i]) * u1 + sin(t[i] - s1) * u2) / den
        val[den <= 1e-14] = -np.inf
        v[i] = max(u[i], np.nanmax(val))
    return v


def repair_upper(theta, h):
    """repair both open quarters of an upper support function sampled on a
    grid of [0, pi] containing pi/2."""
    hR = h.copy()
    iL = int(np.argmin(abs(theta - L)))
    for sl in (slice(0, iL + 1), slice(iL, len(theta))):
        tt = theta[sl]
        u = h[sl] - 1
        v = sin_concave_envelope(tt, u)
        hR[sl] = 1 + v
    return hR


def A_functional(theta, h, nt=1200, nx=3000):
    """|U| - |N(U)| for the cap with upper support function h on grid theta.
    Uses interpolation of h at hallway angles."""
    hf = lambda a: np.interp(a, theta, h)
    t = np.linspace(0, L, nt + 2)[1:-1]
    f, g = hf(t), hf(t + L)
    xr, xl = hf(np.array([0.0]))[0], -hf(np.array([pi]))[0]
    x = np.linspace(xl, xr, nx)
    th = theta[(theta > 0) & (theta < pi)]
    a = np.minimum(1.0, ((hf(th)[None, :] - x[:, None] * cos(th)[None, :])
                         / sin(th)[None, :]).min(axis=1))
    a = np.maximum(a, 0)
    st, ct = sin(t)[None, :], cos(t)[None, :]
    F = np.minimum((f[None, :] - 1 - x[:, None] * ct) / st,
                   (g[None, :] - 1 + x[:, None] * st) / ct).max(axis=1)
    U = np.trapezoid(a, x)
    N = np.trapezoid(np.maximum(F, 0), x)
    return U - N, U, N, xr - xl


def cap_support_from_polygon(theta_e, sig, theta):
    P = pc.vertices(theta_e, sig)
    return pc.support(P, theta)


if __name__ == "__main__":
    rng = np.random.default_rng(1)
    theta = np.linspace(0, pi, 361)          # includes pi/2 exactly
    import cand
    # 1) the candidate itself must be a fixed point (curvature dominated)
    h = cand.h_star_upper(theta)
    hR = repair_upper(theta, h)
    print("candidate: max |R(h)-h| = %.2e" % abs(hR - h).max())
    Ah = A_functional(theta, h)
    print("candidate A=%.6f |U|=%.6f |N|=%.6f W=%.6f  A-W/2=%.6f (M/2=%.6f)"
          % (Ah[0], Ah[1], Ah[2], Ah[3], Ah[0] - Ah[3] / 2, cand.M / 2))
    # 2) random polygon caps (all curvature in atoms)
    n = 8
    q = (np.arange(n) + 0.5) / n * L
    th_e = np.concatenate([[0.0], q, [L], q + L, [pi]])
    worst = 1e9
    for k in range(60):
        sig = rng.random(len(th_e)) ** 2
        sig[0] *= rng.random()
        sig[-1] *= rng.random()
        sig[n + 1] = rng.random() * 2.0         # top face length
        sig = pc.normalize(th_e, sig)
        hp = cap_support_from_polygon(th_e, sig, theta)
        hpR = repair_upper(theta, hp)
        A0 = A_functional(theta, hp)
        A1 = A_functional(theta, hpR)
        d = A1[0] - A0[0]
        worst = min(worst, d)
        if k < 12 or d < 0:
            print("k=%2d W=%.3f  A=%.5f -> A(R)=%.5f  diff=%+.5f  (hull %+.5f niche %+.5f)"
                  % (k, A0[3], A0[0], A1[0], d, A1[1] - A0[1], A1[2] - A0[2]))
    print("min A(R)-A over random polygon caps: %+.6f" % worst)
