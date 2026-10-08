"""Diagnostic for the one-turn chain  A(V) <= F(V)  (SR1)  and
F(V) - W/2 <= M/2  (AF3), on curvature-dominated caps.

F is the half functional (A.1) of adaptive-functional-global-calibration.md.
Caps are random polygon caps repaired to be curvature dominated (repair.py).
Not a proof certificate: floating point, sampled caps, finite grids.

    python3 af_chain.py            # candidate value + 40 random repaired caps
    python3 af_chain.py --converge # refinement study of A - F on one cap
"""
import argparse
import numpy as np
from numpy import pi
import cand
import polycap as pc
import repair as rp

L = pi / 2


def F_half(theta, h, n=4000):
    """F(f, g) of (A.1) for an upper support function h sampled on theta."""
    t = np.linspace(0, L, n)
    f = np.interp(t, theta, h)
    g = np.interp(t + L, theta, h)
    fp, gp = np.gradient(f, t), np.gradient(g, t)
    p = fp - g + 1
    q = gp + f - 1
    integrand = (f**2 + g**2 - fp**2 - gp**2 + (f - 1)**2 + (g - 1)**2
                 + (f - 1) * gp - (g - 1) * fp
                 - np.minimum(p, 0)**2 - np.maximum(q, 0)**2)
    return 0.5 * np.trapezoid(integrand, t)


def random_cap(rng, n=8):
    q = (np.arange(n) + 0.5) / n * L
    th_e = np.concatenate([[0.0], q, [L], q + L, [pi]])
    sig = rng.random(len(th_e)) ** 2
    sig[n + 1] = rng.random() * 2.0
    return th_e, pc.normalize(th_e, sig)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--converge", action="store_true")
    ap.add_argument("--samples", type=int, default=40)
    a = ap.parse_args()
    if a.converge:
        rng = np.random.default_rng(5)
        random_cap(rng)
        th_e, sig = random_cap(rng)
        for ng, nt, nx in [(721, 1500, 4000), (1441, 3000, 8000),
                           (2881, 6000, 12000)]:
            theta = np.linspace(0, pi, ng)
            hR = rp.repair_upper(theta, rp.cap_support_from_polygon(th_e, sig, theta))
            A = rp.A_functional(theta, hR, nt=nt, nx=nx)
            Fv = F_half(theta, hR, n=8000)
            print("grid %5d: W=%.4f A=%.6f F=%.6f A-F=%+.2e"
                  % (ng, A[3], A[0], Fv, A[0] - Fv))
        return
    theta = np.linspace(0, pi, 2001)
    h = cand.h_star_upper(theta)
    A = rp.A_functional(theta, h, nt=2000, nx=5000)
    Fv = F_half(theta, h)
    print("candidate: F-W/2=%.6f  A-W/2=%.6f  M/2=%.6f"
          % (Fv - A[3] / 2, A[0] - A[3] / 2, cand.M / 2))
    rng = np.random.default_rng(5)
    theta = np.linspace(0, pi, 721)
    worst_enc, worst_cal = -9.0, -9.0
    for _ in range(a.samples):
        th_e, sig = random_cap(rng)
        hR = rp.repair_upper(theta, rp.cap_support_from_polygon(th_e, sig, theta))
        A1 = rp.A_functional(theta, hR, nt=1500, nx=4000)
        if A1[3] < 1:
            continue
        F1 = F_half(theta, hR)
        worst_enc = max(worst_enc, A1[0] - F1)
        worst_cal = max(worst_cal, F1 - A1[3] / 2 - cand.M / 2)
    print("max A-F over samples        = %+.2e (discretisation; see --converge)"
          % worst_enc)
    print("max F-W/2-M/2 over samples  = %+.4f (AF3 predicts <= 0)" % worst_cal)


if __name__ == "__main__":
    main()
