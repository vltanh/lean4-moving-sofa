"""Adversarial search for one-turn caps on which the least curvature-dominated
repair R decreases Baek's functional A(U) = |U| - |N(U)|.

Finds no decrease for W <= 2.8 on these polygon families, and decreases of
about 0.05 near W = 4.5.  GR1 (global-repair-counterexample.md) proves a
decrease at W = 63/25 in a regime far too thin for this search to see, so a
negative search result here is NOT evidence that repair is monotone.
Not a proof certificate.

    python3 repair_search.py --wmax 2.8 --seed 21
"""
import argparse
import numpy as np
from numpy import pi
from scipy.optimize import minimize
import polycap as pc
import repair as rp

L = pi / 2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wmax", type=float, default=2.8)
    ap.add_argument("--seed", type=int, default=21)
    ap.add_argument("--trials", type=int, default=5)
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    theta = np.linspace(0, pi, 241)
    n = 6
    q = (np.arange(n) + 0.5) / n * L
    th_e = np.concatenate([[0.0], q, [L], q + L, [pi]])

    def shape(z):
        return pc.normalize(th_e, np.clip(np.abs(z), 0, 3))

    def gap(z):
        sig = shape(z)
        P = pc.vertices(th_e, sig)
        W = P[0, 0] - P[-1, 0]
        if W > a.wmax:
            return 1.0 + (W - a.wmax)
        hp = rp.cap_support_from_polygon(th_e, sig, theta)
        hpR = rp.repair_upper(theta, hp)
        return (rp.A_functional(theta, hpR, nt=700, nx=2000)[0]
                - rp.A_functional(theta, hp, nt=700, nx=2000)[0])

    best = np.inf
    for trial in range(a.trials):
        z0 = rng.random(len(th_e)) ** 2
        z0[n + 1] = rng.random() * 2.0
        r = minimize(gap, z0, method="Nelder-Mead",
                     options=dict(maxiter=900, xatol=1e-6, fatol=1e-8))
        sig = shape(r.x)
        P = pc.vertices(th_e, sig)
        print("trial %d: min A(R U)-A(U) = %+.6f  W=%.3f face=%.3f"
              % (trial, r.fun, P[0, 0] - P[-1, 0], sig[n + 1]), flush=True)
        best = min(best, r.fun)
    print("overall minimum %+.6f (W <= %.2f)" % (best, a.wmax))


if __name__ == "__main__":
    main()
