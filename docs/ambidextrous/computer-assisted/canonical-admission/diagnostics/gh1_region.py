"""Floating-point sanity check of the GH1 region (not a proof).

Tot(A,B0,C0; s,e) = y(sR+sD) + Pk + Pcut + mixed  (exact formula from GH.3).
For sampled heights, minimise Tot over 0<=s<=1, |e|<=s and compare the sign
with the sufficient conditions (GH-R), (GH-D).
"""
import numpy as np
from scipy.optimize import minimize

Y = float(np.real([r for r in np.roots([4, 0, 3, -1]) if abs(np.imag(r)) < 1e-12][0]))
y = Y
k = 2 * y / (1 + y * y)


def tot(h, v):
    A, B0, C0 = h
    sr, sd, er, ed = v
    Pk = ((A - B0) ** 2 + C0 ** 2) / 8 + (k - .25) * A * C0 + (k - .75) * B0 * C0
    Pc = ((y * y + 2 * y + 3 / y) * (er + ed) ** 2 + (1 + 3 / y) * (er - ed) ** 2) / 8 \
        - y * (sr ** 2 + sd ** 2 + 2 * y * sr * sd) / 4
    aR = (1 - y) / 2 * A + B0 + (1 - y) / 2 * C0
    aD = A + (1 - y) / 2 * B0 + C0
    g = (1 - y) / 4 * (A + B0 - C0)
    mix = -aR * sr - aD * sd - g * (er + ed)
    return y * (sr + sd) + Pk + Pc + mix


def min_tot(h, rng, starts=12):
    best = np.inf
    for _ in range(starts):
        z0 = rng.uniform(-1, 1, 4)
        def f(z):
            sr = 1 / (1 + np.exp(-z[0])); sd = 1 / (1 + np.exp(-z[1]))
            er = sr * np.tanh(z[2]); ed = sd * np.tanh(z[3])
            return tot(h, (sr, sd, er, ed))
        r = minimize(f, z0, method="Nelder-Mead", options=dict(xatol=1e-10, fatol=1e-13, maxiter=4000))
        best = min(best, r.fun)
    # vertices of the slack box
    for sr in (0, 1):
        for sd in (0, 1):
            for er in (-sr, 0, sr):
                for ed in (-sd, 0, sd):
                    best = min(best, tot(h, (sr, sd, er, ed)))
    return best


def conds(h):
    A, B0, C0 = h
    lin = y * (3 - y) / 4
    g = abs((1 - y) / 4 * (A + B0 - C0))
    cR = lin - ((1 - y) / 2 * A + B0 + (1 - y) / 2 * C0) - g
    cD = lin - (A + (1 - y) / 2 * B0 + C0) - g
    return min(cR, cD)


if __name__ == "__main__":
    rng = np.random.default_rng(0)
    worst_in, n_in, viol_out, n_out = np.inf, 0, 0, 0
    for i in range(400):
        h = rng.uniform(0, 0.25, 3) * rng.integers(0, 2, 3)
        m = min_tot(h, rng, starts=4)
        if conds(h) >= 0:
            n_in += 1
            worst_in = min(worst_in, m)
        else:
            n_out += 1
            viol_out += m < -1e-9
    print("inside GH1 region: %d samples, min Tot = %.3e" % (n_in, worst_in))
    print("outside: %d samples, %d with negative minimum" % (n_out, viol_out))
    # rays: first height level where the free minimum turns negative
    for name, dirv in [("A only", (1, 0, 0)), ("B0 only", (0, 1, 0)), ("C0 only", (0, 0, 1)),
                       ("crossed A=B0", (1, 1, 0)), ("shared B0=C0", (0, 1, 1)),
                       ("all equal", (1, 1, 1))]:
        dirv = np.array(dirv, float)
        lo, hi = 0.0, 1.0
        for _ in range(40):
            mid = (lo + hi) / 2
            if min_tot(mid * dirv, rng, starts=3) >= -1e-10:
                lo = mid
            else:
                hi = mid
        # GH1 sufficient threshold along the ray
        lo2, hi2 = 0.0, 1.0
        for _ in range(60):
            mid = (lo2 + hi2) / 2
            if conds(mid * dirv) >= 0:
                lo2 = mid
            else:
                hi2 = mid
        print("%-14s free-min threshold %.4f   GH1 sufficient threshold %.4f" % (name, lo, lo2))
