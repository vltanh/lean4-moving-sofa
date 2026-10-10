"""Two-cap problem:  maximize |T_U cap rho(T_U' + shift)|  over asymmetric
pairs of polygon caps and a relative horizontal shift.  Reports the clipping
term |G| of OT1 at each optimum.  Not a proof certificate.

    python3 optimize_pairs.py --seed 1
"""
import argparse
import time
import numpy as np
from scipy.optimize import minimize
import cand
import polycap as pc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--normals", type=int, default=10)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    np.random.seed(a.seed)
    n = a.normals
    th, sg0 = pc.candidate_polygon(n)
    sg0 = pc.normalize(th, sg0)
    m = len(sg0)
    lo, hi = pc.Grid(400, 900), pc.Grid(2000, 4000)

    def unpack(z):
        return (pc.normalize(th, np.maximum(z[:m], 0)),
                pc.normalize(th, np.maximum(z[m:2 * m], 0)), z[-1])

    def obj(z):
        s1, s2, sh = unpack(z)
        return -pc.pair_area(th, s1, th, s2, sh, lo)

    zc = np.concatenate([sg0, sg0, [0.0]])
    print("candidate pair: %.6f   (M = %.6f)" % (-obj(zc), cand.M), flush=True)
    starts = []
    for amp in (0.1, 0.3):
        z = zc.copy()
        z[:2 * m] *= np.exp(amp * np.random.randn(2 * m))
        z[-1] = 0.05 * np.random.randn()
        starts.append(("perturb %.1f" % amp, z))
    starts.append(("random", np.concatenate(
        [np.random.rand(m) * 2 * sg0.mean(), np.random.rand(m) * 2 * sg0.mean(),
         [0.0]])))
    for label, z0 in starts:
        t0 = time.time()
        r = minimize(obj, z0, method="L-BFGS-B",
                     bounds=[(0, 5)] * (2 * m) + [(-1.5, 1.5)],
                     options=dict(maxiter=300, eps=1e-6))
        s1, s2, sh = unpack(r.x)
        d = pc.pair_area(th, s1, th, s2, sh, hi, return_parts=True)
        asym = np.abs(s1 - s2).sum() / np.abs(s1).sum()
        print("%-12s area=%.6f (fine %.6f) clip=%.1e asym=%.3f shift=%+.4f %.0fs"
              % (label, -r.fun, d["area"], d["clip"], asym, sh,
                 time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
