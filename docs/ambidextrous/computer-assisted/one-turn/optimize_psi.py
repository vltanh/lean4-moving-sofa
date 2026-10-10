"""Width-penalized one-turn problem:  maximize Psi(U) = |T_U| - W(U)/2
over polygon caps with fixed normals (edge lengths are the variables).

Starts: the candidate polygon, random caps, wide caps (W ~ 3.5-4.6) and
narrow caps (W ~ 1.3-1.8).  Each optimum is re-evaluated on a finer grid.
Not a proof certificate: local optimizer, finite angle grids.

    python3 optimize_psi.py --normals 14 --seed 3
"""
import argparse
import time
import numpy as np
from numpy import pi
from scipy.optimize import minimize
import cand
import polycap as pc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--normals", type=int, default=14,
                    help="normals per open quarter")
    ap.add_argument("--seed", type=int, default=3)
    ap.add_argument("--runs", type=int, default=3,
                    help="wide and narrow starts each")
    a = ap.parse_args()
    np.random.seed(a.seed)
    n = a.normals
    th, sg0 = pc.candidate_polygon(n)
    sg0 = pc.normalize(th, sg0)
    lo, hi = pc.Grid(500, 1100), pc.Grid(2500, 5000)

    def obj(z):
        return -pc.psi(th, pc.normalize(th, np.maximum(z, 0)), lo)

    def width(z):
        P = pc.vertices(th, pc.normalize(th, np.maximum(z, 0)))
        return P[0, 0] - P[-1, 0]

    dc = pc.psi(th, sg0, hi, return_parts=True)
    print("candidate polygon, %d normals: Psi=%.6f   M/2=%.6f"
          % (n, dc["T"] - dc["W"] / 2, cand.M / 2), flush=True)
    starts = [("candidate", sg0.copy())]
    for k in range(a.runs):
        z = np.random.rand(len(sg0)) ** 2
        z[n + 1] = 2.0 + np.random.rand()
        starts.append(("wide%d" % k, z))
        z = np.random.rand(len(sg0)) ** 2
        z[n + 1] = 0.05 * np.random.rand()
        z[0] = z[-1] = 0.6
        starts.append(("narrow%d" % k, z))
    for label, z0 in starts:
        t0 = time.time()
        r = minimize(obj, z0, method="L-BFGS-B", bounds=[(0, 6)] * len(z0),
                     options=dict(maxiter=500, eps=1e-6))
        s = pc.normalize(th, np.maximum(r.x, 0))
        d = pc.psi(th, s, hi, return_parts=True)
        print("%-10s start W=%.2f -> Psi=%.6f W=%.4f niche=%.3f "
              "ends=(%.3f,%.3f) face=%.3f %.0fs"
              % (label, width(z0), d["T"] - d["W"] / 2, d["W"],
                 d["alpha"].max(), s[0], s[-1], s[n + 1], time.time() - t0),
              flush=True)


if __name__ == "__main__":
    main()
