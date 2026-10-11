"""Local path search. Run python search.py --help; this is NOT a convex solver."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import platform

import numpy as np
import scipy
from scipy.optimize import minimize
import shapely

from geometry import Motion, largest_component, sampled_intersection, stationary_area, translation_area, validate_beta
from enclosure import enclose


def seed_path(beta: float, mode: str, knots: int, ax: float, ay: float) -> Motion:
    u = np.linspace(0, 1, knots)
    if mode == "forward":
        corners = np.column_stack((ax*np.cos(math.pi*u), ay*np.sin(math.pi*u)))
        corners[[0, -1], 1] = 0.0
    else:
        corners = np.column_stack((ax*(2*u-1)**2, u+ay*np.sin(2*math.pi*u)))
        corners[0, 1], corners[-1, 1] = 0.0, 1.0
    corners[knots//2, 0] = 0.0  # remove horizontal translation freedom
    return Motion(beta, mode, corners)


def optimize(beta: float, mode: str, knots: int = 9, subdivisions: int = 4,
             restarts: int = 2, maxiter: int = 100, seed: int = 0,
             initial: Motion | None = None) -> tuple[Motion, dict]:
    validate_beta(beta)
    if subdivisions < 1:
        raise ValueError("subdivisions must be positive")
    if knots < 3 or knots % 2 != 1 or restarts < 1 or maxiter < 1:
        raise ValueError("odd knots >= 3, restarts >= 1 and maxiter >= 1 required")
    # Bounds are search restrictions, not a compactness theorem.
    xlimit = 4.0/min(math.sin(beta/2), math.cos(beta/2))
    free = [i for i in range(2*knots) if i not in (1, 2*(knots-1)+1, 2*(knots//2))]
    template = seed_path(beta, mode, knots, 0.0, 0.0).corners.copy()
    def decode(x):
        c = template.copy().ravel()
        c[free] = x
        return Motion(beta, mode, c.reshape(-1, 2))
    bounds = [(-xlimit, xlimit) if i % 2 == 0 else (-2.0, 3.0) for i in free]
    best_area, best_motion, evaluations = -1.0, None, 0
    def objective(x):
        nonlocal best_area, best_motion, evaluations
        m = decode(x)
        area = float(largest_component(sampled_intersection(m, subdivisions)).area)
        evaluations += 1
        if area > best_area:
            best_area, best_motion = area, m
        return -area
    if initial is not None:
        if initial.beta != beta or initial.mode != mode:
            raise ValueError("initial motion must have matching beta and mode")
        old = np.linspace(0, 1, len(initial.corners))
        new = np.linspace(0, 1, knots)
        c = np.column_stack([np.interp(new, old, initial.corners[:, j]) for j in range(2)])
        objective(c.ravel()[free])
    starts = [(0.0, 0.0), (0.6/max(math.sin(beta), .25), .5), (1.5, .4)] if mode == "forward" else [(0.0, 0.0), (.5, 0.0), (1.0, .1)]
    for ax, ay in starts:
        objective(seed_path(beta, mode, knots, ax, ay).corners.ravel()[free])
    # First improve a small ansatz, then release all the non-gauge coordinates.
    def ansatz_objective(a):
        return objective(seed_path(beta, mode, knots, *a).corners.ravel()[free])
    ansatz = minimize(ansatz_objective, starts[1], method="Powell",
                      bounds=[(-xlimit, xlimit), (-1.5, 1.5)],
                      options={"maxiter": min(maxiter, 40), "ftol": 1e-8, "xtol": 1e-5})
    rng = np.random.default_rng(seed)
    runs = []
    for restart in range(restarts):
        x = best_motion.corners.ravel()[free].copy()
        if restart:
            x += rng.normal(0, .03, len(x))
            x = np.clip(x, [b[0] for b in bounds], [b[1] for b in bounds])
        result = minimize(objective, x, method="L-BFGS-B", bounds=bounds,
                          options={"maxiter": maxiter, "ftol": 1e-10,
                                   "gtol": 1e-6, "eps": 1e-5, "maxls": 30})
        runs.append({"success": bool(result.success), "status": int(result.status),
                     "message": str(result.message), "iterations": int(result.nit),
                     "evaluations": int(result.nfev), "returned_area": float(-result.fun)})
    return best_motion, {"objective": "largest connected sampled component area",
                         "best_sampled_area": best_area, "evaluations": evaluations,
                         "knots": knots, "subdivisions": subdivisions, "seed": seed,
                         "restarts": restarts, "maxiter": maxiter,
                         "x_bounds": [-xlimit, xlimit], "y_bounds": [-2.0, 3.0],
                         "ansatz_success": bool(ansatz.success), "runs": runs}


def environment():
    return {"python": platform.python_version(), "numpy": np.__version__,
            "scipy": scipy.__version__, "shapely": shapely.__version__}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--angles", type=float, nargs="+", default=[60, 90, 120, 150], help="bend angles in degrees, strictly between 0 and 180")
    parser.add_argument("--modes", nargs="+", choices=["forward", "reverse"], default=["forward", "reverse"])
    parser.add_argument("--knots", type=int, default=9)
    parser.add_argument("--subdivisions", type=int, default=4)
    parser.add_argument("--restarts", type=int, default=2)
    parser.add_argument("--maxiter", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--refinements", type=int, nargs="+", default=[8, 32, 128])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for degrees in args.angles:
        beta = math.radians(degrees)
        for mode in args.modes:
            motion, optimization = optimize(beta, mode, args.knots, args.subdivisions,
                                            args.restarts, args.maxiter, args.seed)
            refinements = [enclose(motion, n, audit=True)[0] for n in args.refinements]
            row = {"bend_degrees": degrees, "ray_angle_degrees": 180-degrees,
                   "mode": mode, "corners": motion.corners.tolist(),
                   "translation_only_exact_area": translation_area(beta),
                   "stationary_corner_exact_area": stationary_area(beta),
                   "optimization": optimization, "refinements": refinements}
            rows.append(row)
            print(degrees, mode, optimization["best_sampled_area"], refinements[-1], flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({"environment": environment(),
                "status": "exploratory floats; no global optimality or machine-certified bounds", "results": rows}, indent=2)+"\n")


if __name__ == "__main__":
    main()
