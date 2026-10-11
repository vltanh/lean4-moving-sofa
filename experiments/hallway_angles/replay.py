"""Replay saved paths, optionally refine their knots, and recheck motion enclosures."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

from geometry import Motion
from enclosure import enclose
from swept import enclose_swept
from search import environment, optimize


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", type=Path)
    p.add_argument("--angles", type=float, nargs="+")
    p.add_argument("--modes", choices=["forward", "reverse"], nargs="+")
    p.add_argument("--refinements", type=int, nargs="+", default=[32, 64])
    p.add_argument("--method", choices=["lipschitz", "swept"], default="swept")
    p.add_argument("--refine-knots", type=int)
    p.add_argument("--optimization-subdivisions", type=int, default=4)
    p.add_argument("--restarts", type=int, default=1)
    p.add_argument("--maxiter", type=int, default=100)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    if any(n < 1 for n in a.refinements):
        p.error("refinements must be positive")
    if a.refine_knots is not None and (a.refine_knots < 3 or a.refine_knots % 2 == 0):
        p.error("refine-knots must be odd and at least 3")
    source = json.loads(a.input.read_text())
    rows = source.get("results", [source])
    rows = [r for r in rows if (a.angles is None or r["bend_degrees"] in a.angles)
            and (a.modes is None or r["mode"] in a.modes)]
    if not rows:
        p.error("no saved paths match the selection")
    result = {"environment": environment(), "input": a.input.name,
              "status": "exploratory floats; no global optimality or machine-certified bounds",
              "configuration": {"method": a.method, "refinements": a.refinements,
                  "refine_knots": a.refine_knots, "optimization_subdivisions": a.optimization_subdivisions,
                  "restarts": a.restarts, "maxiter": a.maxiter, "seed": a.seed}, "results": []}
    constructor = enclose_swept if a.method == "swept" else enclose
    for row in rows:
        m = Motion(math.radians(row["bend_degrees"]), row["mode"], row["corners"])
        optimization = None
        if a.refine_knots is not None:
            m, optimization = optimize(m.beta, m.mode, a.refine_knots,
                a.optimization_subdivisions, a.restarts, a.maxiter, a.seed, initial=m)
        checks = [constructor(m, n, audit=True)[0] for n in a.refinements]
        result["results"].append({"bend_degrees": row["bend_degrees"], "mode": row["mode"],
            "corners": m.corners.tolist(), "optimization": optimization, "refinements": checks})
        print(row["bend_degrees"], row["mode"], checks[-1], flush=True)
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(result, indent=2)+"\n")


if __name__ == "__main__":
    main()
