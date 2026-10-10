"""Decompose the canonical core curve Gamma into faces with their winding
numbers (exact polygon arithmetic on the sampled curve), and run a
resolution study of |T| - What for a shaved, saturated candidate.

Floating-point diagnostic, not a proof certificate.
"""
import sys
import numpy as np
from shapely.geometry import LineString, Polygon
from shapely.ops import unary_union, polygonize
import wings as W
import precise as PR
import junction_test as J


def faces_with_winding(G):
    ring = LineString(np.vstack([G, G[:1]]))
    merged = unary_union(ring)
    out = []
    for f in polygonize(merged):
        pt = np.array(f.representative_point().coords)
        w = W.winding_cw(G, pt)[0]
        out.append((w, f.area, f))
    return out


def study(eps, levels):
    K0 = J.shaved(eps)
    for (nv, nx, nt, nth, ncore) in levels:
        x = np.linspace(K0.bounds[0], K0.bounds[2], nx + 2)[1:-1]
        K = PR.saturate(K0, x, nt=nt)
        o = PR.full_analysis(K, nx=nx, nt=nt, nth=nth, verbose=False)
        R, D = o["Rpoly"], o["Dpoly"]
        G, _ = W.gamma_polygon(W.verts(R), W.verts(D), nt=ncore)
        fw = faces_with_winding(G)
        neg = sum(a for w, a, f in fw if w < 0)
        pos2 = sum(a for w, a, f in fw if w >= 2)
        signed = sum(w * a for w, a, f in fw)
        print("eps=%.3f nx=%d nt=%d nth=%d | |T|=%.6f What=%.6f |T|-What=%+.2e | "
              "faces: neg-winding area %.2e (n=%d), w>=2 area %.2e, signed %.6f vs shoelace %.6f"
              % (eps, nx, nt, nth, o["T"], o["What"], o["T"] - o["What"], neg,
                 sum(1 for w, a, f in fw if w < 0), pos2, signed, o["core"]), flush=True)


if __name__ == "__main__":
    eps = float(sys.argv[1]) if len(sys.argv) > 1 else 0.08
    levels = [(3000, 2000, 4000, 1441, 3001),
              (3000, 4000, 8000, 2881, 6001)]
    study(eps, levels)
