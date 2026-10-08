"""Shave the candidate hull at normals +-pi/4, +-3pi/4 (facets in all open
quarters, so CW4's curvature hypothesis fails) and test the canonical
two-wing admission.  Floating-point diagnostic."""
import sys
import numpy as np
from numpy import pi
import wings as W
import precise as PR
import junction_test as J
import loops as LP
for eps in [float(a) for a in sys.argv[1:]]:
    K0 = J.shaved(eps, which=(pi / 4, 3 * pi / 4, -pi / 4, -3 * pi / 4))
    x = np.linspace(K0.bounds[0], K0.bounds[2], 4002)[1:-1]
    K = PR.saturate(K0, x, nt=8000)
    o = PR.full_analysis(K, nx=4000, nt=8000, nth=2881, verbose=False)
    G, _ = W.gamma_polygon(W.verts(o["Rpoly"]), W.verts(o["Dpoly"]), nt=6001)
    fw = LP.faces_with_winding(G)
    neg = sum(a for w, a, f in fw if w < 0)
    print("shave pi/4 eps=%.3f: |T|=%.6f What=%.6f |T|-What=%+.2e neg-loop %.1e  M-What=%.4f p(beta)=%+.4f  R y[%.4f,%.4f] D y[%.4f,%.4f]"
          % (eps, o["T"], o["What"], o["T"] - o["What"], neg, W.M - o["What"], o["p_beta"],
             o["Rb"][1], o["Rb"][3], o["Db"][1], o["Db"][3]), flush=True)
