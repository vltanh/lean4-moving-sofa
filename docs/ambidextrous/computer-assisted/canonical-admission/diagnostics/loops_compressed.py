import sys
import numpy as np
from shapely import affinity
import wings as W
import precise as PR
import loops as LP
lam = float(sys.argv[1])
for (nx, nt, nth, ncore) in [(2000, 4000, 1441, 3001), (4000, 8000, 2881, 6001), (8000, 12000, 4001, 8001)]:
    K0 = affinity.scale(W.candidate_hull(4000), xfact=lam, yfact=1.0, origin=(0, 0))
    x = np.linspace(K0.bounds[0], K0.bounds[2], nx + 2)[1:-1]
    K = PR.saturate(K0, x, nt=nt)
    o = PR.full_analysis(K, nx=nx, nt=nt, nth=nth, verbose=False)
    G, _ = W.gamma_polygon(W.verts(o["Rpoly"]), W.verts(o["Dpoly"]), nt=ncore)
    fw = LP.faces_with_winding(G)
    neg = sum(a for w, a, f in fw if w < 0)
    lo, hi = PR.T_fibers(K, np.linspace(K.bounds[0], K.bounds[2], 2002)[1:-1], 4000)
    print("lambda=%.3f nx=%d: |T|=%.6f What=%.6f |T|-What=%+.2e  neg-loop area %.2e (n=%d)  p(beta)=%+.4f  minfiber=%.3f  R y[%.4f,%.4f]"
          % (lam, nx, o["T"], o["What"], o["T"] - o["What"], neg, sum(1 for w, a, f in fw if w < 0),
             o["p_beta"], np.min(hi - lo), o["Rb"][1], o["Rb"][3]), flush=True)
