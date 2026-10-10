"""Evaluate the hypotheses of Theorem CA / Corollary CA2 on test hulls and
compare with |T| - What.  Floating-point diagnostic only.

Reports: max p on [beta,L], min q on [0,b] (both motions), cut slacks,
outward-arm lengths tau, apex order, core regularity defect max|r-h|, max|d-h|,
GH.5 margins, and |T| - What.
"""
import sys
import numpy as np
from numpy import pi, sin, cos
from shapely import affinity
import wings as W
import precise as PR
import junction_test as J

L = pi / 2
beta, bb = W.beta, W.bb
y = np.tan(beta)


def contact(P, n=4001, e=1e-6):
    h = lambda t: W.support(P, t)
    hp = lambda t: (h(t + e) - h(t - e)) / (2 * e)
    t1 = np.linspace(beta + 1e-4, L - 1e-4, n)
    t2 = np.linspace(1e-4, bb - 1e-4, n)
    p = hp(t1) - h(t1 + L) + 1
    q = hp(t2 + L) + h(t2) - 1
    pr = -hp(-t1) - h(-t1 - L) + 1
    qr = -hp(-t2 - L) + h(-t2) - 1
    return p.max(), q.min(), pr.max(), qr.min()


def hyp(name, K):
    P = W.verts(K)
    o = PR.full_analysis(K, nx=3000, nt=6000, nth=2881, verbose=False)
    R, D = o["Rpoly"], o["Dpoly"]
    Rv, Dv = W.verts(R), W.verts(D)
    pm, qm, prm, qrm = contact(P)
    s = lambda V, th: W.support(V, np.array([th]))[0]
    slack = [1 - s(Rv, beta) - s(Rv, beta + pi), 1 - s(Rv, -beta) - s(Rv, pi - beta),
             1 - s(Dv, beta) - s(Dv, beta + pi), 1 - s(Dv, -beta) - s(Dv, pi - beta)]
    G, (t, zm, zp, IR, ID) = W.gamma_polygon(Rv, Dv, nt=3001)
    eR = np.array([sin(beta), -cos(beta)])
    tau = [(zm[0] - IR) @ eR, (zp[0] - IR) @ np.array([sin(beta), cos(beta)]),
           (zm[-1] - ID) @ np.array([-sin(beta), -cos(beta)]),
           (zp[-1] - ID) @ np.array([-sin(beta), cos(beta)])]
    tt = np.linspace(beta, bb, 801)
    reg = max(np.abs(W.support(Rv, tt) - W.support(P, tt)).max(),
              np.abs(W.support(Rv, -tt) - W.support(P, -tt)).max(),
              np.abs(W.support(Dv, tt + L) - W.support(P, tt + L)).max(),
              np.abs(W.support(Dv, -tt - L) - W.support(P, -tt - L)).max())
    # heights -> GH.5 margins (normalise: higher top at 1, on the right)
    (Rlo, Rhi), (Dlo, Dhi) = (R.bounds[1], R.bounds[3]), (D.bounds[1], D.bounds[3])
    if Dhi > Rhi:
        (Rlo, Rhi), (Dlo, Dhi) = (Dlo, Dhi), (Rlo, Rhi)
    shift = 1 - Rhi
    c = cos(beta)
    A, B0, C0 = (1 - Dhi - shift) / c, (Rlo + shift) / c, (Dlo + shift) / c
    aR = (1 - y) / 2 * A + B0 + (1 - y) / 2 * C0
    aD = A + (1 - y) / 2 * B0 + C0
    g = abs((1 - y) / 4 * (A + B0 - C0))
    lin = y * (3 - y) / 4
    gh = min(lin - aR - g, lin - aD - g)
    print("%-22s (M): max p=%+.4f min q=%+.4f | max p^r=%+.4f min q^r=%+.4f | slack max %.1e | "
          "tau min %.3f | apex gap %.3f | reg %.1e | GH.5 margin %+.3f | |T|-What=%+.1e M-What=%.4f"
          % (name, pm, qm, prm, qrm, max(np.abs(slack)), min(tau), IR[0] - ID[0], reg, gh,
             o["T"] - o["What"], W.M - o["What"]), flush=True)


if __name__ == "__main__":
    def sat(K0):
        x = np.linspace(K0.bounds[0], K0.bounds[2], 3002)[1:-1]
        return PR.saturate(K0, x)
    cand = W.candidate_hull(3000)
    hyp("candidate", cand)
    for lam in (1.05, 1.1, 0.95):
        hyp("x-scale %.2f" % lam, sat(affinity.scale(cand, xfact=lam, yfact=1.0, origin=(0, 0))))
    hyp("shaved junction .04", sat(J.shaved(0.04)))
    hyp("shaved pi/4 .05", sat(J.shaved(0.05, which=(pi / 4, 3 * pi / 4, -pi / 4, -3 * pi / 4))))
