"""Radius of curvature h+h'' of compressed candidate hulls on the four open
quarters (CW4 hypothesis: h+h''<=1 there).  Floating point."""
import numpy as np
from numpy import pi
import sys
import cand
def h0(th):
    th = np.mod(th, 2 * pi)
    out = np.empty_like(th)
    up = th <= pi
    out[up] = cand.h_star_upper(th[up])
    tt = 2 * pi - th[~up]
    out[~up] = cand.h_star_upper(tt) - np.sin(tt)
    return out
for lam in (1.0, 0.95, 0.9, 0.85):
    # support of diag(lam,1)K at theta: |(lam cos, sin)| h0(arg(lam cos, sin))
    def h(th):
        a, b = lam * np.cos(th), np.sin(th)
        return np.hypot(a, b) * h0(np.arctan2(b, a))
    worst = 0
    for q0 in (0, pi / 2, pi, 3 * pi / 2):
        th = np.linspace(q0 + 1e-3, q0 + pi / 2 - 1e-3, 20001)
        d = th[1] - th[0]
        hh = h(th)
        rad = hh[1:-1] + (hh[2:] - 2 * hh[1:-1] + hh[:-2]) / d**2
        worst = max(worst, rad.max())
    print("lambda=%.2f  max radius of curvature on open quarters = %.4f" % (lam, worst))
