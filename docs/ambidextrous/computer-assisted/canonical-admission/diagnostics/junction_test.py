"""Controlled junction test: shave the candidate hull at normals L+beta,
L-beta, -L+beta, -L-beta by depth eps.  This raises the contact velocity
p(beta) = r'(beta) - d(beta+L) + 1 from 0 to about eps at all four junctions.
"""
import sys
import numpy as np
from numpy import pi, cos, sin
import wings as W
import precise as PR

L = pi / 2
beta = W.beta


def shaved(eps, which=(L + beta, L - beta, -L + beta, -L - beta), nv=3000):
    K = W.candidate_hull(nv)
    P = W.verts(K)
    for th in which:
        h = W.support(P, np.array([th]))[0]
        K = K.intersection(W.halfplane((-cos(th), -sin(th)), -(h - eps)))
    return K


if __name__ == "__main__":
    for eps in [float(e) for e in sys.argv[1:]] or [0.005, 0.01, 0.02, 0.04]:
        K = shaved(eps)
        x = np.linspace(K.bounds[0], K.bounds[2], 2002)[1:-1]
        Ks = PR.saturate(K, x)
        print("eps=%.3f  hull area %.5f -> saturated %.5f" % (eps, K.area, Ks.area))
        PR.full_analysis(Ks)
