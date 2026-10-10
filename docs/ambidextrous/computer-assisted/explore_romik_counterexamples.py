#!/usr/bin/env python3
"""Exploratory search for ambidextrous sofas larger than Romik's.

Not a proof or certificate. Finite angle samples OMIT some real hallway
constraints, and trapezoidal spatial quadrature is not an interval bound.
Any purported area > M MUST be rechecked with full continuous angles,
rigorous area enclosure and a connectedness proof.

Uses actual Romik analytic support formula and the repository's Gerver
rotation path (scripts/figures/gerver.py). No Lean is touched.

Usage:
  python docs/ambidextrous/computer-assisted/explore_romik_counterexamples.py
  python docs/ambidextrous/computer-assisted/explore_romik_counterexamples.py --mode gerver
  python docs/ambidextrous/computer-assisted/explore_romik_counterexamples.py --mode shear
"""
import argparse
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
from scipy.spatial import ConvexHull

ROOT = Path(__file__).resolve().parents[3]

Y = brentq(lambda y: 4*y**3 + 3*y - 1, 0, 0.5)
BETA = np.arctan(Y)
HALF_WIDTH = 1/(3*np.sin(BETA))
TOP_HALF_WIDTH = HALF_WIDTH/2
R0 = np.cos(BETA)/np.sin(1.5*BETA + np.pi/8)
ROMIK_AREA = 1 + 4*Y**2 + BETA


def romik_capsample(n=200):
    """Polygon strictly INSIDE the reference one-turn convex cap."""
    t = np.unique(np.r_[
        np.linspace(0, BETA, max(3, n//4)),
        np.linspace(BETA, np.pi/2-BETA, n),
        np.linspace(np.pi/2-BETA, np.pi/2, max(3, n//4))
    ])
    c, s = np.cos(t), np.sin(t)
    f = np.where(t <= BETA, HALF_WIDTH*c + s/2,
        np.where(t >= np.pi/2-BETA,
            TOP_HALF_WIDTH*c + s/2 + .5,
            R0*np.cos(t/2+np.pi/8)+s/2))
    g = np.where(t <= BETA, TOP_HALF_WIDTH*s + c/2 + .5,
        np.where(t >= np.pi/2-BETA,
            HALF_WIDTH*s + c/2,
            R0*np.sin(t/2+np.pi/8)+c/2))
    fp = np.where(t <= BETA, -HALF_WIDTH*s + c/2,
        np.where(t >= np.pi/2-BETA,
            -TOP_HALF_WIDTH*s + c/2,
            -R0/2*np.sin(t/2+np.pi/8)+c/2))
    gp = np.where(t <= BETA, TOP_HALF_WIDTH*c - s/2,
        np.where(t >= np.pi/2-BETA,
            HALF_WIDTH*c - s/2,
            R0/2*np.cos(t/2+np.pi/8)-s/2))
    right = np.c_[f*c-fp*s, f*s+fp*c]
    left = np.c_[-g*s-gp*c, g*c-gp*s]
    return np.unique(
        np.round(np.r_[right, left,
                       [[-HALF_WIDTH, 0], [HALF_WIDTH, 0]]], 14),
        axis=0
    )


def outer_roof(points, xs):
    """Concave upper polygonal roof obtained from true convex-hull facets."""
    eq = ConvexHull(points).equations
    eq = eq[eq[:, 1] > 1e-9]
    roof = np.min(
        -(eq[:, 0, None]*xs[None, :] + eq[:, 2, None])
        / eq[:, 1, None], axis=0
    )
    return np.clip(roof, 0, 1)


def one_turn_cap(points, xs, ts):
    """Approximate full positive niche from sampled conventional turns."""
    c, s = np.cos(ts), np.sin(ts)
    f = np.max(points[:, 0, None]*c+points[:, 1, None]*s, axis=0)
    g = np.max(-points[:, 0, None]*s+points[:, 1, None]*c, axis=0)
    roofs = np.minimum(
        (f[None, :]-1-xs[:, None]*c)/s,
        (g[None, :]-1+xs[:, None]*s)/c
    )
    return outer_roof(points, xs), np.maximum(np.max(roofs, axis=1), 0)


def pair_area(p, q, nx=1501, nt=1001, details=False):
    """NUMERICAL ONLY: integrates positive vertical intersection lengths.

    E_true is contained in the finite-angle envelope; reported integration
    can overestimate its area. A disconnected union is not a valid sofa.
    """
    left = max(p[:, 0].min(), q[:, 0].min())
    right = min(p[:, 0].max(), q[:, 0].max())
    if right <= left:
        return None
    xs = np.linspace(left, right, nx)
    ts = np.linspace(1e-7, np.pi/2-1e-7, nt)
    A, n = one_turn_cap(p, xs, ts)
    B, v = one_turn_cap(q, xs, ts)
    gap = np.minimum(A, 1-v)-np.maximum(n, 1-B)
    area = float(np.trapezoid(np.maximum(gap, 0), xs))
    if details:
        return dict(area=area, above_M=area-ROMIK_AREA,
                    min_fiber_gap=float(gap.min()),
                    max_niche=float(max(n.max(),v.max())))
    return area


def gaussian_bump(p, center=.6, sigma=.22, amplitude=.015):
    """Nonlinear asymmetric perturbation; convex hull taken in pair_area."""
    x, y = p[:, 0], p[:, 1]
    height = y+y*(1-y)*amplitude*np.exp(
        -0.5*((x-center)/sigma)**2
    )
    return np.c_[x, np.clip(height, 0, 1)]


def core_from_cap(p, n=140):
    """Extract Romik's true height-1/2, point-top curved Minkowski core."""
    verts = p[ConvexHull(p).vertices]
    next_verts = np.roll(verts, -1, axis=0)
    ys = np.linspace(.5, 1, n)
    left = np.full(n, np.inf)
    right = np.full(n, -np.inf)
    for a, b in zip(verts, next_verts):
        if abs(b[1]-a[1]) < 1e-10:
            continue
        u = (ys-a[1])/(b[1]-a[1])
        mask = (u >= -1e-8) & (u <= 1+1e-8)
        x = a[0]+u*(b[0]-a[0])
        left[mask] = np.minimum(left[mask], x[mask])
        right[mask] = np.maximum(right[mask], x[mask])
    assert np.isfinite(left).all() and np.isfinite(right).all()
    return np.r_[np.c_[left, ys-.5],
                 np.c_[right-HALF_WIDTH, ys-.5]]


def filled_sheared_cap(core, d):
    """Shear curved core, re-add the ACTUAL reference half-height rectangle."""
    v = core.copy()
    v[:, 0] += 2*d*v[:, 1]
    p = np.vstack(
        [v+offset for offset in
         ([0,0], [HALF_WIDTH,0], [0,.5], [HALF_WIDTH,.5])]
    )
    return p[ConvexHull(p).vertices]


def smoke():
    p = romik_capsample(160)
    q = gaussian_bump(p)
    print('Exact Romik area', ROMIK_AREA)
    for nx, nt in [(1001, 901), (4501, 2501), (6001, 5500)]:
        r = pair_area(p, p, nx, nt, True)
        s = pair_area(q, q, nx, nt, True)
        print('grid',nx,nt,'Romik approximate',r,
              'bumped approximate',s,
              'bump_minus_reference',s['area']-r['area'])


def sweep_shears():
    p = romik_capsample(340)
    v = core_from_cap(p)
    samples = np.linspace(-.14, .14, 29)
    caps = [filled_sheared_cap(v,d) for d in samples]
    reference = pair_area(filled_sheared_cap(v, 0),
                          filled_sheared_cap(v, 0),
                          1001, 701)
    best = (-1e9, None, None)
    for x, P in zip(samples, caps):
        for y, Q in zip(samples, caps):
            area = pair_area(P,Q,1001,701)
            if area > best[0]:
                best = (area, float(x), float(y))
    print('Grid best area, shear parameters:',best,
          'Romik polygon sampled-area',reference,
          'exact Romik target',ROMIK_AREA)
    print('Exploratory, not certified.')


def gerver_check():
    sys.path.insert(0,str(ROOT/'scripts'/'figures'))
    import gerver
    low, high = gerver.path(np.pi/2)[0]-1, 1.0
    xs = np.linspace(low,high,12001)
    upper, lower, inside = gerver.bounds(xs, n=1500)
    rev_upper = 1-lower
    rev_lower = 1-upper
    gap = np.minimum(upper,rev_upper)-np.maximum(lower,rev_lower)
    height = np.where(inside,np.maximum(gap,0),0)
    raw_area = float(np.trapezoid(height,xs))
    good = height > 1e-8
    edges = np.diff(np.r_[False,good,False].astype(int))
    starts = np.where(edges==1)[0]
    ends = np.where(edges==-1)[0]
    components = [
        (float(xs[i]),float(xs[j-1]),
         float(np.trapezoid(height[i:j],xs[i:j])))
        for i,j in zip(starts,ends)
    ]
    print('Gerver two reflected one-turn copies:')
    print('TOTAL (can be disconnected):',raw_area)
    print('Components (only connected ones can be sofas):',components)
    print('Romik area:',ROMIK_AREA)
    print('Exploratory angular and spatial quadrature, not certified.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode',choices=['smoke','shear','gerver'],
                        default='smoke')
    args=parser.parse_args()
    {'smoke':smoke, 'shear':sweep_shears,
     'gerver':gerver_check}[args.mode]()
