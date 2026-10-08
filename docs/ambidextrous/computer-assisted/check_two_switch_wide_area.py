"""Exact rational box-area certificate: complete turns with W >= 1411/500.

Mathematical reduction: ../two-switch-global-wide-area-certificate.md
Uses all 18 rational hallway frames and two *actual* unknown switching
angles. Fraction arithmetic constructs parameter enclosures and the final
comparisons; fixed-scale int64 operations round intermediate spatial
affine lines in the safe direction. No solver/optimizer is trusted.
"""
from fractions import Fraction as F
import numpy as np
import json, time

W0 = F(1411, 500)
WEND = F(283, 100)
R0, REND = F(1, 4), F(3, 5)
T, N = 10**10, 512
QNUM = np.arange(1, 2*N, 2, dtype=np.int64)
QDEN = 2*N
QMID = QNUM < QDEN//2
TRIPLES = ((3,4,5), (5,12,13), (8,15,17), (20,21,29),
           (28,45,53), (33,56,65), (48,55,73), (65,72,97),
           (60,91,109))
ANGLES = []
for a, b, d in TRIPLES:
    assert a*a+b*b == d*d
    for c, s in ((F(a,d), F(b,d)), (F(b,d), F(a,d))):
        assert c*c+s*s == 1
        assert max(c/s, s/c) <= F(12,5)
        ANGLES.append((c,s))
assert len(ANGLES) == 18

def flo(x):
    return x.numerator // x.denominator

def cei(x):
    return -((-x.numerator) // x.denominator)

def normal(r):
    return (1-r*r)/(1+r*r), 2*r/(1+r*r)

def FR(r, w):
    c, s = normal(r)
    return (1-w*c/2)/s

def FL(r, w):
    c, s = normal(r)
    return (1-w*s/2)/c

def line(alpha, beta, upper):
    # Rounding alpha and beta outwards is safe because 0 < q < 1.
    a = cei(T*alpha) if upper else flo(T*alpha)
    b = cei(T*beta) if upper else flo(T*beta)
    assert abs(a) < 2**40 and abs(b) < 2**40
    product = b*QNUM
    return a + (-((-product)//QDEN) if upper else product//QDEN)

def bound(wlo, whi, tl, th, pl, ph):
    # Disjoint impossible-height boxes can be rejected exactly.
    if FR(th,wlo)+FR(ph,wlo) < 0 or FL(tl,wlo)+FL(pl,wlo) < 0:
        return None
    amin, amax = -FL(pl,wlo), FL(tl,wlo)
    bmin, bmax = -FR(ph,wlo), FR(th,wlo)
    if amin > amax or bmin > bmax:
        return None

    def inner_lower(aa, bb):
        result = np.full(N, -2**55, dtype=np.int64)
        for c, s in ANGLES:
            # Every affine coefficient is a Fraction, rounded downward.
            # Split the midpoint-anchor W term at q = 1/2.
            u = [
                line((wlo*c + bb*s - 1)/s, -wlo*c/s, False),
                line((aa*s - 1)/s, -whi*c/s, False),
                np.where(QMID,
                    line((wlo*c/2-1)/s, -wlo*c/s, False),
                    line((whi*c/2-1)/s, -whi*c/s, False))
            ]
            v = [
                line((aa*c-1)/c, wlo*s/c, False),
                line((-whi*s+bb*c-1)/c, whi*s/c, False),
                np.where(QMID,
                    line((-whi*s/2-1)/c, whi*s/c, False),
                    line((-wlo*s/2-1)/c, wlo*s/c, False))
            ]
            result = np.maximum(
                result, np.minimum(np.maximum.reduce(u), np.maximum.reduce(v)))
        return result

    lower = inner_lower(amin,bmin)
    upper = -inner_lower(-amax,-bmax)

    def outer_upper(rlo, rhi):
        c0,s0 = normal(rlo)
        c1,s1 = normal(rhi)
        aa = np.where(QMID,
            line(1/s0+whi*c0/(2*s0),-whi*c0/s0,True),
            line(1/s0+wlo*c1/(2*s1),-wlo*c1/s1,True))
        bb = np.where(QMID,
            line(1/c1-wlo*s0/(2*c0),wlo*s0/c0,True),
            line(1/c1-whi*s1/(2*c1),whi*s1/c1,True))
        return np.minimum(aa,bb)

    lower = np.maximum(lower,-outer_upper(pl,ph))
    upper = np.minimum(upper,outer_upper(tl,th))
    h = np.minimum(T, np.maximum(0,upper-lower))
    assert np.max(abs(h)) <= T
    total = int(np.sum(h, dtype=np.int64))
    # d(q) is 14-Lipschitz; midpoint upper error is 14/(4N).
    return whi*(F(total,N*T)+F(7,2*N))

def replay():
    assert F(1414213562,10**9)**2 < 2 < F(1414213563,10**9)**2
    assert F(23,17) < F(7,5)
    assert 2*F(1414213563,10**9)-W0 < F(1,100)
    target = F(41,25)
    stack = [(W0,WEND,R0,REND,R0,REND,0)]
    visited = accepted = pruned = maxdepth = 0
    largest = F(0)
    start = time.monotonic()
    while stack:
        wlo,whi,tl,th,pl,ph,depth = stack.pop()
        value = bound(wlo,whi,tl,th,pl,ph)
        visited += 1
        if value is None:
            pruned += 1
            continue
        if value < target:
            accepted += 1
            largest = max(largest,value)
            maxdepth = max(maxdepth,depth)
            continue
        assert depth < 35, "undischarged box"
        spans = ((whi-wlo)/F(1,20),th-tl,ph-pl)
        dimension = max(range(3),key=lambda j:spans[j])
        if dimension == 0:
            mid = (wlo+whi)/2
            stack.extend(((wlo,mid,tl,th,pl,ph,depth+1),
                          (mid,whi,tl,th,pl,ph,depth+1)))
        elif dimension == 1:
            mid = (tl+th)/2
            stack.extend(((wlo,whi,tl,mid,pl,ph,depth+1),
                          (wlo,whi,mid,th,pl,ph,depth+1)))
        else:
            mid = (pl+ph)/2
            stack.extend(((wlo,whi,tl,th,pl,mid,depth+1),
                          (wlo,whi,tl,th,mid,ph,depth+1)))
    expected = F(4198376550651309,2560000000000000)
    assert largest == expected
    assert (visited,accepted,pruned,maxdepth) == (5393,1287,1410,19)
    assert largest < target
    print(json.dumps({
        "status":"exact_rational_certificate_passed",
        "domain":"[1411/500,2sqrt2]",
        "checked_root":"[1411/500,283/100]",
        "boxes_checked":visited,
        "accepted_area_leaves":accepted,
        "impossible_leaves":pruned,
        "max_depth":maxdepth,
        "largest_area_upper":str(largest),
        "margin_to_41_25":str(target-largest),
        "cells_per_leaf":N,
        "angular_frames_per_turn":len(ANGLES),
        "integer_scale":T,
        "run_seconds":round(time.monotonic()-start,3),
        "global_optimality_proved":False,
        "lean_ci_used":False
    },indent=2))

if __name__ == "__main__":
    replay()
