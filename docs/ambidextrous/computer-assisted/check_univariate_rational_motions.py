#!/usr/bin/env python3
"""Exact continuous-time collision decision for rational rigid-motion arcs.

No time-grid approximation or positive clearance is required. Polynomial
conditions have degree at most five in the rational half-angle parameter.
Uses SymPy's exact real-root isolation, not a numerical root solver.
Not a global area/optimality certificate.
"""
from fractions import Fraction as F
from sympy import Poly, Rational, symbols

t = symbols("t", real=True)


def rat(x):
    return Rational(x.numerator, x.denominator) if isinstance(x, F) else Rational(x)


def sign_samples(polynomials):
    """One rational sample between each adjacent real root in (0,1).

    Strict polynomial inequalities at a root or endpoint can hold only if
    they hold in a neighboring open interval. The sign on such an interval
    is constant. Rational root isolation supplies exact representatives.
    """
    nonconstant = []
    for p in polynomials:
        p = Poly(p, t, domain="QQ")
        if not p.is_zero and p.degree() > 0:
            nonconstant.append(p)
    if not nonconstant:
        return [Rational(1, 2)]
    prod = Poly(1, t, domain="QQ")
    for p in nonconstant:
        prod *= p
    sq = prod.sqf_part()
    eps = Rational(1, 2**12)
    while True:
        intervals = sq.intervals(eps=eps)
        inside = []
        ambiguous = False
        for (a, b), multiplicity in intervals:
            if a < 0 < b or a < 1 < b:
                ambiguous = True
                break
            if b <= 0 or a >= 1:
                continue
            if a == b and a in (0, 1):
                continue
            if not 0 < a <= b < 1:
                ambiguous = True
                break
            inside.append((a, b))
        if not ambiguous and all(inside[i][1] < inside[i+1][0]
                                 for i in range(len(inside)-1)):
            if not inside:
                return [Rational(1, 2)]
            sample = [inside[0][0] / 2]
            sample.extend((inside[i][1] + inside[i+1][0]) / 2
                          for i in range(len(inside)-1))
            sample.append((inside[-1][1] + 1) / 2)
            assert all(0 < u < 1 for u in sample)
            return sample
        eps /= 16


def any_positive(poly):
    poly = Poly(poly, t, domain="QQ")
    return any(poly.eval(s) > 0 for s in sign_samples((poly,)))


def simultaneous_positive(polys):
    polys = [Poly(p, t, domain="QQ") for p in polys]
    if any(p.is_zero for p in polys):
        return False
    return any(all(p.eval(s) > 0 for p in polys)
               for s in sign_samples(polys))


def rational_pose(start, end):
    """Return positive D and polynomial numerators C,S,Tx,Ty."""
    c0, s0, x0, y0 = map(rat, start)
    c1, s1, x1, y1 = map(rat, end)
    assert c0*c0+s0*s0 == c1*c1+s1*s1 == 1
    cd, sd = c0*c1+s0*s1, c0*s1-s0*c1
    assert 1+cd > 0, "split a 180-degree pose jump"
    q = sd/(1+cd)
    D = Poly(1+q*q*t*t, t, domain="QQ")
    C = Poly(c0*(1-q*q*t*t)-s0*2*q*t, t, domain="QQ")
    S = Poly(s0*(1-q*q*t*t)+c0*2*q*t, t, domain="QQ")
    Tx = D*Poly(x0+(x1-x0)*t, t, domain="QQ")
    Ty = D*Poly(y0+(y1-y0)*t, t, domain="QQ")
    return D, C, S, Tx, Ty


def point_numerators(p, pose):
    D, C, S, Tx, Ty = pose
    x, y = map(rat, p)
    return C*x-S*y+Tx, S*x+C*y+Ty


def edge_inner_collision(A, B, C, E):
    """Exist t in [0,1], lambda in [0,1], with both values < 0.

    At a fixed t, both numerators are affine on the polygon edge.
    Minimize their maximum: an endpoint or their crossing suffices.
    Crossing conditions use univariate polynomials of degree <= 5.
    """
    if simultaneous_positive((-A, -C)) or simultaneous_positive((-B, -E)):
        return True
    U, V = B-A, E-C
    H, L = U-V, C-A
    T = A*H+U*L
    assert all(Poly(p, t).degree() <= 5 for p in (A,B,C,E,H,L,T))
    return (simultaneous_positive((H, L, H-L, -T)) or
            simultaneous_positive((-H, -L, L-H, T)))


def piece_feasible(cell, start, end, hand):
    """Exact all-time/all-point decision for one rational rectangle."""
    x0, x1, y0, y1 = map(rat, cell)
    assert x0 < x1 and y0 < y1 and hand in ("lower", "upper")
    pose = rational_pose(start, end)
    D = pose[0]
    corners = ((x0,y0), (x1,y0), (x1,y1), (x0,y1))
    values = [point_numerators(p,pose) for p in corners]
    for X,Y in values:
        if any_positive(X-D):
            return False, "outer_x"
        if hand == "lower" and any_positive(Y-D):
            return False, "outer_y_lower"
        if hand == "upper" and any_positive(-Y):
            return False, "outer_y_upper"
    for i in range(4):
        X0,Y0 = values[i]
        X1,Y1 = values[(i+1)%4]
        if hand == "lower":
            G0,G1 = Y0,Y1
        else:
            G0,G1 = D-Y0,D-Y1
        if edge_inner_collision(X0,X1,G0,G1):
            return False, "inner_edge_%d" % i
    return True, "certified"


def full_path_feasible(cells, paths):
    """Assumes continuity of shared rational knots and correct endpoint arms.

    The endpoint/connectedness/area checks of check_rational_motion_witness.py
    remain necessary when certifying a genuine ambidextrous counterexample.
    """
    assert set(paths) == {"lower","upper"}
    for hand, knots in paths.items():
        for a,b in zip(knots, knots[1:]):
            for cell in cells:
                ok, reason = piece_feasible(cell, a, b, hand)
                if not ok:
                    return False, (hand, reason)
    return True, None


def self_test():
    h = F(1,10)
    square = (-h,h,-h,h)
    a = (F(1),F(0),F(-2),F(1,2))
    b = (F(1),F(0),F(1,2),F(1,2))
    down = (F(0),F(-1),F(1,2),F(1,2))
    up = (F(0),F(1),F(1,2),F(1,2))
    paths = {
        "lower": [a,b,up,b,down,(F(0),F(-1),F(1,2),F(-2))],
        "upper": [a,b,up,(F(0),F(1),F(1,2),F(2))]
    }
    assert full_path_feasible([square], paths)[0]
    print("PASS: rational nonmonotone two-handed motion")
    contact = (F(0),F(1,5),F(4,5),F(1))
    stationary = (F(1),F(0),F(1,2),F(0))
    assert piece_feasible(contact, stationary, stationary, "lower")[0]
    assert piece_feasible(contact, stationary, stationary, "upper")[0]
    print("PASS: boundary contact with zero clearance")
    rect = (-F(3,10),F(3,10),-F(2,5),F(2,5))
    start = (F(1),F(0),F(1,2),F(1,2))
    end = (F(0),F(1),F(1,2),F(1,2))
    assert piece_feasible(rect,start,end,"lower")[0]
    assert piece_feasible(rect,start,end,"upper")[0]
    assert F(1,2)+F(3,10)*F(3,5)+F(2,5)*F(4,5) == 1
    print("PASS: interior-time exact wall tangency")
    big = (-F(3,10),F(3,10),-F(3,10),F(3,10))
    moved = (F(1),F(0),F(31,50),F(1,2))
    turned = (F(0),F(1),F(31,50),F(1,2))
    assert piece_feasible(big,moved,moved,"lower")[0]
    assert piece_feasible(big,turned,turned,"lower")[0]
    assert not piece_feasible(big,moved,turned,"lower")[0]
    print("PASS: collision between two safe endpoint poses")
    edge = (-F(1,2),F(1,2),-F(1,2),F(1,2))
    pose = (F(3,5),F(4,5),F(0),F(3,20))
    assert piece_feasible(edge,pose,pose,"lower") == (False,"inner_edge_3")
    print("PASS: edge-only forbidden collision")
    print("PASS: exact degree-five all-time test")


if __name__ == "__main__":
    self_test()
