#!/usr/bin/env python3
"""Exact rational witness for two-corner packing (CP1–CP12).

Checks an individually compatible, unit-height pentagonal hull whose
two selected opposite-handed canonical hallway placements cannot coexist
with one connected sofa of that *actual hull*. No time/area sampling, CI,
Lean, floating trigonometry, or optimization is involved.
"""
from fractions import Fraction as Q


P = [
    (Q(-13, 10), Q(4, 5)),
    (Q(-19, 20), Q(0)),
    (Q(-7, 10), Q(0)),
    (Q(13, 10), Q(3, 4)),
    (Q(13, 20), Q(1)),
]
LOWER = (Q(20, 29), Q(21, 29))
UPPER = (Q(4, 5), Q(3, 5))


def cross(a, b, c):
    return (b[0] - a[0])*(c[1] - a[1]) - (b[1] - a[1])*(c[0] - a[0])


def hull_area(vertices):
    return sum(
        a[0]*b[1]-b[0]*a[1]
        for a, b in zip(vertices, vertices[1:] + vertices[:1])
    ) / 2


def reflected(vertices):
    return [(x, 1-y) for x, y in vertices]


def corner(vertices, unit_normal):
    c, s = unit_normal
    assert c*c+s*s == 1 and c > 0 and s > 0
    f = max(x*c + y*s for x, y in vertices)
    g = max(-x*s + y*c for x, y in vertices)
    xi = (f-1)*c-(g-1)*s
    eta = (f-1)*s+(g-1)*c
    margins = [1-min(f-x*c-y*s, g+x*s-y*c) for x, y in vertices]
    return xi, eta, f, g, min(margins)


def upper_roof(vertices, x):
    vals = []
    for (xx, yy), (XX, YY) in zip(vertices, vertices[1:] + vertices[:1]):
        if min(xx, XX) <= x <= max(xx, XX):
            if xx == XX:
                vals.extend((yy, YY))
            else:
                vals.append(yy+(YY-yy)*(x-xx)/(XX-xx))
    assert vals
    return max(vals)


def roof_gap(vertices, unit_normal):
    c, s = unit_normal
    xi, eta, _, _, _ = corner(vertices, unit_normal)
    knots = sorted(set([x for x, y in vertices] + [xi]))
    def w(x):
        return eta-(xi-x)*s/c if x <= xi else eta-(x-xi)*c/s
    return max(w(x)-upper_roof(vertices, x) for x in knots)


def pair_violation(vertices, a, b):
    x, height_a, *_ = corner(vertices, a)
    z, height_b, *_ = corner(reflected(vertices), b)
    l = min(xx for xx, y in vertices)
    r = max(xx for xx, y in vertices)
    assert l <= x <= r and l <= z <= r
    if x <= z:
        distance = min(a[0]/a[1], b[1]/b[0])*(z-x)
    else:
        distance = min(a[1]/a[0], b[0]/b[1])*(x-z)
    return height_a + height_b - distance - 1, distance


def diagonal_raw_spans(vertices):
    X = [x+y for x, y in vertices]
    Y = [-x+y for x, y in vertices]
    return max(X)-min(X), max(Y)-min(Y)


def midpoint_vertex_depth_numerator(vertices):
    A = max(x+y for x,y in vertices)
    B = max(-x+y for x,y in vertices)
    return max(min(A-x-y, B+x-y) for x,y in vertices)


def main():
    assert all(cross(P[i-1], P[i], P[(i+1)%len(P)]) > 0
               for i in range(len(P)))
    assert max(y for x,y in P)-min(y for x,y in P)==1
    assert hull_area(P) == Q(1147, 800)
    l, r = corner(P, LOWER), corner(reflected(P), UPPER)
    assert l[:2] == (Q(-453, 8410), Q(2215, 3364))
    assert r[:2] == (Q(-7, 100), Q(41, 100))
    assert l[-1] == Q(2,145) > 0
    assert r[-1] == Q(33,100) > 0
    assert roof_gap(P, LOWER) == -Q(176699,655980)
    assert roof_gap(reflected(P), UPPER) == -Q(283,800)
    gap, separation = pair_violation(P, LOWER, UPPER)
    assert separation == Q(28497,1682000)
    assert gap == Q(103,2000) > 0
    diag = diagonal_raw_spans(P)
    assert diag == (Q(3),Q(53,20)) and min(diag)**2 < 8
    assert midpoint_vertex_depth_numerator(P) == Q(7,5)
    assert midpoint_vertex_depth_numerator(reflected(P)) == Q(9,10)
    # Their squares are < 2, so the two individual 45 degree
    # canonical poses retain each of the pentagon's extreme vertices.
    assert max(Q(7,5)**2,Q(9,10)**2) < 2

    print("PASS: strictly convex rational pentagon, height one, area =", hull_area(P))
    print("PASS: individually full-projection canonical snapshots, margin lower/upper =", l[-1],r[-1])
    print("PASS: single-snapshot roof clearances =",roof_gap(P,LOWER),roof_gap(reflected(P), UPPER))
    print("PASS: 45-degree diagonal-width screen, raw spans =",diag)
    print("PASS: corner mismatch penalty =",separation)
    print("CERTIFIED: forbidden lower/upper tents overlap by",gap,"at a common interior column")


if __name__=="__main__":
    main()
