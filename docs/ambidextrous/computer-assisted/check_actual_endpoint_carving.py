#!/usr/bin/env python3
"""Exact geometric regressions for actual-startup-carving-and-cubic-endpoint-saving.md.

Only Fraction arithmetic. These tests audit polygonal formulas and constants.
The arbitrary-hull/all-angle theorems are proved in the companion note, not
inferred from finite numerical samples. No CI or Lean is required.
"""
from fractions import Fraction as F
from itertools import combinations


def hull(points):
    pts = sorted(set(tuple(map(F, p)) for p in points))
    if len(pts) < 3:
        raise ValueError('a positive-area polygon is required')
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    lo, hi = [], []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi) >= 2 and cross(hi[-2], hi[-1], p) <= 0:
            hi.pop()
        hi.append(p)
    return lo[:-1] + hi[:-1]


def area(poly):
    if len(poly) < 3:
        return F(0)
    return abs(sum(p[0]*q[1]-p[1]*q[0]
                   for p,q in zip(poly, poly[1:]+poly[:1])))/2


def clip(poly, normal, offset):
    if not poly:
        return []
    a, b = normal
    out = []
    old = poly[-1]
    d0 = a*old[0]+b*old[1]-offset
    for new in poly:
        d1 = a*new[0]+b*new[1]-offset
        if (d0 <= 0) != (d1 <= 0):
            z = d0/(d0-d1)
            out.append((old[0]+z*(new[0]-old[0]),
                        old[1]+z*(new[1]-old[1])))
        if d1 <= 0:
            out.append(new)
        old, d0 = new, d1
    return out


def frame(q):
    q = F(q)
    return (1-q*q)/(1+q*q), 2*q/(1+q*q)


def depth_peak(poly, u, v):
    """Exact max over the polygon of the minimum of the two depths."""
    def dot(p, n): return p[0]*n[0]+p[1]*n[1]
    f, g = max(dot(p,u) for p in poly), max(dot(p,v) for p in poly)
    values = [(f-dot(p,u), g-dot(p,v)) for p in poly]
    best = max(min(z) for z in values)
    for a,b in zip(values, values[1:]+values[:1]):
        da, db = a[0]-a[1], b[0]-b[1]
        if da*db < 0:
            w = da/(da-db)
            best = max(best, a[0]+w*(b[0]-a[0]))
    return best


def single_cut(poly, q):
    c, s = frame(q)
    u, v = (c,s), (-s,c)
    f = max(x*c+y*s for x,y in poly)
    g = max(-x*s+y*c for x,y in poly)
    return area(clip(clip(poly, u, f-1), v, g-1))


def coefficient(poly):
    H = max(y for x,y in poly)-min(y for x,y in poly)
    if H < 1:
        return F(0)
    assert H == 1 and min(y for x,y in poly) == 0
    r = max(x for x,y in poly)
    a = min(x for x,y in poly if y == 1)
    c = min(x for x,y in poly if y == 0)
    d = max(x for x,y in poly if y == 0)
    lo, hi = max(a,c), min(d,r-1)
    return ((hi-a)**2-(lo-a)**2)/2 if hi > lo else F(0)


def transformed(poly, hand, end):
    return hull([(-x if end else x, 1-y if hand else y)
                 for x,y in poly])


def verify_dual(poly, u, v):
    """Independently minimize the piecewise affine support dual in lambda."""
    def dot(p,n): return p[0]*n[0]+p[1]*n[1]
    f, g = max(dot(p,u) for p in poly), max(dot(p,v) for p in poly)
    lines = [(f-dot(p,u)-g+dot(p,v), g-dot(p,v)) for p in poly]
    candidates = {F(0), F(1)}
    for i,(a,b) in enumerate(lines):
        for A,B in lines[i+1:]:
            if a != A:
                z = (B-b)/(a-A)
                if 0 <= z <= 1:
                    candidates.add(z)
    dual = min(max(a*z+b for a,b in lines) for z in candidates)
    assert dual == depth_peak(poly,u,v)
    return dual


def quarter_cut(poly, q):
    c,s = frame(q)
    f = max(x*c+y*s for x,y in poly)
    g = max(-x*s+y*c for x,y in poly)
    return [((c,s),f-1), ((-s,c),g-1)]


def cut_by_constraints(poly, constraints):
    for n,b in constraints:
        poly = clip(poly,n,b)
    return poly


def finite_missing_union(poly, early, terminal):
    """Exact inclusion-exclusion: union of early cuts minus terminal cut."""
    cuts = [quarter_cut(poly,q) for q in early]
    end = quarter_cut(poly,terminal)
    result = F(0)
    for size in range(1,len(cuts)+1):
        for choice in combinations(range(len(cuts)),size):
            constraints = [c for i in choice for c in cuts[i]]
            intersection = cut_by_constraints(poly,constraints)
            value = area(intersection)-area(cut_by_constraints(intersection,end))
            result += value if size%2 else -value
    return result


def cross_area(V,q):
    """Exact polygonal cross-branch term in the general theorem."""
    Z=2*q/(1-q*q)
    k=2*q*q/(1-q*q)
    return Z/2*(V*V-max(V-k,0)**2/(1+Z*Z))


def rational_endpoint_upper(W,q):
    # q-atan(q) <= q^3/3; no floating trigonometry.
    return 2*q**3/3+cross_area(max(W-1,0),q)


def endpoint_regressions(polygons):
    count = 0
    for poly in polygons:
        W=max(x for x,y in poly)-min(x for x,y in poly)
        for q in (F(1,100),F(1,10),F(1,2)):
            missing=finite_missing_union(poly,[q/4,q/2,3*q/4],q)
            assert 0 <= missing <= rational_endpoint_upper(W,q)
            count += 1
    print('PASS:',count,'exact three-early-angle union checks against the all-angle upper bound')
    cross_checks=0
    for V in (F(0),F(1,10000),F(1,10),F(1),F(3)):
        for q in (F(1,100),F(1,10),F(1,2),F(3,4)):
            if V==0:
                assert cross_area(V,q)==0
            else:
                Z=2*q/(1-q*q);k=2*q*q/(1-q*q)
                triangle=[(F(0),F(0)),(V,F(0)),(F(0),V*Z)]
                assert area(clip(triangle,(F(1),-Z),k))==cross_area(V,q)
            cross_checks+=1
    print('PASS:',cross_checks,'exact cross-branch polygon area identities')
    square=hull([(0,0),(1,0),(1,1),(0,1)])
    for q in (F(1,100),F(1,10),F(1,2)):
        q0=q/4
        early=single_cut(square,q0)
        assert early==q0**3*(1-q0)**3/((1+q0)*(1+q0*q0)**2)
        assert early > q**3/128
        assert 2*q0/(1+q0) < q
    print('PASS: positive cubic-order omitted-interval witness on the square hull')


def main():
    aligned = hull([(-F(3,2),0),(F(3,2),0),(F(3,2),1),(-F(3,2),1)])
    strict = hull([(-F(6,5),1),(-F(3,5),1),(F(3,5),0),(F(6,5),0)])
    boundary = hull([(-F(3,2),1),(-F(1,2),1),(F(1,2),0),(F(3,2),0)])
    mixed = hull([(-1,0),(1,0),(-F(1,2),1),(F(1,2),1)])
    square = hull([(0,0),(1,0),(1,1),(0,1)])
    subunit = hull([(-F(3,2),0),(F(3,2),0),(F(3,2),F(9,10)),(-F(3,2),F(9,10))])
    assert coefficient(aligned) == 2
    assert coefficient(mixed) == F(1,8)
    assert coefficient(transformed(mixed,True,False)) == F(3,8)
    assert coefficient(strict) == coefficient(boundary) == coefficient(square) == 0

    checked = 0
    # t=2 atan(q)=2q+O(q^3), so area/(2q) has the same limit.
    q = F(1,10**6)
    for poly in (aligned, strict, boundary, mixed, square):
        for hand in (False,True):
            for end in (False,True):
                p = transformed(poly,hand,end)
                estimate = single_cut(p,q)/(2*q)
                expected = coefficient(p)
                assert abs(estimate-expected) < F(1,10000), (estimate,expected)
                checked += 1
    print('PASS:', checked, 'exact single-frame small-angle/coefficient regression tests')

    for hand in (False,True):
        for end in (False,True):
            p = transformed(strict,hand,end)
            c,s = frame(F(1,100))
            assert verify_dual(p,(c,s),(-s,c)) < 1
            assert single_cut(p,F(1,100)) == 0
    print('PASS: strict opposite-face exact endpoint loss is zero in all four test poses')

    c,s = frame(F(1,100))
    f=max(x*c+y*s for x,y in strict)
    g=max(-x*s+y*c for x,y in strict)
    assert (f-1)*s+(g-1)*c > 0
    assert single_cut(strict,F(1,100)) == 0
    print('PASS: positive ambient corner height with zero actual hull carving')

    for k in (1,2,3,10,100):
        q=F(1,100*k)
        c,s=frame(q)
        eta=(1-s)*(1-c)
        assert single_cut(square,q) == eta*eta/(2*s*c) > 0
    print('PASS: square exact positive triangle formula; zero linear loss is not a delay theorem')

    assert single_cut(subunit,F(1,100)) == 0
    for poly in (aligned, strict, boundary, mixed, square, subunit):
        for q in (F(1,20),F(1,3),F(3,4)):
            c,s=frame(q)
            verify_dual(poly,(c,s),(-s,c))
    print('PASS: 18 exact primal/dual deepest-corner cross-checks')
    endpoint_regressions([aligned,strict,boundary,mixed,square,subunit])
    print('These regressions are not a sharp area-bound or full-motion certificate.')


if __name__ == '__main__':
    main()
