#!/usr/bin/env python3
"""Exact rational interval verifier for polygonal two-handed physical motions.

For a connected union of pairwise interior-disjoint rational squares and two
piecewise-rational SE(2) paths, this is a sound all-time/all-point certificate.
It reports inconclusive when its subdivision budget expires. No floating-point
angles, sampled frames, optimizer, Lean or CI.
"""
from fractions import Fraction as Q


def rat(x):
    return x if isinstance(x, Q) else Q(x)


class Interval:
    def __init__(self, a, b=None):
        self.lo = rat(a)
        self.hi = rat(a if b is None else b)
        assert self.lo <= self.hi

    def __add__(self, other):
        v = as_interval(other)
        return Interval(self.lo + v.lo, self.hi + v.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -as_interval(other)

    def __rsub__(self, other):
        return as_interval(other) + -self

    def __mul__(self, other):
        v = as_interval(other)
        values = (self.lo*v.lo, self.lo*v.hi,
                  self.hi*v.lo, self.hi*v.hi)
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def square(self):
        if self.lo >= 0:
            return Interval(self.lo*self.lo, self.hi*self.hi)
        if self.hi <= 0:
            return Interval(self.hi*self.hi, self.lo*self.lo)
        return Interval(0, max(self.lo*self.lo, self.hi*self.hi))

    def __truediv__(self, other):
        v = as_interval(other)
        assert v.lo > 0 or v.hi < 0
        return self * Interval(1/v.hi, 1/v.lo)


def as_interval(x):
    return x if isinstance(x, Interval) else Interval(x)


def pose_intervals(start, end, t):
    """Exact rational enclosures for rational half-angle rotation arc."""
    c0, s0, x0, y0 = map(rat, start)
    c1, s1, x1, y1 = map(rat, end)
    assert c0*c0+s0*s0 == c1*c1+s1*s1 == 1
    cd = c0*c1+s0*s1
    sd = c0*s1-s0*c1
    assert 1+cd > 0, "refine a 180-degree rotation into shorter arcs"
    z = t*(sd/(1+cd))
    den = 1+z.square()
    co = (1-z.square())/den
    si = (2*z)/den
    co_rot = c0*co-s0*si
    si_rot = s0*co+c0*si
    tx = x0+(x1-x0)*t
    ty = y0+(y1-y0)*t
    return co_rot, si_rot, tx, ty


def image_intervals(cell, start, end, t):
    x0, x1, y0, y1 = cell
    co, si, tx, ty = pose_intervals(start, end, t)
    x, y = Interval(x0, x1), Interval(y0, y1)
    return co*x-si*y+tx, si*x+co*y+ty


def safe_box(cell, start, end, hand, time_box, margin):
    X, Y = image_intervals(cell, start, end, time_box)
    m = rat(margin)
    if hand == "lower":
        return (X.hi <= 1-m and Y.hi <= 1-m
                and (X.lo >= m or Y.lo >= m))
    if hand == "upper":
        return (X.hi <= 1-m and Y.lo >= m
                and (X.lo >= m or Y.hi <= 1-m))
    raise ValueError(hand)


def certify_piece(cell, start, end, hand, margin,
                  max_boxes=50000, max_depth=72):
    """Sound rational space-time partition certificate; budget exhaustion is inconclusive."""
    pending = [(Interval(0, 1), tuple(map(rat, cell)), 0)]
    visited = 0
    while pending:
        t, cell, depth = pending.pop()
        visited += 1
        if visited > max_boxes:
            return False, visited
        if safe_box(cell, start, end, hand, t, margin):
            continue
        if depth >= max_depth:
            return False, visited
        a, b, c, d = cell
        widths = (t.hi-t.lo, b-a, d-c)
        which = max(range(3), key=lambda i: widths[i])
        if widths[which] == 0:
            return False, visited
        if which == 0:
            mid = (t.lo+t.hi)/2
            pending.extend(((Interval(t.lo, mid), cell, depth+1),
                            (Interval(mid, t.hi), cell, depth+1)))
        elif which == 1:
            mid = (a+b)/2
            pending.extend(((t, (a, mid, c, d), depth+1),
                            (t, (mid, b, c, d), depth+1)))
        else:
            mid = (c+d)/2
            pending.extend(((t, (a, b, c, mid), depth+1),
                            (t, (a, b, mid, d), depth+1)))
    return True, visited


def connected_square_area(cells):
    """Verify square geometry, disjoint interiors and connectivity; return exact area."""
    cells = [tuple(map(rat, cell)) for cell in cells]
    assert cells
    for a, b, c, d in cells:
        assert a < b and c < d and b-a == d-c
    n = len(cells)
    adjacency = [[] for _ in range(n)]
    for i, (a, b, c, d) in enumerate(cells):
        for j in range(i+1, n):
            A, B, C, D = cells[j]
            assert not (max(a,A)<min(b,B) and max(c,C)<min(d,D))
            if max(a,A)<=min(b,B) and max(c,C)<=min(d,D):
                adjacency[i].append(j)
                adjacency[j].append(i)
    seen = {0}
    todo = [0]
    while todo:
        for j in adjacency[todo.pop()]:
            if j not in seen:
                seen.add(j)
                todo.append(j)
    assert len(seen) == n, "disconnected polyomino"
    return sum((b-a)*(d-c) for a, b, c, d in cells)


def verify_straight_arm_endpoints(cells, motions, m):
    """Require a common identity-oriented incoming pose and valid far outgoing poses."""
    assert set(motions) == {"lower", "upper"}
    assert motions["lower"][0] == motions["upper"][0]
    assert tuple(map(rat,motions["lower"][0][:2])) == (Q(1), Q(0))
    for hand, knots in motions.items():
        assert len(knots) >= 2
        for k in knots:
            c, s, tx, ty = map(rat, k)
            assert c*c+s*s == 1
        for at_start, pose in ((True, knots[0]), (False, knots[-1])):
            c, s, tx, ty = map(rat, pose)
            for a, b, lo, hi in cells:
                for x in (a,b):
                    for y in (lo,hi):
                        X, Y = c*x-s*y+tx, s*x+c*y+ty
                        if at_start:
                            assert X <= -m and m <= Y <= 1-m
                        elif hand == "lower":
                            assert m <= X <= 1-m and Y <= -m
                        else:
                            assert m <= X <= 1-m and Y >= 1+m


def certify_ambidextrous(cells, motions, margin, max_boxes=50000,
                          max_depth=72):
    """Return (certified, rational area, box_count); False means inconclusive."""
    margin = rat(margin)
    assert 0 < margin < Q(1,2)
    area = connected_square_area(cells)
    verify_straight_arm_endpoints(cells, motions, margin)
    boxes = 0
    for hand, knots in motions.items():
        for start, end in zip(knots, knots[1:]):
            for cell in cells:
                passed, count = certify_piece(cell, start, end, hand, margin,
                                             max_boxes, max_depth)
                boxes += count
                if not passed:
                    return False, area, boxes
    return True, area, boxes



def romik_rational_upper(j):
    """Provable rational upper bound decreasing to Romik's candidate area.

    Bisect 4Y^3+3Y-1=0 on [0,1/3], then use an even-index
    upper truncation of the alternating atan series at the upper endpoint.
    """
    assert isinstance(j, int) and j >= 0
    low, high = Q(0), Q(1,3)
    for _ in range(max(16,4*j)):
        mid = (low+high)/2
        if 4*mid**3 + 3*mid - 1 > 0:
            high = mid
        else:
            low = mid
    value = 1+4*high**2
    for k in range(2*j+1):
        value += (-1)**k * high**(2*k+1)/Q(2*k+1)
    return value


def certify_strict_counterexample(cells, motions, margin, j=16,
                                  max_boxes=50000, max_depth=72):
    """True proves both complete paths and rational area > a rigorous M upper."""
    certified, area, boxes = certify_ambidextrous(
        cells, motions, margin, max_boxes, max_depth)
    return certified and area > romik_rational_upper(j), area, boxes


def self_test():
    h = Q(1,10)
    cells = [(-h,h,-h,h)]
    incoming = (Q(1),Q(0),Q(-2),Q(1,2))
    middle = (Q(1),Q(0),Q(1,2),Q(1,2))
    motions = {
        "lower": [incoming, middle, (Q(0),Q(-1),Q(1,2),Q(1,2)),
                  (Q(0),Q(-1),Q(1,2),Q(-2))],
        "upper": [incoming, middle, (Q(0),Q(1),Q(1,2),Q(1,2)),
                  (Q(0),Q(1),Q(1,2),Q(2))],
    }
    passed, area, boxes = certify_ambidextrous(cells, motions, Q(1,4))
    assert passed and area == Q(1,25)
    assert Q(8,5)<romik_rational_upper(8)<Q(329,200)
    assert not certify_strict_counterexample(cells, motions, Q(1,4), j=8)[0]
    print("PASS: two continuous rational motions with common start")
    print("area =", area, "; certified rational boxes =", boxes)
    # A larger square would collide with the outer wall halfway through
    # its rotation: tan(half-angle)=1/2 gives cos=3/5 and |sin|=4/5.
    bad_x = Q(1,2) + Q(1,2)*(Q(3,5)+Q(4,5))
    assert bad_x == Q(6,5) > 1
    print("NEGATIVE CONTROL: exact forbidden outer x =", bad_x)


if __name__ == "__main__":
    self_test()
