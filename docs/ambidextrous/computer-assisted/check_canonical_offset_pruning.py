"""Exact rational audit of canonical-support trimming for four 3-4-5 hallways.

Run: timeout 5s python -u check_canonical_offset_pruning.py
This checks finite arithmetic and certificates for a necessary support polytope;
it does not check a huge search tree, a continuum motion, or sharp optimality.
"""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256
from pathlib import Path
from time import perf_counter
import json

# Five times each coordinate: the original eight-dimensional source box.
ROOT = [(-5, 23), (-20, 4), (-5, 19), (-25, 3)] * 2
# An exhaustive canonical-support replacement after moving a connected
# component's left and bottom extremes to zero.
TRIM = [(-5, 18), (-5, -1), (-5, 14), (-5, -2),
        (-2, 18), (-5, -1), (-1, 14), (-5, -2)]


def support_intervals(box):
    # Five times the actual linear supports for the eight normals:
    # A1=(4,3), B1=(-3,4), A2=(3,4), B2=(-4,3),
    # C1=(4,-3), D1=(-3,-4), C2=(3,-4), D2=(-4,-3); /5 each.
    shifts = [5, 5, 5, 5, 2, 1, 1, 2]
    return ([a + t for (a, _), t in zip(box, shifts)],
            [b + t for (_, b), t in zip(box, shifts)])


def compatible_with_necessary_constraints(box):
    low, high = support_intervals(box)
    # A pair of supports cannot have an impossible range difference.
    for i, j, max_scaled in [(0, 4, 6), (2, 6, 8),
                             (1, 5, 8), (3, 7, 6)]:
        if high[i] < low[j] or low[i] - high[j] > max_scaled:
            return False
    # Subadditivity relations between nearby 3-4-5 normals and axis supports.
    # Axis extrema are W <= 5 and H <= 1, multiplied by five here.
    for i, j, axis_bound in [(0, 2, 25), (2, 0, 5),
                             (1, 3, 5), (4, 6, 25)]:
        if 20 * low[i] > 15 * high[j] + 7 * axis_bound:
            return False
    # The remaining four relations have zero support on the negative axes.
    for i, j in [(3, 1), (6, 4), (5, 7), (7, 5)]:
        if 4 * low[i] > 3 * high[j]:
            return False
    # Widths in four antipodal directions are nonnegative.
    for i, j in [(0, 7), (2, 5), (1, 6), (3, 4)]:
        if high[i] + high[j] < 0:
            return False
    return True


def test_support_geometry():
    # Rational points include an x-minimizer and a y-minimizer, possibly distinct.
    shapes = 0
    for w in [Q(9, 5), Q(12, 5), Q(5)]:
        for h in [Q(3, 5), Q(1)]:
            for a in [Q(0), Q(1, 5), h]:
                for b in [Q(0), Q(1, 5), h]:
                    pts = [(Q(0), a), (w, b), (w / 3, Q(0)),
                           (2 * w / 3, h)]
                    normals = [(4, 3), (-3, 4), (3, 4), (-4, 3),
                               (4, -3), (-3, -4), (3, -4), (-4, -3)]
                    support5 = [max(nx * x + ny * y for x, y in pts)
                                for nx, ny in normals]
                    offsets5 = [v - shift for v, shift in
                                zip(support5, [5, 5, 5, 5, 2, 1, 1, 2])]
                    assert all(Q(lo) <= v <= Q(hi)
                               for (lo, hi), v in zip(TRIM, offsets5))
                    assert compatible_with_necessary_constraints(
                        [(v, v) for v in offsets5])
                    shapes += 1
    return shapes


def run():
    start = perf_counter()
    ratio = Q(1)
    for (a, b), (c, d) in zip(ROOT, TRIM):
        assert a <= c < d <= b
        ratio *= Q(d - c, b - a)
    assert ratio == Q(10925, 118013952)
    counts = {}
    for parts in (2, 4):
        subboxes = []
        for i, (a, b) in enumerate(ROOT):
            assert (b - a) % parts == 0
            width = (b - a) // parts
            subboxes.append([(a + j * width, a + (j + 1) * width)
                             for j in range(parts)
                             if a + j * width <= TRIM[i][1]
                             and a + (j + 1) * width >= TRIM[i][0]])
        passing_scalar = 1
        for candidates in subboxes:
            passing_scalar *= len(candidates)
        passing_coupled = sum(compatible_with_necessary_constraints(box)
                              for box in product(*subboxes))
        counts[f'{parts}^8'] = dict(total=parts ** 8,
                                    scalar_possible=passing_scalar,
                                    coupled_possible=passing_coupled)
    assert counts['2^8'] == dict(total=256, scalar_possible=16,
                                coupled_possible=16)
    assert counts['4^8'] == dict(total=65536, scalar_possible=4096,
                                coupled_possible=405)
    shapes = test_support_geometry()
    # Deliberately impossible canonical offset: B1 below its true minimum.
    assert ROOT[1][0] < TRIM[1][0]
    # Original source placement-box coverage is not refuted by this example;
    # only a component-normalized, support-tight representation is pruned.
    result = dict(status='exact_rational_checks_passed',
                  original_root_volume_fraction=str(ratio),
                  original_root_volume_fraction_approx=float(ratio),
                  box_counts=counts, rational_point_set_tests=shapes,
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=perf_counter() - start,
                  external_main_certificate_rerun=False,
                  continuum_sharp_value_proved=False,
                  ci_or_lean_used=False)
    return result


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
