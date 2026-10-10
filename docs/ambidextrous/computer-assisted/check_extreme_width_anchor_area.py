"""Exact rational upper-Riemann verifier for the W=2*sqrt(2) anchor-area theorem.

Mathematical inclusion and midpoint width rigidity are proved separately
in three-point-switching-fiber-width.md and extreme-width-anchored-area.md.
This checks only the final finite rational slice area. No floating point,
no optimizer, no Lean, and no unsound sampled-angle area inference.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

ROOT_LO = Q(1414213562, 10**9)
ROOT_HI = Q(1414213563, 10**9)
assert ROOT_LO * ROOT_LO < 2 < ROOT_HI * ROOT_HI
WIDTH_LO = 2 * ROOT_LO
N = 1024
DX = ROOT_HI / N
LIPSCHITZ = Q(12, 5)
TARGET = Q(41, 25)
TRIPLES = ((3, 4, 5), (5, 12, 13), (8, 15, 17))
ANGLES = []
for a, b, hyp in TRIPLES:
    assert a * a + b * b == hyp * hyp
    ANGLES.extend(((Q(a, hyp), Q(b, hyp)),
                   (Q(b, hyp), Q(a, hyp))))
    assert max(Q(a, b), Q(b, a)) <= LIPSCHITZ


def upper_halfwidth(x: Q) -> Q:
    """Rational majorant on the x<=sqrt(2) half projection."""
    caps = [Q(1, 2), x, ROOT_HI - x]
    for cosine, sine in ANGLES:
        # True -b_t(x) is max of these two affine expressions,
        # with 2*sqrt(2) in place of WIDTH_LO. Replacing width
        # by the smaller WIDTH_LO raises the first expression.
        first = (1 - (WIDTH_LO - x) * cosine) / sine
        second = (1 - x * sine) / cosine
        caps.append(max(first, second))
    return min(caps)


def main() -> None:
    values = []
    for i in range(N):
        middle = DX * Q(2 * i + 1, 2)
        values.append(max(Q(0), upper_halfwidth(middle)))
    midpoint_area = 4 * DX * sum(values)
    # The r(x)_+ envelope is LIPSCHITZ-Lipschitz, so the
    # full-area midpoint rule's upward error is 2*L*ROOT_HI*DX.
    correction = 2 * LIPSCHITZ * ROOT_HI * DX
    certified_upper = midpoint_area + correction
    assert certified_upper == Q(170619797734244653516561,
                                104857600000000000000000)
    assert certified_upper < TARGET
    report = {
        'status': 'exact_rational_slice_upper_passed',
        'scope': 'W exactly 2sqrt2, complete two-handed turns, with anchoring theorem',
        'angles_cos_sin': [list(map(str, pair)) for pair in ANGLES],
        'root_lower': str(ROOT_LO), 'root_upper': str(ROOT_HI),
        'cells': N, 'lipschitz': str(LIPSCHITZ),
        'midpoint_area': str(midpoint_area),
        'midpoint_correction': str(correction),
        'exact_area_upper': str(certified_upper),
        'comparison_target': str(TARGET),
        'strict_margin': str(TARGET - certified_upper),
        'global_sharp_optimality_proved': False,
        'lean_or_ci_run': False,
    }
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
