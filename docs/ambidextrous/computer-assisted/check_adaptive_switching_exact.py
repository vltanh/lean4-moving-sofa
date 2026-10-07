"""Bounded exact rational checks of AS.10/AS.11. No continuum proof claim.
Run: timeout 5s python -u check_adaptive_switching_exact.py
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from hashlib import sha256
from time import perf_counter
import json


def positive(v):
    return max(Q(0), v)


def run():
    start = perf_counter()
    grid = [Q(0), Q(1, 8), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)]
    count = positive_mismatch = equal_profiles = 0
    for d_u, d_v, n_u, n_v in product(grid, repeat=4):
        a, b = n_u - d_v, n_v - d_u
        cross = max(d_u, n_v) + max(d_v, n_u) - max(d_u + d_v, n_u + n_v)
        triangle = (abs(a) + abs(b) - abs(a + b)) / 2
        thickness_difference = abs((1 - d_u - n_u) - (1 - d_v - n_v)) / 2
        assert cross == positive(a) + positive(b) - positive(a + b)
        assert cross == triangle
        assert Q(0) <= cross <= thickness_difference
        count += 1
        positive_mismatch += cross > 0
        equal_profiles += thickness_difference == 0
        if thickness_difference == 0:
            assert cross == 0
    assert positive_mismatch > 0 and equal_profiles > 0
    result = {
        'status': 'exact_rational_regressions_passed',
        'cases': count,
        'strict_switching_mismatch_cases': positive_mismatch,
        'equal_profile_cases': equal_profiles,
        'arithmetic': 'Fraction with exact unbounded integers',
        'bounds_proved_by_code': False,
        'continuum_full_turn_optimality_proved': False,
        'source_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'internal_seconds': perf_counter() - start,
        'ci_or_lean_used': False,
    }
    return result


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
