"""Exact arithmetic sanity checks for the computer-free three-hallway theorem.

The continuum argument (geometry, connectedness, support tightening,
and motion angle reach) is a separate hand proof. This script cannot
verify those claims; it only replays ten rational inequalities.
"""
from fractions import Fraction as F

EPS = F(1, 10**9)


def run():
    checks = {
        "eps_vs_witness_square_area": EPS < F(1, 10000),
        "t_bound": 2 * EPS < F(1, 20000) ** 2,
        "alpha_bound": EPS + F(3, 40000) < F(1, 110) ** 2,
        "parameter_P_bound": F(1, 20000) + F(2, 110) < F(1, 50),
        "band_center_bound": F(1, 20000) + F(1, 110) < F(1, 100),
        "first_wall_depth_gt_one": 361**2 > 2 * 250**2,
        "second_wall_depth_gt_one": 733**2 > 2 * 500**2,
        "three_witness_areas": (
            F(2, 200) ** 2 == F(1, 10000)
            and F(1, 100) ** 2 == F(1, 10000)
        ),
        "witness_inside_A": F(103, 100) > F(2) + F(1, 50) - 1,
        "witness_inside_diagonal_band": F(22, 100) < F(1, 2),
        "boundary_width_two_line_connector": (
            F(6, 5) < F(5, 2) and F(1) == F(2) - 1
            and not (F(3, 2) <= F(6, 5) <= F(5, 2))
            and not (F(0) <= F(6, 5) <= F(1))
        ),
    }
    assert all(checks.values()), checks
    return checks


if __name__ == "__main__":
    for name, passed in run().items():
        print(f"{name}: {'PASS' if passed else 'FAIL'}")
    print("ALL_PASS: True checks: 11")
