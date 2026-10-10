"""Exact rational verification of the seven stated leakage-proof rows.

This is a fixed certificate check, with no search and no numerical
evaluation of square roots or trigonometric functions.
"""

from fractions import Fraction as F


ROWS = [
    (".68568", ".686", ".2724", ".0135", ".377", ".368", F(1, 400000)),
    (".686", ".69", ".2762", ".038", ".3784", ".3627", F(1, 30000)),
    (".69", ".7", ".2859", ".0971", ".3801", ".3492", F(1, 2000)),
    (".7", ".725", ".3113", ".2323", ".3845", ".3161", F(3, 400)),
    (".725", ".75", ".3386", ".3542", ".3799", ".2837", F(31, 1000)),
    (".75", ".775", ".3681", ".4662", ".3765", ".2521", F(83, 1000)),
    (".775", ".8", ".4", ".5703", ".3742", ".2213", F(9, 50)),
]


def verify():
    previous_right = None
    g0 = F(22199, 10000)
    for row_index, row in enumerate(ROWS, start=1):
        a, b, H, h, T, tb, leak = map(F, row)
        assert F(1, 2) < a <= b <= F(4, 5)
        if previous_right is not None:
            assert a == previous_right
        previous_right = b
        assert 0 <= H < 1 and 0 <= h < 1 and 0 <= leak < 1
        epsilon = (h * h + 2 * h) / 4
        z = (1 - b) / (1 + b)
        a0 = h * h / 4 + h**3 / 6
        a1 = h**3 / 12 + h**4 / 16
        sine_lower = (1 - b * b) / (1 + b * b)

        assert (1 - H) ** 2 <= 1 - b * b, (row_index, "H")
        assert (2 + epsilon) ** 2 >= 9 * b * b - F(1, 4) + 9 * H * H / 16, (row_index, "h")
        assert 6 * a * T - T * T >= 1 + F(3, 2) * H, (row_index, "T")
        assert 0 < T < 3 * a
        assert 0 < tb <= 2 * (z - z**3 / 3), (row_index, "t_box")
        assert leak * sine_lower >= a0 * max(T - tb, 0) + a1, (row_index, "leak")

        remainder = g0 - a * (2 - leak)
        assert remainder > 0
        assert a * a + (1 - leak) ** 2 / 4 > remainder**2, (row_index, "Gerver")

    initial = F(8571, 12500)
    assert F(ROWS[0][0]) == initial
    z0 = initial * initial
    assert 35 * z0 - 15 > 0
    overlap = 4 * (1 - z0) - (35 * z0 - 15) ** 2
    assert overlap == F(878611101631, 976562500000000)
    assert overlap > 0
    print("Verified all seven exact rational rows and the initial overlap.")


if __name__ == "__main__":
    verify()
