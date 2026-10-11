"""Exact arithmetic checks for ultradeep_rational_exclusion.py."""
from fractions import Fraction
import unittest

from ultradeep_rational_exclusion import LOWER, UPPER, SCALE, prove


class UltraDeepRationalExclusionTests(unittest.TestCase):
    def test_farey_neighbors(self):
        self.assertEqual(
            UPPER.numerator*LOWER.denominator
            - LOWER.numerator*UPPER.denominator,
            1,
        )

    def test_denominator_sum(self):
        self.assertEqual(
            LOWER.denominator+UPPER.denominator,
            120960480401807934322756058341844601463578189551623733657668053196745441803,
        )

    def test_exact_signs(self):
        r=prove()
        self.assertGreater(Fraction(r["lower_gap"][0]),0)
        self.assertLess(Fraction(r["upper_gap"][1]),0)
        self.assertEqual(r["farey_determinant"],1)

    def test_expected_conclusion(self):
        r=prove()
        self.assertEqual(
            r["minimum_denominator"],
            120960480401807934322756058341844601463578189551623733657668053196745441803,
        )


if __name__=="__main__":
    unittest.main(verbosity=2)
