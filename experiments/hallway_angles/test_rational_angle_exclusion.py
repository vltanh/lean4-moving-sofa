"""Exact arithmetic tests for the unconditional rational-angle exclusion."""
from fractions import Fraction as F
import unittest

from rational_angle_exclusion import (
    ROOT_LO, ROOT_HI, LEFT, RIGHT, MEDIANT,
    mediant_gap_upper, prove,
)


class RationalAngleExclusionTests(unittest.TestCase):
    def test_farey_neighbors(self):
        self.assertEqual(
            RIGHT.numerator * LEFT.denominator
            - LEFT.numerator * RIGHT.denominator,
            1,
        )

    def test_mediant_is_the_minimum_denominator_candidate(self):
        self.assertEqual(
            MEDIANT,
            F(LEFT.numerator + RIGHT.numerator,
              LEFT.denominator + RIGHT.denominator),
        )
        self.assertEqual(MEDIANT.denominator, 723688)
        self.assertTrue(LEFT < ROOT_LO < MEDIANT < ROOT_HI < RIGHT)

    def test_mediant_is_strictly_excluded(self):
        self.assertLess(mediant_gap_upper(), 0)

    def test_exact_record(self):
        record = prove()
        self.assertEqual(
            record["conclusion"],
            "if beta_model/pi=p/q in lowest terms then q>723688",
        )
        self.assertLess(F(record["mediant_gap_upper"]), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
