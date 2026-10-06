"""Exact arithmetic tests for deep_rational_exclusion.py."""
from fractions import Fraction
import unittest

from deep_rational_exclusion import LOWER, UPPER, prove


class DeepRationalExclusionTests(unittest.TestCase):
    def test_farey_neighbors(self):
        self.assertEqual(
            UPPER.numerator*LOWER.denominator
            - LOWER.numerator*UPPER.denominator,
            1,
        )

    def test_denominator_bound(self):
        self.assertEqual(
            LOWER.denominator+UPPER.denominator,
            3193502245874191590,
        )

    def test_exact_sign_certificate(self):
        record = prove()
        self.assertGreater(Fraction(record["lower_gap"][0]), 0)
        self.assertLess(Fraction(record["upper_gap"][1]), 0)
        self.assertEqual(
            record["conclusion"],
            "if beta_model/pi=p/q in lowest terms then q>=3193502245874191590",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
