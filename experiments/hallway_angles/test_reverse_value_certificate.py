"""Regression tests for exact scalar evaluations of the theorem's bounds."""
import unittest
from fractions import Fraction as F
from parameter_certificate import Interval as I, SCALE, sin_cos
from reverse_value_certificate import scaled_value, prove_forward_exclusion, value_bounds, decimal_outward


class ReverseValueCertificateTests(unittest.TestCase):
    def test_asymptotic_constant_two_formulas(self):
        root3=I.rational(3).sqrt()
        s,c=sin_cos(root3/2)
        T=s/c/root3
        direct=3*(1+3*T)/(4*(1+T))
        limiting=scaled_value(I.rational(0))
        self.assertLessEqual(direct.lo,limiting.hi)
        self.assertLessEqual(limiting.lo,direct.hi)
        display=decimal_outward(limiting,12)
        self.assertEqual(display,{'lower':'1.356533732452','upper':'1.356533732453'})

    def test_parameter_interval_exclusion(self):
        proof=prove_forward_exclusion(64)
        self.assertEqual(len(proof['cell_lower_numerators']),64)
        self.assertGreater(proof['minimum_lower_numerator'],0)

    def test_outward_decimal_rounding(self):
        for f in (F(1,3),F(-1,3),F(1,1000000),F(0),F(7,3)):
            enclosure=I.rational(f)
            for digits in (0,3,9):
                output=decimal_outward(enclosure,digits)
                self.assertLessEqual(F(output['lower']),f)
                self.assertGreaterEqual(F(output['upper']),f)

    def test_point_values(self):
        result=value_bounds(150)
        self.assertEqual(result['reverse_optimum'],{'lower':'2.641025081','upper':'2.641025082'})
        self.assertEqual(result['unrestricted_upper'],'2.735686')
        result=value_bounds(135)
        self.assertLess(F(result['reverse_optimum']['upper']),F('1.81'))

    def test_invalid_arguments(self):
        for bend in (119,180,True,F(150)):
            with self.assertRaises(ValueError): value_bounds(bend)
        for n in (0,-1,True):
            with self.assertRaises(ValueError): prove_forward_exclusion(n)
        with self.assertRaises(ValueError): decimal_outward(I.rational(1),-1)


if __name__=='__main__':
    unittest.main()
