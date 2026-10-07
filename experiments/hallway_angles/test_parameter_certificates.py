"""Exact-rational regression tests for the small theorem checkers."""
import ast
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import random
import unittest

from parameter_certificate import Interval as I, SCALE, ceil_div, pi_interval, sin_cos, prove
from width_certificate import sinc, prove_width


def rational_trig(x, cosine=False, terms=100):
    start = 0 if cosine else 1
    value = sum(((-1)**j*x**(2*j+start)/factorial(2*j+start)
                 for j in range(terms)), F(0))
    error = abs(x)**(2*terms+start)/factorial(2*terms+start)
    return value-error, value+error


class ParameterCertificateTests(unittest.TestCase):
    def test_signed_ceiling(self):
        for a in range(-11,12):
            for b in range(-5,6):
                if b:
                    n=ceil_div(a,b)
                    self.assertTrue(n-1 < F(a,b) <= n)

    def test_rational_conversion_and_arithmetic(self):
        rng=random.Random(907)
        for _ in range(250):
            a,b=F(rng.randint(-50,50),rng.randint(1,53)),F(rng.randint(-50,50),rng.randint(1,53))
            A,B=I.rational(a),I.rational(b)
            self.assertTrue(A.contains(a))
            self.assertTrue((A+B).contains(a+b))
            self.assertTrue((A-B).contains(a-b))
            self.assertTrue((A*B).contains(a*b))
            if b: self.assertTrue((A/B).contains(a/b))

    def test_interval_corners(self):
        rng=random.Random(908)
        for _ in range(100):
            a0,a1=sorted([rng.randint(-100,100),rng.randint(-100,100)])
            b0,b1=sorted([rng.randint(1,100),rng.randint(1,100)])
            A=I(a0*SCALE//7,ceil_div(a1*SCALE,7))
            B=I(b0*SCALE//11,ceil_div(b1*SCALE,11))
            for a in (F(a0,7),F(a1,7)):
                for b in (F(b0,11),F(b1,11)):
                    self.assertTrue((A*B).contains(a*b))
                    self.assertTrue((A/B).contains(a/b))
                    self.assertTrue((A/(-B)).contains(-a/b))

    def test_square_crosses_zero(self):
        a=I(-2*SCALE,3*SCALE).square()
        self.assertEqual((a.lo,a.hi),(0,9*SCALE))

    def test_square_roots(self):
        for a in range(40):
            A=I.rational(a,7)
            B=A.sqrt()
            self.assertLessEqual(B.lo*B.lo,A.lo*SCALE)
            self.assertGreaterEqual(B.hi*B.hi,A.hi*SCALE)
        self.assertTrue(I.rational(4).sqrt().contains(F(2)))

    def test_pi_enclosure(self):
        pi=pi_interval()
        self.assertGreater(F(pi.lo,SCALE),F('3.14159265358979323846264338327'))
        self.assertLess(F(pi.hi,SCALE),F('3.14159265358979323846264338331'))
        self.assertLessEqual(pi.hi-pi.lo,2)

    def test_point_trigonometry_against_rational_series(self):
        for x in [F(j,7) for j in range(-28,29,3)]:
            sn,cs=sin_cos(I.rational(x))
            for interval,cosine in ((sn,False),(cs,True)):
                lo,hi=rational_trig(x,cosine)
                self.assertTrue(interval.contains(lo))
                self.assertTrue(interval.contains(hi))

    def test_interval_trigonometry(self):
        A=I(I.rational(F(1,3)).lo,I.rational(F(2,3)).hi)
        sn,cs=sin_cos(A)
        for x in (F(1,3),F(1,2),F(2,3)):
            for interval,cosine in ((sn,False),(cs,True)):
                lo,hi=rational_trig(x,cosine)
                self.assertTrue(interval.contains(lo))
                self.assertTrue(interval.contains(hi))

    def test_sinc_at_zero_and_near_zero(self):
        self.assertTrue(sinc(I.rational(0)).contains(F(1)))
        for x in (F(1,1000),F(1,3),F(4)):
            lo,hi=rational_trig(x)
            result=sinc(I.rational(x))
            self.assertTrue(result.contains(lo/x))
            self.assertTrue(result.contains(hi/x))

    def test_parameter_cover(self):
        result=prove(64)
        self.assertEqual(len(result['cell_lower_numerators']),64)
        self.assertGreater(result['minimum_R_lower_numerator'],0)
        self.assertGreater(result['minimum_X_lower_numerator'],0)

    def test_width_cover_including_zero(self):
        result=prove_width(64)
        self.assertEqual(len(result['cell_lower_numerators']),64)
        self.assertTrue(all(x>0 for x in result['minimum_lower_numerators']))

    def test_coarse_cover_is_rejected_not_assumed(self):
        with self.assertRaises(ArithmeticError): prove(8)

    def test_no_float_literals_or_third_party_imports(self):
        # A code audit aid, not a proof of the mathematical formulas.
        allowed={'__future__','dataclasses','fractions','math','argparse','json','pathlib','parameter_certificate'}
        for name in ('parameter_certificate.py','width_certificate.py'):
            tree=ast.parse(Path(__file__).with_name(name).read_text())
            for node in ast.walk(tree):
                if isinstance(node,ast.Constant): self.assertNotIsInstance(node.value,float)
                if isinstance(node,ast.Import):
                    self.assertTrue(all(alias.name in allowed for alias in node.names))
                if isinstance(node,ast.ImportFrom): self.assertIn(node.module,allowed)

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError): I(2,1)
        with self.assertRaises(TypeError): I(0.0,1)
        with self.assertRaises(ZeroDivisionError): I.rational(1)/I(-1,1)
        with self.assertRaises(ValueError): I.rational(-1).sqrt()
        with self.assertRaises(ValueError): sin_cos(I.rational(5))
        with self.assertRaises(ValueError): sinc(I.rational(5))
        for n in (0,-1,True):
            with self.assertRaises(ValueError): prove(n)
            with self.assertRaises(ValueError): prove_width(n)


if __name__ == '__main__':
    unittest.main()
