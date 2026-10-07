"""Supplementary checks of exact motion-rigidity constants and rejection cases."""
from fractions import Fraction as F
import math
import unittest

from explicit_motion_rigidity import prove_motion_rigidity


class MotionRigidityChecks(unittest.TestCase):
    def test_all_exact_slacks(self):
        result=prove_motion_rigidity()
        self.assertEqual(result['epsilon_max'],'1/100')
        self.assertEqual(result['normalized_deficit_max'],'1/10000')
        self.assertTrue(all(F(v)>0 for v in result['rational_slacks'].values()))

    def test_absorption_margin(self):
        s=prove_motion_rigidity()['rational_slacks']
        self.assertEqual(F(s['triangle_absorption']),F(31801,200000))
        self.assertEqual(F(s['horizontal_failure_absorption']),F(47909,50000))

    def test_deficit_and_width_constants(self):
        r=F(prove_motion_rigidity()['deficit_ratio'])
        self.assertEqual(r,1+F(17,50)*40**2/F(100)**2)
        self.assertLess(10*r,11)
        self.assertLess(r,F(103,100)**2)

    def test_penalty_branches(self):
        for e in [F(1,100),F(1,1000)]:
            for n in [F(0),e/100,e/2]:
                small=n*n/(1600*e*e)
                self.assertGreaterEqual(min(F(1,10000),small),0)
                self.assertEqual(min(F(1,10000)/e,n*n/(1600*e**3)),
                                 min(F(1,10000),small)/e)

    def test_horizontal_failure_is_really_needed(self):
        e,D,n=.01,.0001,1e-9
        d=D+.34*n*n
        a,b=math.sin(n)/e,math.cos(n)
        W=.286-2*(2.5*math.sqrt(d)+3.5*d)
        self.assertGreater(d,a*W*W/(2*b))
        self.assertLess(n,41*e*D)

    def test_abstract_width_inequality_excludes_large_mismatch(self):
        # These sample the derived scalar necessary condition, not sofa motions.
        for e in [.0001,.001,.005,.01]:
            for D in [1e-12,1e-8,1e-6,1e-4]:
                start=40*e*math.sqrt(D)*1.001
                end=.75*e
                self.assertLess(start,end)
                for alpha in [0.,.1,.5,1.]:
                    n=(1-alpha)*start+alpha*end
                    d=D+.34*n*n
                    a,b=math.sin(n)/e,math.cos(n)
                    ex=2.5*math.sqrt(d)+3.5*d
                    ey=1.7*math.sqrt(d)+5*d
                    W,H=.286-2*ex,1-2*ey
                    self.assertGreater(W,.225)
                    self.assertGreater(H,.95)
                    if d<a*W*W/(2*b):
                        self.assertLess(d,b*H*H/(2*a))
                        lower=a*W+b*H-2*math.sqrt(a*b*d)
                        self.assertGreater(lower,math.cos(n/2))
                    else:
                        self.assertGreater(n,40*e*d)


if __name__=='__main__':
    unittest.main(verbosity=2)
