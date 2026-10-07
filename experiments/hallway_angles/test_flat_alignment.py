"""Regression checks for the analytic flat-contact argument, not its proof."""
from fractions import Fraction
import math
import unittest
import numpy as np
from reverse_exact import ReverseSofa
from limiting_profile import T,area_constant
from near_reversal_coefficients import coefficients


class FlatContactAlignment(unittest.TestCase):
    def test_positive_contact_length_and_limit(self):
        limit=3*(1-T)/(2*(1+T))
        for e in [.5,.2,.1,.05,.025]:
            shape=ReverseSofa(e)
            _,dh,_=shape.support(0.)
            ell=e*dh
            self.assertGreater(ell,.25)
            self.assertAlmostEqual(ell,limit,delta=.3*e**2)

    def test_directional_width_lower_bound(self):
        for e in [.5,.2,.1,.05]:
            shape=ReverseSofa(e)
            _,dh,_=shape.support(0.)
            ell=e*dh
            polygon=shape.polygon(257)*np.array([e,1.])
            for nu in np.linspace(-e,e,41):
                n=np.array([math.sin(nu)/e,math.cos(nu)])
                values=polygon@n
                width=values.max()-values.min()
                lower=math.cos(nu)+ell*abs(math.sin(nu))/e
                self.assertGreaterEqual(width+2e-13,lower)

    def test_nonzero_tilt_cost_dominates_scaling_for_candidate(self):
        # This is only a candidate-width regression, not a numerical
        # certification of the uniform theorem constants for competitors.
        for e in [.2,.1,.05]:
            _,dh,_=ReverseSofa(e).support(0.)
            ell=e*dh
            for nu in [1e-7,1e-5,e/10,e/2]:
                lower=math.cos(nu)+ell*math.sin(nu)/e
                self.assertGreater(lower,math.cos(nu/2))

    def test_scaled_deficit_identity(self):
        for e in [.1,.05,.02]:
            value=ReverseSofa(e).area()
            for deficit in [0.,.0001,.01]:
                area=value-deficit/e
                for nu in [0.,e/10,e/2]:
                    lam=math.cos(nu/2)
                    gap=e*(value-lam*lam*area)
                    rhs=deficit+e*area*math.sin(nu/2)**2
                    self.assertAlmostEqual(gap,rhs,delta=5e-16)

    def test_next_area_coefficient_without_fit(self):
        c1=(9-4*T-9*T*T)/(8*(1+T)**2)
        for e in [.1,.05,.025]:
            estimate=(ReverseSofa(e).area()-area_constant()/e)/e
            self.assertAlmostEqual(estimate,c1,delta=.005*e**2)

    def test_exact_coefficient_enclosures(self):
        result=coefficients();den=result['denominator']
        brackets={
            'leading_area':('1.356533732452','1.356533732453'),
            'next_area':('0.094773305749','0.094773305750'),
            'limit_contact_length':('0.286932535095','0.286932535096')}
        for key,(left,right) in brackets.items():
            lo,hi=result[key]
            self.assertLess(Fraction(left),Fraction(lo,den))
            self.assertLess(Fraction(hi,den),Fraction(right))


if __name__=='__main__':unittest.main()
