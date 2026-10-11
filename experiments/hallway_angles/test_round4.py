"""Local regression and exact-certificate tests; no CI or Lean invocation."""
from fractions import Fraction
import math
import unittest
import numpy as np
from scipy.integrate import quad
from shapely.geometry import Polygon
from parameter_certificate import Interval,SCALE,pi_interval
from extended_width_certificate import prove_extended_width,stable_parameters
from branch_comparison_certificate import (prove_monotonicity,prove_early_reverse_exclusion,
    certify_root,comparison_at_degrees,derivative_numerator,sinc_derivative)
from circular_notch import CircularNotchSofa
from limiting_profile import (left_boundary,upper_boundary,profile_polygon,area_constant,T)
from reverse_exact import ReverseSofa


class ExactCertificates(unittest.TestCase):
    def test_full_obtuse_width_cover(self):
        r=prove_extended_width(256)
        self.assertEqual(r['epsilon_over_pi_interval'],['0','1/2'])
        self.assertGreater(min(r['minimum_lower_numerators']),0)
    def test_coarse_width_rejected(self):
        with self.assertRaises(ArithmeticError):prove_extended_width(8)
    def test_monotonicity_cover(self):
        r=prove_monotonicity(512)
        self.assertLess(r['maximum_upper_numerator'],0)
    def test_coarse_monotonicity_rejected(self):
        with self.assertRaises(ArithmeticError):prove_monotonicity(8)
    def test_entire_early_exclusion(self):
        self.assertGreater(prove_early_reverse_exclusion(256)['minimum_lower_numerator'],0)
    def test_coarse_exclusion_rejected(self):
        with self.assertRaises(ArithmeticError):prove_early_reverse_exclusion(8)
    def test_lower_root(self):
        r=certify_root('lower',Fraction('133.644346372'),Fraction('133.644346373'))
        self.assertGreater(r['left_positive_lower_numerator'],0)
        self.assertLess(r['right_negative_upper_numerator'],0)
    def test_upper_root(self):
        r=certify_root('upper',Fraction('142.098382576'),Fraction('142.098382577'))
        self.assertGreater(r['left_positive_lower_numerator'],0)
        self.assertLess(r['right_negative_upper_numerator'],0)
    def test_wrong_root_bracket_rejected(self):
        with self.assertRaises(ArithmeticError):certify_root('lower',Fraction(130),Fraction(131))
    def test_invalid_inputs_rejected(self):
        for f in [prove_extended_width,prove_monotonicity,prove_early_reverse_exclusion]:
            for bad in [0,-1,True,1.5]:
                with self.assertRaises(ValueError):f(bad)
        with self.assertRaises(ValueError):comparison_at_degrees(Fraction(90),'lower')
        with self.assertRaises(ValueError):comparison_at_degrees(Fraction(130),'unknown')
    def test_removable_endpoint_parameters(self):
        _,_,_,r,s=stable_parameters(pi_interval()/2)
        self.assertTrue(r.contains(Fraction(1)))
        approx=(s.lo+s.hi)/(2*SCALE)
        self.assertAlmostEqual(approx,math.pi/4+1/4,places=13)
        self.assertTrue(sinc_derivative(Interval.rational(0)).contains(Fraction(0)))
    def test_derivative_independent_finite_difference(self):
        for e in [.1,.4,.8,1.4]:
            v=derivative_numerator(Interval.rational(Fraction.from_float(e)))
            result=(v.lo+v.hi)/(2*SCALE)
            h=1e-5
            fd=(ReverseSofa(e+h).area()-ReverseSofa(e-h).area())/(2*h)*math.sin(e)**2
            self.assertAlmostEqual(result,fd,delta=3e-8)


class CrossingEstimates(unittest.TestCase):
    def test_rational_narrow_width_constant(self):
        self.assertGreater(27*(1000**2-983**2)*1000**4,983**6)
    def test_full_width_extended_range(self):
        threshold=math.acos(math.sqrt(2)-1)
        for e in [.1,.5,math.pi/3,threshold]:
            for phi in np.linspace(e/1000,e/2,201):
                psi=e-phi
                j=math.cos(psi)**2+(1+math.cos(phi))*math.cos(psi)-1
                self.assertGreater(j,0)
    def test_full_width_estimate_really_fails_beyond_threshold(self):
        e,phi=math.radians(80),math.radians(1)
        psi=e-phi
        self.assertLess(math.cos(psi)**2+(1+math.cos(phi))*math.cos(psi)-1,0)
    def test_uniform_scaled_coercivity_matrix(self):
        for e in np.linspace(.005,.5,60):
            a,b=1-math.cos(e),1+math.cos(e)
            mat=np.array([[a/e**2-(a+1)/math.pi**2,-1/math.pi],
                          [-1/math.pi,b-(b+1)*e**2/math.pi**2]])
            self.assertGreater(np.linalg.eigvalsh(mat)[0],.25)
    def test_free_endpoint_coercivity_limit(self):
        target=(1/T-1)/2
        for e in [.02,.01,.005]:
            z=ReverseSofa(e).constants;d,q,K,eta=(z[x] for x in ['d','q','K','eta'])
            E=(q/d)*((2*d-1)*math.sin(K)-eta*(2*d+1)*math.cos(K))/((1+d)*math.sin(K)+eta*(1-d)*math.cos(K))
            self.assertAlmostEqual(-E/e,target,delta=2*e**2)
    def test_alignment_width_shortcut_fails(self):
        # The sign is opposite to the one needed to cancel scaling loss.
        e=math.pi/6;z=ReverseSofa(e).constants;d,m,q=z['d'],z['m'],z['q']
        tt=z['eta']*math.tan(z['K'])
        c1=-2*(tt*d+tt+d-2)/((1+tt)*m)
        c2=(2*tt*d+3*tt+2*d-3)/(4*(1+tt))
        self.assertLess((c1+2*c2)/q-2*ReverseSofa(e).area(),0)


class CircularConstruction(unittest.TestCase):
    def test_hammersley_special_case(self):
        s=CircularNotchSofa(math.pi/2)
        self.assertAlmostEqual(s.radius,2/math.pi)
        self.assertAlmostEqual(s.area(),math.pi/2+2/math.pi)
    def test_positive_top_bridge(self):
        for b in np.linspace(.01,math.pi-.01,100):
            self.assertLess(CircularNotchSofa(b).top_height,1)
    def test_independent_area_quadrature(self):
        for deg in [30,60,90,120,150,170]:
            s=CircularNotchSofa(math.radians(deg));R=s.disk_radius;a=s.disk_center_height
            removed=quad(lambda y:2*math.sqrt(max(0,R*R-(y-a)**2)),0,s.top_height,epsabs=2e-11)[0]
            self.assertAlmostEqual(math.pi/2+2*s.radius-removed,s.area(),places=9)
    def test_endpoint_motion(self):
        for deg in [30,90,120,170]:
            s=CircularNotchSofa(math.radians(deg));p=s.corner(np.array([0,s.beta]))
            np.testing.assert_allclose(p,[[s.radius,0],[-s.radius,0]],atol=1e-13)
    def test_all_pose_grid_regression(self):
        for deg in [30,90,120,150]:
            s=CircularNotchSofa(math.radians(deg))
            xx,yy=np.meshgrid(np.linspace(-s.radius-1,s.radius+1,121),np.linspace(0,1,81))
            p=np.column_stack([xx.ravel(),yy.ravel()]);p=p[s.contains(p)]
            for theta in np.linspace(0,s.beta,73):
                n=np.array([[-math.sin(theta),math.cos(theta)],
                            [math.sin(s.beta-theta),math.cos(s.beta-theta)]])
                f=(p-s.corner(theta))@n.T;v=np.max(f,axis=1)
                self.assertGreaterEqual(np.min(v),-2e-12)
                self.assertLessEqual(np.max(v),1+1e-12)
    def test_invalid_construction_rejected(self):
        for b in [0,math.pi,float('nan')]:
            with self.assertRaises(ValueError):CircularNotchSofa(b)
        with self.assertRaises(ValueError):CircularNotchSofa(math.pi/2,2)


class LimitProfile(unittest.TestCase):
    def test_endpoints_and_symmetry(self):
        x,y=left_boundary(np.array([-.5,0,.5]))
        np.testing.assert_allclose(x[[0,2]],[0,0],atol=1e-14)
        np.testing.assert_allclose(y,[-.5,0,.5],atol=1e-14)
        xr,yr=upper_boundary(np.array([0,1]))
        self.assertAlmostEqual(xr[1],1.5)
        self.assertAlmostEqual(yr[0],.5)
        self.assertAlmostEqual(yr[1],0)
        self.assertGreater(xr[0],0)
    def test_convex_profile_and_area(self):
        p=Polygon(profile_polygon(2001))
        self.assertTrue(p.is_valid)
        self.assertLess(abs(p.convex_hull.area-p.area),1e-12)
        self.assertAlmostEqual(p.area,area_constant(),delta=2e-7)
    def test_positive_left_height_derivative(self):
        u=np.linspace(-.5,.5,1001);x,y=left_boundary(u)
        self.assertGreater(np.diff(y).min(),0)
        self.assertLessEqual(x.max(),1e-14)
    def test_second_order_boundary_convergence(self):
        u=np.linspace(-.5,.5,501);v=u+.5;xl,yl=left_boundary(u);xr,yr=upper_boundary(v)
        errors=[]
        for e in [.2,.1,.05,.025]:
            s=ReverseSofa(e);x,y,*_=s.corner(e*u);h,dh,_=s.support(e*v)
            xp=e*(h*np.sin(e*v)+dh*np.cos(e*v));yp=h*np.cos(e*v)-dh*np.sin(e*v)
            error=max(np.max(abs(e*x-xl)),np.max(abs(y-yl)),np.max(abs(xp-xr)),np.max(abs(yp-yr)))
            self.assertLess(error,.11*e**2)
            errors.append(error)
        for a,b in zip(errors,errors[1:]):self.assertGreater(a/b,3.9)
    def test_limiting_all_pose_constraints(self):
        p=profile_polygon(501)
        for v in np.linspace(0,1,101):
            cx,cy=left_boundary(v-.5)
            f=(p-np.array([cx,cy]))@np.array([[v,1],[1-v,-1]]).T
            m=f.max(axis=1)
            self.assertGreaterEqual(m.min(),-1e-12)
            self.assertLessEqual(m.max(),1+1e-12)
    def test_top_and_bottom_spurs_are_excluded(self):
        # Endpoint pose alone has a zero x coefficient: nearby poses are essential.
        for x,y in [(-.1,-.5),(-.1,.5)]:
            v=1e-5 if y<0 else 1-1e-5
            cx,cy=left_boundary(v-.5)
            f=(np.array([x,y])-np.array([cx,cy]))@np.array([[v,1],[1-v,-1]]).T
            self.assertLess(f.max(),0)
    def test_invalid_profile_parameters_rejected(self):
        with self.assertRaises(ValueError):left_boundary(.6)
        with self.assertRaises(ValueError):upper_boundary(-.1)
        with self.assertRaises(ValueError):profile_polygon(True)


if __name__=='__main__':unittest.main()
