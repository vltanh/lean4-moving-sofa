"""Scalar-proof and numerical-regression tests; not a sofa optimality checker."""
from fractions import Fraction as F
import math
import unittest
import mpmath as mp
import numpy as np
from scipy.integrate import quad
from shapely.geometry import Polygon

from forward_contact_equations import ForwardContactModel as Model
from reverse_exact import ReverseSofa
from contact_crossing_certificate import (I,SCALE,Jet,ZERO,pi_interval,interval,
    reduced_sin_cos,hyper_interval,at,isolate_t,prove_model)


def mid(x):return (x.lo+x.hi)/(2*SCALE)


def independent_area(m):
    a=m.alpha;b=m.beta-a
    def pairs(theta):
        f,df=m.support_pair(theta)
        return float(f*f-df*df+f+.5)
    def cross(t):
        x,y,dx,dy=m.central(t)
        return float(x*dy-y*dx)
    f,fp=m.support_pair(b)
    return (2*(quad(pairs,0,a,epsabs=1e-12)[0]+quad(pairs,a,b,epsabs=1e-12)[0])
            -quad(cross,-m.T,m.T,epsabs=1e-12)[0]/2+2*(f+.5)*fp)


class ScalarCertificateChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.proof=prove_model(256)
        cls.pi=pi_interval()

    def test_crossing_uniqueness_certificate(self):
        p=self.proof
        self.assertGreater(p['minimum_F_T'],0)
        self.assertLess(p['maximum_along_branch_derivative'],0)
        self.assertEqual(p['root_bend_degrees_interval'],['136.672184698','136.672184699'])
        self.assertGreater(p['endpoint_records'][0]['gap'][0],0)
        self.assertLess(p['endpoint_records'][1]['gap'][1],0)
        self.assertIn('NOT a forward-class',p['warning'])

    def test_root_tube_has_no_gaps(self):
        prev=F(135)
        for r in self.proof['tube_records']:
            lo,hi=map(F,r['beta_degrees'])
            self.assertEqual(lo,prev);self.assertGreater(hi,lo);prev=hi
            self.assertLess(r['derivative_upper'],0)
            self.assertLess(r['T'][0],r['T'][1])
        self.assertEqual(prev,F(140))

    def test_reject_invalid_cell_counts(self):
        for n in [True,0,-1,F(3,2)]:
            with self.assertRaises(ValueError):prove_model(n)

    def test_coarse_crossing_cover_is_rejected(self):
        with self.assertRaises(ArithmeticError):prove_model(1)

    def test_reduced_trigonometry_against_high_precision(self):
        with mp.workdps(90):
            for q in [F(-4),F(-12,5),F(0),F(12,5),F(4)]:
                s,c=reduced_sin_cos(I.rational(q))
                x=mp.mpf(q.numerator)/q.denominator
                self.assertTrue(s.contains(F(mp.nstr(mp.sin(x),85))))
                self.assertTrue(c.contains(F(mp.nstr(mp.cos(x),85))))
        with self.assertRaises(ValueError):reduced_sin_cos(I.rational(5))

    def test_hyperbolic_enclosures_against_high_precision(self):
        with mp.workdps(90):
            for q in [F(-4),F(-1,2),F(0),F(7,10),F(4)]:
                s,c=hyper_interval(I.rational(q));x=mp.mpf(q.numerator)/q.denominator
                self.assertTrue(s.contains(F(mp.nstr(mp.sinh(x),85))))
                self.assertTrue(c.contains(F(mp.nstr(mp.cosh(x),85))))
        with self.assertRaises(ValueError):hyper_interval(I.rational(-5))

    def test_jet_arithmetic_exact(self):
        x=Jet(I.rational(2),I.rational(1),ZERO)
        y=Jet(I.rational(3),ZERO,I.rational(1))
        z=(x.square()+x*y)/y
        self.assertTrue(z.v.contains(F(10,3)))
        self.assertTrue(z.db.contains(F(7,3)))
        self.assertTrue(z.dt.contains(F(-4,9)))

    def test_model_jet_matches_independent_float_formula(self):
        for deg in [135,137,140]:
            m=Model.solve(math.radians(deg));b=self.pi*I.rational(deg,180)
            f,g,w,a=at(b,I.rational(F(str(m.T))),self.pi)
            self.assertAlmostEqual(mid(f.v),m.residual(),places=12)
            self.assertAlmostEqual(mid(w.v),m.signed_area(),places=12)
            self.assertAlmostEqual(mid(g.v),m.signed_area()-ReverseSofa(math.pi-m.beta).area(),places=12)
            self.assertAlmostEqual(mid(a.v),m.alpha,places=12)

    def test_automatic_derivatives_against_finite_differences(self):
        eps=1e-6
        for deg in [135,137,140]:
            m=Model.solve(math.radians(deg));b=self.pi*I.rational(deg,180)
            f,g,w,_=at(b,I.rational(F(str(m.T))),self.pi)
            def vals(beta,t):
                z=Model(beta,t)
                return np.array([z.residual(),z.signed_area()-ReverseSofa(math.pi-beta).area(),z.signed_area()])
            db=(vals(m.beta+eps,m.T)-vals(m.beta-eps,m.T))/(2*eps)
            dt=(vals(m.beta,m.T+eps)-vals(m.beta,m.T-eps))/(2*eps)
            np.testing.assert_allclose([mid(x.db) for x in [f,g,w]],db,rtol=1e-7,atol=1e-8)
            np.testing.assert_allclose([mid(x.dt) for x in [f,g,w]],dt,rtol=1e-7,atol=1e-8)

    def test_interval_newton_contains_endpoint_solutions(self):
        for lo,hi in [(F(135),F(13501,100)),(F(13999,100),F(140))]:
            t=isolate_t(self.pi*interval(lo/180,hi/180),self.pi)
            for b in [lo,(lo+hi)/2,hi]:
                root=Model.solve(math.radians(float(b))).T
                self.assertLess(t.lo/SCALE-1e-14,root)
                self.assertGreater(t.hi/SCALE+1e-14,root)


class ContactGeometryRegressions(unittest.TestCase):
    def test_boundary_matching_conditions(self):
        for deg in [135,136.672184698,137,140]:
            m=Model.solve(math.radians(deg));a=m.alpha
            x,y,dx,dy=m.central(-m.T)
            n2=np.array([math.sin(m.beta-a),math.cos(m.beta-a)])
            self.assertAlmostEqual(n2@np.array([dx,dy]),0,places=12)
            self.assertAlmostEqual(y+math.cos(m.beta-a),0,places=12)
            p,_=m.circle_and_vertex()
            n1=np.array([-math.sin(a),math.cos(a)])
            jn1=np.array([-math.cos(a),-math.sin(a)])
            self.assertAlmostEqual(n1@np.array([x,y]),p*math.sin(a)+(math.cos(a)-1)/2,places=12)
            self.assertAlmostEqual(jn1@np.array([x,y])+n1@np.array([dx,dy]),p*math.cos(a)-math.sin(a)/2,places=12)

    def test_motion_continuity_and_reflection(self):
        for deg in [135,137,140]:
            m=Model.solve(math.radians(deg));a=m.alpha
            left=m.corner([a-1e-8,a,a+1e-8])
            self.assertLess(np.max(np.abs(left-left[1])),1e-7)
            t=np.linspace(0,m.beta,129);c=m.corner(t)
            np.testing.assert_allclose(c,c[::-1]*np.array([-1,1]),atol=3e-14)
            self.assertAlmostEqual(c[0,1],0,places=12)
            self.assertAlmostEqual(c[-1,1],0,places=12)

    def test_first_phase_radius_half(self):
        m=Model.solve(math.radians(137));p,_=m.circle_and_vertex()
        t=np.linspace(0,m.alpha,101);f,df=m.support_pair(t)
        n=np.column_stack([-np.sin(t),np.cos(t)]);jn=np.column_stack([-np.cos(t),-np.sin(t)])
        inner=f[:,None]*n+df[:,None]*jn;outer=inner+n;center=np.array([-p,.5])
        np.testing.assert_allclose(np.linalg.norm(inner-center,axis=1),.5,atol=1e-14)
        np.testing.assert_allclose(np.linalg.norm(outer-center,axis=1),.5,atol=1e-14)

    def test_central_euler_equation(self):
        J=np.array([[0,-1],[1,0]])
        for deg in [135,137,140]:
            m=Model.solve(math.radians(deg));z=m.constants
            t=np.linspace(-m.T,m.T,101)
            A,B,r,mu,z0=(z[k] for k in ['A','B','r','mu','z0'])
            q=np.column_stack([A*np.sin(t)+B*np.sinh(mu*t),A*np.cos(t)+r*B*np.cosh(mu*t)+z0])
            dq=np.column_stack([A*np.cos(t)+mu*B*np.cosh(mu*t),-A*np.sin(t)+r*mu*B*np.sinh(mu*t)])
            ddq=np.column_stack([-A*np.sin(t)+mu**2*B*np.sinh(mu*t),-A*np.cos(t)+r*mu**2*B*np.cosh(mu*t)])
            D=np.diag([1-z['d'],1+z['d']])
            residual=2*ddq@D.T+dq@J.T+q@(2*D-np.eye(2)).T+np.array([0,2*z['c']])
            self.assertLess(np.max(abs(residual)),3e-14)

    def test_closed_signed_area_against_quadrature(self):
        for deg in [135,136.672184698,137,140]:
            m=Model.solve(math.radians(deg))
            self.assertAlmostEqual(m.signed_area(),independent_area(m),places=11)

    def test_boundary_polygon_area_converges(self):
        for deg in [135,137,140]:
            m=Model.solve(math.radians(deg));errors=[]
            for n in [129,513,2049]:
                shape=Polygon(m.boundary_polygon(n))
                self.assertTrue(shape.is_valid)
                errors.append(abs(shape.area-m.signed_area()))
            self.assertLess(errors[-1],4e-8)
            self.assertGreater(errors[0],errors[1]);self.assertGreater(errors[1],errors[2])

    def test_model_scope_errors(self):
        for deg in [90,120,150,180]:
            with self.assertRaises(ValueError):Model(math.radians(deg),.7)
        for t in [0,float('nan'),2]:
            with self.assertRaises(ValueError):Model(math.radians(137),t)
        m=Model.solve(math.radians(137))
        with self.assertRaises(ValueError):m.corner([-1])
        with self.assertRaises(ValueError):m.boundary_polygon(2)


if __name__=='__main__':unittest.main(verbosity=2)
