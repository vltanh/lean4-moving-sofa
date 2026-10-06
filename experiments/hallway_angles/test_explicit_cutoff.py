"""Local regression tests; only integer interval covers certify scalar bounds."""
from fractions import Fraction as F
import math
import unittest

import numpy as np
from shapely.geometry import Polygon, box

from explicit_cutoff_certificate import BOUNDS, prove_propagation, prove_scalars, quantities
from parameter_certificate import Interval, SCALE
from reverse_exact import ReverseSofa, width_majorant


def midpoint(interval):
    return (interval.lo+interval.hi)/(2*SCALE)


class ExactChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = prove_scalars(256)

    def test_whole_parameter_cover(self):
        self.assertEqual(self.record['epsilon_interval'], ['0', '1/10'])
        self.assertEqual(len(self.record['cell_margins']), 256)
        for row in self.record['cell_margins']:
            self.assertEqual(set(row), set(BOUNDS))
            self.assertTrue(all(min(v) > 0 for v in row.values()))

    def test_closed_zero_endpoint(self):
        values = quantities(Interval.rational(0))
        self.assertAlmostEqual(midpoint(values['eV']), 1.35653373245229, places=12)
        self.assertTrue(all(v.lo <= v.hi for v in values.values()))

    def test_certificate_domains(self):
        for value in [F(-1, 100), F(11, 100)]:
            with self.assertRaises(ValueError):
                quantities(Interval.rational(value))
        for n in [True, 0, -1, F(1, 2)]:
            with self.assertRaises(ValueError):
                prove_scalars(n)

    def test_coarse_cover_rejected(self):
        with self.assertRaises(ArithmeticError):
            prove_scalars(1)

    def test_exact_cutoff_propagation(self):
        proof = prove_propagation()
        self.assertEqual(proof['epsilon_cutoff'], '1/19')
        self.assertTrue(all(F(v)>0 for v in proof['rational_slacks'].values()))
        self.assertEqual(F(proof['rational_slacks']['alignment_contradiction_slack']),
                         F(166189, 7125000))

    def test_smaller_cutoffs(self):
        for e in [F(1, 10000), F(1, 100), F(1, 20)]:
            self.assertEqual(prove_propagation(e)['status'], 'all rational inequalities positive')

    def test_aggressive_cutoff_is_inconclusive(self):
        with self.assertRaisesRegex(ArithmeticError, 'alignment_contradiction_slack'):
            prove_propagation(F(53, 1000))

    def test_invalid_cutoff(self):
        for value in [F(0), F(-1), F(1, 9)]:
            with self.assertRaises(ValueError):
                prove_propagation(value)

    def test_177_degrees_is_covered(self):
        self.assertLess(F(22, 7), F(60, 19))


class IndependentFormulaChecks(unittest.TestCase):
    def test_area_flat_width_and_width_slopes(self):
        for e in [.001, .01, .05, .1]:
            sofa = ReverseSofa(e)
            v = quantities(Interval.rational(F(str(e))))
            self.assertAlmostEqual(midpoint(v['eV']), e*sofa.area(), places=11)
            self.assertAlmostEqual(midpoint(v['ell']), e*float(sofa.support(0)[1]), places=11)
            self.assertAlmostEqual(midpoint(v['width_half_slope']),
                                   2*e*(sofa.area()-width_majorant(e, .5)), places=10)
            h = 1e-5
            derivative = e*(width_majorant(e, 1)-width_majorant(e, 1-h))/h
            self.assertAlmostEqual(midpoint(v['width_slope']), derivative, places=5)

    def test_jacobi_and_width_fields_on_whole_sampled_arc(self):
        for e in [.0001, .01, .05, .1]:
            z = ReverseSofa(e).constants
            s,c,k,K,r,eta = (z[key] for key in ['s','c','k','K','r','eta'])
            t = np.linspace(0,e/2,4097)
            sk,ck = np.sin(k*t),np.cos(k*t)
            st,ct = np.sin(t),np.cos(t)
            dj=c*math.sin(K)+r*s*math.cos(K)
            p=s*(math.sin(K)-eta*math.cos(K))/dj
            jx=-(sk*ct+r*ck*st)/dj
            jy=-p-(r*ck*ct-sk*st)/dj
            self.assertLessEqual(np.max(abs(jx)),1+1e-12)
            self.assertLess(np.max(abs(jy/e)),16/25)
            self.assertTrue(np.all(np.diff(jx)<=1e-14))
            self.assertTrue(np.all(np.diff(jy)>=-1e-14))
            bw=1/(2*s*z['denominator'])
            aw=-c/(2*s)+(r/s)*bw*math.sin(K)
            wx=e*(aw+bw*(ck*ct-r*sk*st))
            wy=-bw*(ck*st+r*sk*ct)
            self.assertLess(np.max(abs(wx)),7/20)
            self.assertLessEqual(np.max(abs(wy)),.5+1e-12)

    def test_trace_matrix_constants(self):
        m=np.array([[35/96,-1/3],[-1/3,43/24]])
        mi=np.linalg.inv(m)
        tx=np.array([1,1/200])@mi@np.array([1,1/200])/2
        ty=np.array([.5,1])@mi@np.array([.5,1])/2
        self.assertAlmostEqual(tx,4135701/2498000,places=12)
        self.assertAlmostEqual(ty,1320/1249,places=12)

    def test_zero_endpoint_trace_against_quadrature(self):
        rng=np.random.default_rng(5)
        u=np.linspace(-.5,.5,8193)
        j=np.arange(1,6)[:,None]
        basis=np.sin(j*math.pi*(u+.5))
        deriv=j*math.pi*np.cos(j*math.pi*(u+.5))
        for e in [.001,.05,.1]:
            for _ in range(5):
                coeff=rng.normal(size=(2,5))
                p,q=coeff@basis
                dp,dq=coeff@deriv
                aa=2*math.sin(e/2)**2;bb=1+math.cos(e)
                energy=np.trapezoid((aa/e**2)*dp**2+bb*dq**2
                       -(aa+1)*p**2-(bb+1)*e**2*q**2+p*dq-q*dp,u)/2
                self.assertGreater(energy,0)
                xx=np.cos(e*u)*p+e*np.sin(e*u)*q
                yy=-np.sin(e*u)*p/e+np.cos(e*u)*q
                self.assertLessEqual(np.max(xx**2), (4135701/2498000)*energy+1e-9)
                self.assertLessEqual(np.max(yy**2), (1320/1249)*energy+1e-9)


class GeometryChecks(unittest.TestCase):
    def test_triangle_lemma_sharp_example(self):
        a,b,d=2.,3.,.01
        z=math.sqrt(a*b*d)
        low=Polygon([(0,0),(z/a,0),(0,z/b)])
        high=Polygon([(1,1),(1-z/a,1),(1,1-z/b)])
        shape=box(0,0,1,1).difference(low.union(high))
        pts=np.array(shape.exterior.coords)
        projections=pts@np.array([a,b])
        self.assertAlmostEqual(1-shape.area,d,places=12)
        self.assertAlmostEqual(np.ptp(projections),a+b-2*math.sqrt(a*b*d),places=12)

    def test_triangle_regime_cannot_be_dropped(self):
        a,b,d=100.,1.,.9
        shape=box(0,0,.1,1)
        pts=np.array(shape.exterior.coords)
        width=np.ptp(pts@np.array([a,b]))
        self.assertGreater(d,min(a/(2*b),b/(2*a)))
        self.assertLess(width,a+b-2*math.sqrt(a*b*d))

    def test_contact_core_for_scaled_feasible_candidates(self):
        for e in [.01,.05,.1]:
            sofa=ReverseSofa(e)
            points=sofa.polygon(1025)*np.array([e,1])
            phi=np.linspace(0,e,257)
            normals=np.stack((np.column_stack((np.sin(phi)/e,np.cos(phi))),
                              np.column_stack((np.sin(e-phi)/e,-np.cos(e-phi)))),axis=1)
            reference=np.column_stack(sofa.corner(phi-e/2)[:2])*np.array([e,1])
            ell=e*float(sofa.support(0)[1])
            for lam in [.99999,.9999]:
                p=lam*points
                supports=np.max(np.einsum('nij,pj->nip',normals,p),axis=2)
                corners=np.linalg.solve(normals,(supports-1)[...,None])[...,0]
                gauge=(corners[0,0]+corners[-1,0])/2
                corners[:,0]-=gauge;p[:,0]-=gauge
                shape=Polygon(p)
                deficit=e*sofa.area()-shape.area
                ex=2.5*math.sqrt(deficit)+3.5*deficit
                ey=1.7*math.sqrt(deficit)+5*deficit
                self.assertLessEqual(np.max(abs(corners-reference),axis=0)[0],ex)
                self.assertLessEqual(np.max(abs(corners-reference),axis=0)[1],ey)
                core=box(ex,-.5+ey,ell-ex,.5-ey)
                self.assertGreater(core.area,0)
                self.assertLessEqual(core.difference(shape).area,deficit+1e-12)
                cp=np.array(core.exterior.coords)
                shifted=supports-normals[:,:,0]*gauge
                residual=np.einsum('nij,pj->nip',normals,cp)-shifted[:,:,None]
                self.assertLessEqual(np.max(residual),1e-12)


if __name__=='__main__':
    unittest.main(verbosity=2)
