"""Local numerical regressions; no workflow or Lean build required."""
import math
import unittest
import numpy as np
from geometry import Motion, clip_halfplane, sampled_intersection, largest_component
from pressure import clip, area_gradient
from pressure_search import interpolation_matrix, default_seed, optimize_pressure

class PressureTests(unittest.TestCase):
    def test_clipping_matches_reference(self):
        rng=np.random.default_rng(91)
        angles=np.sort(rng.uniform(0,2*math.pi,21))
        poly=np.column_stack((np.cos(angles),np.sin(angles)))
        for _ in range(20):
            n=rng.normal(size=2);n/=np.linalg.norm(n)
            rhs=float(rng.uniform(-1.1,1.1))
            np.testing.assert_allclose(clip(poly,n,rhs),clip_halfplane(poly,n,rhs),atol=1e-13)
    def test_all_free_partial_derivatives(self):
        rng=np.random.default_rng(71)
        for deg in (30,60,90,120,150):
            for mode in ('forward','reverse'):
                m=default_seed(math.radians(deg),mode,9)
                c=m.corners.copy();c[:,0]+=rng.normal(0,.004,9);c[1:-1,1]+=rng.normal(0,.004,7)
                m=Motion(m.beta,mode,c)
                area,g,info=area_gradient(m)
                ref=largest_component(sampled_intersection(m)).area
                self.assertAlmostEqual(area,ref,places=11)
                self.assertEqual(info['unassigned_length'],0.)
                self.assertEqual(info['tied_length'],0.)
                for i in range(9):
                    for j in range(2):
                        if j==1 and i in (0,8): continue
                        p=c.copy();q=c.copy();eps=1e-6
                        p[i,j]+=eps;q[i,j]-=eps
                        fp=area_gradient(Motion(m.beta,mode,p))[0]
                        fm=area_gradient(Motion(m.beta,mode,q))[0]
                        self.assertAlmostEqual(g[i,j],(fp-fm)/(2*eps),delta=2e-6)
    def test_horizontal_gauge(self):
        m=default_seed(math.pi/3,'forward',17)
        a,g,_=area_gradient(m)
        c=m.corners.copy();c[:,0]+=3.
        b,_,_=area_gradient(Motion(m.beta,m.mode,c))
        self.assertAlmostEqual(a,b,places=11)
        self.assertAlmostEqual(float(g[:,0].sum()),0.,places=9)
    def test_interpolation(self):
        for basis in ('linear','cubic'):
            b=interpolation_matrix(9,33,basis)
            np.testing.assert_allclose(b.sum(axis=1),1.,atol=1e-14)
            np.testing.assert_allclose(b[::4],np.eye(9),atol=1e-14)
        for args in [(8,33,'linear'),(9,32,'linear'),(9,35,'linear'),(9,33,'bad')]:
            with self.assertRaises(ValueError):interpolation_matrix(*args)
    def test_chain_rule(self):
        rng=np.random.default_rng(11)
        for basis in ('linear','cubic'):
            b=interpolation_matrix(9,33,basis)
            m=default_seed(math.radians(120),'forward',9)
            c=m.corners.copy();c[1:-1]+=rng.normal(0,.01,(7,2))
            dense=b@c;dense[[0,-1],1]=0.
            a,g,_=area_gradient(Motion(m.beta,m.mode,dense))
            gg=b.T@g
            for i,j in [(1,0),(4,1),(6,0)]:
                eps=1e-6;p=c.copy();q=c.copy();p[i,j]+=eps;q[i,j]-=eps
                pp=b@p;qq=b@q;pp[[0,-1],1]=0.;qq[[0,-1],1]=0.
                fp=area_gradient(Motion(m.beta,m.mode,pp))[0]
                fm=area_gradient(Motion(m.beta,m.mode,qq))[0]
                self.assertAlmostEqual(gg[i,j],(fp-fm)/(2*eps),delta=3e-6)
    def test_structural_ties_are_reported(self):
        m=default_seed(math.pi/2,"reverse",9)
        _,_,info=area_gradient(m)
        self.assertGreater(info["tied_length"],0.)

    def test_empty_intersection(self):
        c=np.zeros((5,2));c[2,1]=-10.
        a,g,info=area_gradient(Motion(math.pi/2,'forward',c))
        self.assertEqual(a,0.)
        self.assertTrue(np.all(g==0))
    def test_optimizer_retains_best(self):
        m=default_seed(math.pi/2,'forward',9)
        out,record=optimize_pressure(m,9,2,maxiter=4)
        self.assertGreaterEqual(record['best_sampled_area'],record['initial_sampled_area'])
        self.assertAlmostEqual(area_gradient(out)[0],record['best_sampled_area'],places=10)
        self.assertTrue(np.isfinite(out.corners).all())

if __name__=='__main__':unittest.main()
