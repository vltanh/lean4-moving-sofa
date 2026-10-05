"""Local checks for discovery diagnostics and the quantitative cap derivation.

Numerical tests check implementation and identities, not the continuum theorem.
"""
from __future__ import annotations
from fractions import Fraction as F
import subprocess
import sys
import unittest
import numpy as np
from scipy.integrate import quad
from scipy.optimize import linprog
from contacts import ContactProbe, periodic_candidates
from cut_feedback import interpolate_variables
from cut_search import recut, shared_problem, solve_probe
from diagnostics import square_matrix
from q_experiment import PI, QProblem, unit
from solver_recovery import project_feasible
from stability import (align_difference, analytic_constant, cap_energy_matrix,
                       cap_sup_norm, coercivity, free_cap_indices)


class DiscoveryStabilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.p=QProblem(4);cls.x,cls.result=cls.p.solve()
        cls.probe=ContactProbe(cls.p,cls.x)
        cls.energy=cap_energy_matrix(cls.p)

    def test_single_cut_common_fan_matches_original(self):
        q=shared_problem(4,.04,[.04])
        for key in ('angles','support','vertices','eq','ge','matrix'):
            np.testing.assert_allclose(getattr(q,key),getattr(self.p,key),atol=1e-12)

    def test_recut_does_not_change_geometry_or_original(self):
        p=shared_problem(4,.03,[.03,.04,.05]);q=recut(p,.05)
        self.assertEqual(p.phi,.03);self.assertEqual(q.phi,.05)
        np.testing.assert_array_equal(p.vertices,q.vertices)
        self.assertGreater(np.linalg.norm(p.matrix-q.matrix),1e-5)

    def test_invalid_shared_fan_and_contact_parameters(self):
        for phi,cuts in [(0,[0]),(.04,[]),(.04,[.03]),(.04,[.04,.04000000001])]:
            with self.assertRaises(ValueError):shared_problem(4,phi,cuts)
        with self.assertRaises(ValueError):ContactProbe(self.p,np.zeros(1))
        with self.assertRaises(ValueError):self.probe.corner_exposure(0.)
        with self.assertRaises(ValueError):self.probe.wall_slacks(0)
        with self.assertRaises(ValueError):self.probe.tail_transition(1,1)

    def test_warm_interpolation_on_identical_fan(self):
        np.testing.assert_allclose(interpolate_variables(self.p,self.x,self.p),self.x,atol=1e-12)

    def test_probe_solver_matches_baseline(self):
        x,row=solve_probe(self.p,self.x)
        self.assertTrue(row['success'],row['message'])
        self.assertGreater(row['inequality_min'],-1e-8)
        self.assertAlmostEqual(row['q'],self.result['q'],places=8)
        self.assertLess(row['equality_max_abs'],1e-10)

    def test_periodic_candidates(self):
        points=periodic_candidates(-PI/4,0,2*PI)
        np.testing.assert_allclose(points,[3*PI/4,7*PI/4])

    def test_continuous_wedge_minimum_against_dense_samples(self):
        ts=np.linspace(0,PI/2,8193)
        u=np.c_[np.cos(ts),np.sin(ts)];v=np.c_[-np.sin(ts),np.cos(ts)]
        z=np.r_[self.x,1.]
        h=np.array([self.p.support_row(0,t)@z for t in ts])
        k=np.array([self.p.support_row(0,t+PI/2)@z for t in ts])
        for point in np.random.default_rng(7).uniform([-2,-.2],[2,1.2],(8,2)):
            exact,angle=self.probe.wedge_penetration(point)
            sampled=float(np.min(np.maximum(1+u@point-h,1+v@point-k)))
            radius=np.max(np.linalg.norm(self.probe.vertices[0]-point,axis=1))
            self.assertLessEqual(exact,sampled+1e-12)
            self.assertLessEqual(sampled-exact,radius*(PI/2)/8192+1e-10)
            self.assertTrue(0<=angle<=PI/2)

    def test_own_corner_never_has_positive_full_minimum(self):
        for t in [.01,.07,.31,.8,1.27]:
            point=self.p.corner_rows(t)@np.r_[self.x,1.]
            minimum,_=self.probe.wedge_penetration(point)
            self.assertLessEqual(minimum,1e-12)

    def test_wall_minimum_uses_whole_cell(self):
        z=np.r_[self.x,1.]
        for body in (1,2):
            for row in self.probe.wall_slacks(body):
                ts=np.linspace(row['lo'],row['hi'],101)
                if body==1:
                    sampled=[1-(self.p.support_row(0,t)+self.p.support_row(1,t+PI))@z for t in ts]
                else:
                    sampled=[1-(self.p.support_row(0,t+PI/2)+self.p.support_row(2,t+3*PI/2))@z for t in ts]
                self.assertLessEqual(row['slack'],min(sampled)+1e-11)

    def test_cap_energy_matches_independent_six_term_matrix(self):
        nk=2*self.p.m+1
        np.testing.assert_allclose(self.energy,square_matrix(self.p)[:nk,:nk],atol=1e-11)

    def test_translation_is_removed_not_penalized(self):
        nk=2*self.p.m+1;translation=np.cos(self.p.angles[:nk])
        self.assertLess(np.linalg.norm(self.energy@translation),1e-10)
        np.testing.assert_allclose(align_difference(self.p,translation),0,atol=1e-12)
        free=free_cap_indices(self.p)
        self.assertGreater(np.linalg.eigvalsh(self.energy[np.ix_(free,free)])[0],.01)

    def test_uniform_bound_and_optimal_polygon_witness(self):
        row=coercivity(self.p)
        self.assertLess(row['cap_sup_constant'],analytic_constant(.04))
        self.assertAlmostEqual(row['witness_energy'],1.,places=10)
        self.assertAlmostEqual(row['witness_sup_norm'],row['cap_sup_constant'],places=10)
        rng=np.random.default_rng(91)
        for _ in range(12):
            d=rng.normal(size=2*self.p.m+1);d[self.p.m]=0
            d=align_difference(self.p,d)
            energy=float(d@self.energy@d)
            self.assertLessEqual(cap_sup_norm(self.p,d),analytic_constant(.04)*np.sqrt(energy)+1e-10)

    def test_uniform_norm_is_not_just_nodal_sampling(self):
        d=np.zeros(2*self.p.m+1);d[1]=1;d[2]=1;d=align_difference(self.p,d)
        norm=cap_sup_norm(self.p,d)
        sampled=max(abs(self.p.support_row(0,t)[:len(d)]@d) for t in np.linspace(0,PI,2001))
        self.assertGreaterEqual(norm,sampled-1e-12)
        self.assertLess(norm-sampled,1e-3)

    def test_quantitative_concavity_identity(self):
        rng=np.random.default_rng(43)
        d=self.p.basis@rng.normal(size=self.p.basis.shape[1])
        energy=float(np.r_[d,0.]@square_matrix(self.p)@np.r_[d,0.])
        for lam in [.1,.4,.9]:
            actual=self.p.objective(self.x+lam*d)-((1-lam)*self.p.objective(self.x)+lam*self.p.objective(self.x+d))
            self.assertAlmostEqual(actual,lam*(1-lam)*energy,places=8)

    def test_deficit_dominates_cap_energy_for_feasible_competitor(self):
        rows=self.p.ge@self.p.transform
        lp=linprog(np.random.default_rng(31).normal(size=self.p.basis.shape[1]),
            A_ub=-rows[:,:-1],b_ub=rows[:,-1],bounds=[(-10,10)]*self.p.basis.shape[1],method='highs')
        self.assertTrue(lp.success)
        competitor=self.p.particular+self.p.basis@lp.x
        for scale in [.1,.5,1.]:
            y=(1-scale)*self.x+scale*competitor
            delta=y[:2*self.p.m+1]-self.x[:2*self.p.m+1]
            energy=float(delta@self.energy@delta)
            self.assertGreaterEqual(self.p.objective(self.x)-self.p.objective(y),energy-1e-7)

    def test_integrating_factors_on_independent_smooth_function(self):
        phi=.04;v=PI/2;b=v-phi;target=PI-phi
        f=lambda t:np.sin(2*t)+.2*np.sin(4*t)
        fp=lambda t:2*np.cos(2*t)+.8*np.cos(4*t)
        r1=lambda t:-np.tan(t)*f(t)-fp(t)
        r2=lambda t:f(t+v)-fp(t)
        r3=lambda t:f(target)/np.sin(target-t)-f(t)/np.tan(target-t)-fp(t)
        r4=lambda t:f(t)/np.tan(t)-fp(t)
        t=(v+PI)/2
        self.assertAlmostEqual(f(t),-np.sin(t)*quad(lambda u:r4(u)/np.sin(u),v,t)[0],places=10)
        t=(b+v)/2
        rebuilt=-f(target)*np.cos(t)/np.cos(phi)+np.sin(target-t)*quad(lambda u:r3(u)/np.sin(target-u),t,v)[0]
        self.assertAlmostEqual(f(t),rebuilt,places=10)
        t=(phi+b)/2
        rebuilt=f(b)-quad(lambda u:f(u+v),t,b)[0]+quad(r2,t,b)[0]
        self.assertAlmostEqual(f(t),rebuilt,places=10)
        t=phi/2
        rebuilt=np.cos(t)*(f(phi)/np.cos(phi)+quad(lambda u:r1(u)/np.cos(u),t,phi)[0])
        self.assertAlmostEqual(f(t),rebuilt,places=10)

    def test_rational_bound_is_strictly_below_12_over_5(self):
        c2=2*(F('0.041')+F('1.001')**2*F('1.494')+F('1.001')**2*F('0.041')
              +(F('1.001')*(F('1.494')*F('0.708')+F('0.041')*F('0.2')))**2)
        self.assertLess(c2,F(12,5)**2)
        with self.assertRaises(ValueError):analytic_constant(.1)

    def test_feasibility_projection_preserves_feasible_solution(self):
        x,row=project_feasible(self.p,self.x)
        self.assertLess(row['distance_l1_reduced'],1e-8)
        np.testing.assert_allclose(x,self.x,atol=1e-8)

    def test_feasibility_projection_repairs_perturbed_solution(self):
        bad=self.x.copy();bad[0]+=.1;bad[self.p.m]+=.05
        x,row=project_feasible(self.p,bad)
        self.assertGreater(row['inequality_min'],-1e-7)
        self.assertLess(row['equality_max_abs'],1e-10)
        self.assertGreater(row['support_change_l2'],.01)

    def test_discovery_imports_no_reference(self):
        code='import contacts,cut_search,cut_feedback,stability,solver_recovery,sys; assert not any("gerver" in x.lower() for x in sys.modules)'
        subprocess.run([sys.executable,'-c',code],check=True,cwd=__import__('pathlib').Path(__file__).parent)


if __name__=='__main__':
    unittest.main()
