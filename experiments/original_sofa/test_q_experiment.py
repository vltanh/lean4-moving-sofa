"""Run locally: python -m unittest discover -s experiments/original_sofa -v."""
from __future__ import annotations
import unittest
import numpy as np
from q_experiment import PI, QProblem, unit, tangent
from diagnostics import audit
from motion_validation import conservative_shape


class QExperimentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.p=QProblem(4)
        cls.x,cls.result=cls.p.solve(0)

    def test_invalid_parameters(self):
        for kwargs in [{'intervals':3},{'intervals':4,'phi':0},
                       {'intervals':4,'phi':PI/4},{'intervals':4,'wall_samples':0},
                       {'intervals':4,'quadrature':1}]:
            with self.subTest(kwargs=kwargs),self.assertRaises(ValueError):
                QProblem(**kwargs)

    def test_support_interpolation_at_normals(self):
        z=np.r_[self.x,1.]
        for body in range(3):
            interpolated=np.array([self.p.support_row(body,t)@z for t in self.p.angles])
            np.testing.assert_allclose(interpolated,self.p.support[body]@z,atol=1e-12)

    def test_area_against_shoelace(self):
        z=np.r_[self.x,1.]
        vertices=self.p.vertices[0]@z
        following=np.roll(vertices,-1,axis=0)
        shoelace=.5*np.sum(vertices[:,0]*following[:,1]-vertices[:,1]*following[:,0])
        self.assertAlmostEqual(shoelace,float(z@self.p.area_matrix@z),places=11)

    def test_quadratic_gradient(self):
        rng=np.random.default_rng(10)
        z=np.r_[self.x,1.]
        gradient=2*(self.p.matrix@z)[:-1]
        for _ in range(4):
            direction=rng.normal(size=self.p.size)
            direction/=np.linalg.norm(direction)
            eps=1e-5
            difference=(self.p.objective(self.x+eps*direction)-self.p.objective(self.x-eps*direction))/(2*eps)
            self.assertAlmostEqual(float(gradient@direction),difference,places=7)

    def test_main_quadrature_refinement(self):
        other=QProblem(4,quadrature=16)
        np.testing.assert_allclose(self.p.matrix,other.matrix,atol=1e-12,rtol=1e-12)

    def test_independent_mamikon_decomposition(self):
        self.assertLess(audit(self.p)['square_decomposition_max_abs'],1e-9)

    def test_affine_restricted_concavity(self):
        h=self.p.reduced[:-1,:-1]
        self.assertLess(np.max(np.linalg.eigvalsh(2*h)),1e-10)
        self.assertGreater(np.count_nonzero(abs(np.linalg.eigvalsh(2*h))<1e-8),1)
        rng=np.random.default_rng(25)
        delta=self.p.basis@rng.normal(size=self.p.basis.shape[1])
        gap=self.p.objective(self.x+delta/2)-.5*(self.p.objective(self.x)+self.p.objective(self.x+delta))
        self.assertGreaterEqual(gap,-1e-10)

    def test_solver_feasibility_and_independent_start(self):
        x,result=self.p.solve(1)
        self.assertTrue(self.result['success'],self.result['message'])
        self.assertTrue(result['success'],result['message'])
        for row in (self.result,result):
            self.assertLess(row['equality_max_abs'],1e-9)
            self.assertGreater(row['inequality_min'],-1e-8)
            self.assertGreater(row['cap_area'],2.2)
        self.assertLess(abs(result['q']-self.result['q']),1e-8)
        np.testing.assert_allclose(x[:2*self.p.m+1],self.x[:2*self.p.m+1],atol=2e-5)

    def test_nested_sampling_is_not_a_lower_bound(self):
        coarse=self.p.validate(self.x,128)
        fine=self.p.validate(self.x,512)
        self.assertLessEqual(fine['sampled_sofa_area'],coarse['sampled_sofa_area']+1e-10)
        self.assertGreater(fine['between_node_wall_violation'],1e-6)
        self.assertEqual(fine['positive_area_components'],1)
        self.assertLess(fine['cap_hull_area_discrepancy'],1e-9)

    def test_margin_construction_and_off_grid_motion(self):
        sofa,result=conservative_shape(self.p,self.x,128)
        self.assertFalse(result['arithmetic_certified'])
        self.assertTrue(result['polygon_valid'])
        self.assertEqual(result['positive_area_components'],1)
        self.assertLess(result['conservative_constructed_area'],self.p.validate(self.x,512)['sampled_sofa_area'])
        points=np.asarray(sofa.exterior.coords)
        points=np.vstack([points,(points+np.roll(points,1,axis=0))/2])
        vertices=self.p.vertices[0]@np.r_[self.x,1.]
        for t in np.random.default_rng(5).uniform(0,PI/2,80):
            u,v=unit(t),tangent(t)
            h,k=np.max(vertices@u),np.max(vertices@v)
            first,second=points@u-h+1,points@v-k+1
            self.assertGreaterEqual(float(np.min(np.maximum(first,second))),-1e-8)

    def test_reject_infeasible_validation(self):
        bad=self.x.copy();bad[self.p.m]=10
        with self.assertRaises(ValueError):
            conservative_shape(self.p,bad,128)


if __name__=='__main__':
    unittest.main()
