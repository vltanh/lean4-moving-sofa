"""Local tests for the interior-core certificate, separate from the geometry proof."""
from fractions import Fraction as F
import math
import unittest
import numpy as np
from shapely.geometry import Polygon, box

from interior_core_certificate import (EMAX, I, SCALE, span, constants, scalars,
    corner_point, outer_point, prove_foundation, prove_directions, path_constants)
from reverse_exact import ReverseSofa, width_majorant


class InteriorCoreChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.foundation=prove_foundation(64,128)
        cls.directions=prove_directions(cls.foundation,1024)

    def test_whole_angle_and_direction_covers(self):
        self.assertEqual(self.foundation['epsilon_interval'],['0','1/8'])
        self.assertEqual(self.directions['epsilon_cutoff'],'1/8')
        self.assertEqual(len(self.directions['cell_records']),1024)
        self.assertGreater(F(self.directions['minimum_normalized_margin']),F(5,1000))
        previous=F(0)
        for row in self.directions['cell_records']:
            a,b=map(F,row['t_interval'])
            self.assertEqual(a,previous)
            self.assertLess(a,b)
            self.assertGreater(F(row['normalized_width_margin']),0)
            self.assertTrue(all(F(v)>0 for v in row['other_slacks']))
            previous=b
        self.assertEqual(previous,F(7,8))

    def test_zero_direction_uses_exact_full_height(self):
        k=self.directions['cell_records'][0]['rectangle']
        self.assertEqual(self.foundation['rectangles'][k]['height'],SCALE)

    def test_rectangles_have_valid_dimensions(self):
        for r in self.foundation['rectangles']:
            self.assertLessEqual(r['left'],0)
            self.assertGreater(r['right'],0)
            self.assertEqual(r['width'],r['right']-r['left'])
            self.assertEqual(r['height'],2*r['half_height'])
            self.assertTrue(0<r['height']<=SCALE)

    def test_common_rectangles_against_sampled_candidate(self):
        # A supplementary floating-point check, not the interval proof.
        for e in [.005,.06,.125]:
            p=ReverseSofa(e).polygon(2049)*np.array([e,1])
            body=Polygon(p)
            self.assertTrue(body.is_valid)
            for r in self.foundation['rectangles'][::4]:
                rect=box(r['left']/SCALE,-r['half_height']/SCALE,
                         r['right']/SCALE,r['half_height']/SCALE)
                self.assertLess(rect.difference(body).area,3e-8)

    def test_reject_out_of_range_cutoff(self):
        with self.assertRaises(ValueError):
            prove_directions(self.foundation,32,F(13,100))
        for bad in [True,0,-1,F(1,2)]:
            with self.assertRaises(ValueError):
                prove_directions(self.foundation,bad)

    def test_coarse_direction_cover_rejects(self):
        with self.assertRaises(ArithmeticError):
            prove_directions(self.foundation,1)

    def test_invalid_foundation_not_silently_used(self):
        bad=dict(self.foundation,denominator=SCALE+1)
        with self.assertRaises(ValueError):prove_directions(bad,8)

    def test_path_constants_exact(self):
        r=path_constants()
        self.assertEqual(r['trace_squared'],['80896975/54550528','12025/13318'])
        self.assertEqual(F(r['slacks']['coarse_width_97']),F(3,25600))
        self.assertTrue(all(F(v)>0 for v in r['slacks'].values()))
        M=np.array([[.39,-.32],[-.32,1.97]])
        for row,expected in [(np.array([1,1/128]),F(r['trace_squared'][0])),
                             (np.array([.5,1]),F(r['trace_squared'][1]))]:
            self.assertAlmostEqual(row@np.linalg.inv(M)@row/2,float(expected),places=12)

    def test_removable_zero_endpoint(self):
        z=constants(I.rational(0))
        v=scalars(z)
        self.assertLess(F(v['eV'].lo,SCALE),F('1.35653373245230'))
        self.assertGreater(F(v['eV'].hi,SCALE),F('1.35653373245228'))
        x,y=corner_point(z,F(1,2))
        self.assertEqual((x.lo,x.hi),(0,0))
        self.assertEqual((y.lo,y.hi),(SCALE//2,SCALE//2))
        self.assertEqual(outer_point(z,F(0))[1].lo,SCALE//2)

    def test_formula_enclosures_against_independent_evaluator(self):
        for e in [.01,.08,.125]:
            body=ReverseSofa(e);z=constants(I.rational(F(str(e))))
            m=lambda x:(x.lo+x.hi)/(2*SCALE)
            self.assertAlmostEqual(m(scalars(z)['eV']),e*body.area(),places=10)
            for u in [F(0),F(1,4),F(1,2)]:
                xi,yi=corner_point(z,u)
                x,y,*_=body.corner(float(u)*e)
                self.assertAlmostEqual(m(xi),e*float(x),places=10)
                self.assertAlmostEqual(m(yi),float(y),places=10)
            for u in [F(0),F(1,4),F(3,4)]:
                xi,yi=outer_point(z,u);phi=float(u)*e
                h,dh,_=body.support(phi)
                x=e*(h*math.sin(phi)+dh*math.cos(phi))
                y=h*math.cos(phi)-dh*math.sin(phi)
                self.assertAlmostEqual(m(xi),float(x),places=10)
                self.assertAlmostEqual(m(yi),float(y),places=10)

    def test_width_bootstrap_over_near_full_width(self):
        for e in [.005,.06,.125]:
            V=ReverseSofa(e).area()
            for w in [.971,.98,.99,.999]:
                self.assertGreater(e*(V-width_majorant(e,w)),(1-w)/4)

    def test_invalid_parameter_domains(self):
        for e in [F(-1,100),F(13,100)]:
            with self.assertRaises(ValueError):constants(I.rational(e))
        for bad in [0,True,F(1,2)]:
            with self.assertRaises(ValueError):prove_foundation(bad,8)


if __name__=='__main__':unittest.main(verbosity=2)
