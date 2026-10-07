"""Arithmetic, geometry and adversarial tests for the independent checker."""
from fractions import Fraction
import math
import unittest
import numpy as np
import interval_verify as iv
from geometry import Motion,sampled_intersection
from pressure_search import default_seed
from fast_geometry import fast_intersection,enclose_fast
from swept import enclose_swept

class IntervalTests(unittest.TestCase):
    def test_machin_pi_bounds(self):
        # Decimal endpoints are well-known loose bounds, not the source of PI.
        self.assertGreater(Fraction(iv.PI[0],iv.Q),Fraction('3.14159265358979323846264338'))
        self.assertLess(Fraction(iv.PI[1],iv.Q),Fraction('3.14159265358979323846264339'))
    def test_exact_trigonometric_values(self):
        for a,s,c in [(0,0,1),(1,0,-1),(-1,0,-1),(Fraction(1,2),1,0),(Fraction(-1,2),-1,0)]:
            ss,cc=iv.trig_point(Fraction(a))
            self.assertLessEqual(ss[0],s*iv.Q);self.assertGreaterEqual(ss[1],s*iv.Q)
            self.assertLessEqual(cc[0],c*iv.Q);self.assertGreaterEqual(cc[1],c*iv.Q)
        ss,_=iv.trig_point(Fraction(1,6));_,cc=iv.trig_point(Fraction(1,3))
        self.assertLessEqual(ss[0],iv.Q//2);self.assertGreaterEqual(ss[1],iv.Q//2)
        self.assertLessEqual(cc[0],iv.Q//2);self.assertGreaterEqual(cc[1],iv.Q//2)
    def test_trig_ranges(self):
        for a,b in [(Fraction(-1),Fraction(1)),(Fraction(-2,3),Fraction(1,5)),(Fraction(1,5),Fraction(4,5))]:
            s,c=iv.trig_range(a,b)
            for x in np.linspace(float(a)*math.pi,float(b)*math.pi,1001):
                self.assertLessEqual(s[0],math.sin(x));self.assertGreaterEqual(s[1],math.sin(x))
                self.assertLessEqual(c[0],math.cos(x));self.assertGreaterEqual(c[1],math.cos(x))
    def test_basic_operations_against_exact_rationals(self):
        rng=np.random.default_rng(33)
        for _ in range(250):
            aa=sorted(rng.normal(size=2)*100);bb=sorted(rng.normal(size=2)*100)
            for operation,exact in [(iv.add,lambda x,y:x+y),(iv.sub,lambda x,y:x-y),(iv.mul,lambda x,y:x*y)]:
                lo,hi=operation(tuple(aa),tuple(bb))
                for x in aa:
                    for y in bb:
                        z=exact(Fraction(float(x)),Fraction(float(y)))
                        self.assertLessEqual(Fraction(float(lo)),z)
                        self.assertGreaterEqual(Fraction(float(hi)),z)
    def test_corner_range_against_exact_rationals(self):
        a=np.array([1.234,-.45]);b=np.array([-2.7,.839])
        lo,hi=iv._corner_interval(a,b,Fraction(3,16),Fraction(13,16))
        for s in [Fraction(k,16) for k in range(3,14)]:
            for j in range(2):
                z=(1-s)*Fraction(float(a[j]))+s*Fraction(float(b[j]))
                self.assertLessEqual(Fraction(float(lo[j])),z)
                self.assertGreaterEqual(Fraction(float(hi[j])),z)
    def test_wedge_and_outer_rejection(self):
        ns=[((0.,0.),(1.,1.)),((1.,1.),(0.,0.))]
        c=(np.zeros(2),np.zeros(2))
        boxes=np.array([[.1,.2,.1,.2],[-.1,.1,-.1,.1],[.95,1.1,.5,.6]])
        np.testing.assert_equal(iv.interval_safe(boxes,c,ns),[True,False,False])
    def test_exact_connectivity_and_area(self):
        boxes=[[0,10,0,10],[1,11,10,20],[100,103,0,10]]
        ids,area=iv.largest_rectangle_component(boxes)
        self.assertEqual(ids,[0,1]);self.assertEqual(area,200)
        for bad in [[[0,10,0,10],[5,15,0,10]],[[0,10,0,10],[0,10,5,15]]]:
            with self.assertRaises(ValueError):iv.largest_rectangle_component(bad)
    def test_continuous_baseline(self):
        q=iv.GRID
        data={'format':'hallway-dyadic-rectangles-v1','grid_denominator':q,
            'bend_degrees':'90','mode':'forward','corner_hex':[['0x0.0p+0','0x0.0p+0']]*3,
            'boxes':[[-q//2,q//2,q//8,q//4],[-q//2,q//2,q//4,q//2]]}
        report=iv.verify(data,8)
        self.assertEqual(report['verified_rectangles'],2)
        self.assertEqual(Fraction(report['area_numerator'],report['area_denominator']),Fraction(3,8))
        data['boxes']=[[2*q,3*q,q//8,q//4]]
        self.assertEqual(iv.verify(data,3)['verified_rectangles'],0)
        data['grid_denominator']=1
        with self.assertRaises(ValueError):iv.verify(data)
    def test_depth_and_nonfinite_rejection(self):
        with self.assertRaises(ValueError):iv.verify({},31)
        with self.assertRaises(ArithmeticError):iv.mul((np.inf,np.inf),(1.,1.))

class FastGeometryTests(unittest.TestCase):
    def test_equivalence(self):
        for angle in (30,90,150):
            for mode in ('forward','reverse'):
                m=default_seed(math.radians(angle),mode,9)
                a=sampled_intersection(m,4);b=fast_intersection(m,4)
                self.assertLess(a.symmetric_difference(b).area,1e-11)
                _,a=enclose_swept(m,4);_,b=enclose_fast(m,4)
                self.assertLess(a.symmetric_difference(b).area,1e-11)
    def test_dense_audit(self):
        m=default_seed(math.pi/3,'forward',9)
        report,_=enclose_fast(m,16,True)
        self.assertLessEqual(report['inner_area'],report['sampled_area'])
        self.assertLess(report['audit_outside_area'],1e-12)

if __name__=='__main__':unittest.main()
