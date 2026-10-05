from fractions import Fraction
import unittest
from class_exclusion import class_upper

class ClassBoundTests(unittest.TestCase):
    def test_right_angle(self):
        f=class_upper('90','forward');r=class_upper('90','reverse')
        self.assertGreaterEqual(f*f,8);self.assertLess(f,Fraction(283,100))
        self.assertGreaterEqual(r*r,2);self.assertLess(r,Fraction(142,100))
    def test_exclusion_comparisons(self):
        for angle,mode,lower in [('30','reverse','5.323809'),('60','reverse','2.892784'),
                                 ('90','reverse','2.217848'),('150','forward','2.637591')]:
            self.assertLess(class_upper(angle,mode),Fraction(lower))
        self.assertGreater(class_upper('120','reverse'),Fraction('1.948399'))
    def test_invalid_inputs(self):
        for degrees,mode in [('0','forward'),('180','reverse'),('90','unknown')]:
            with self.assertRaises(ValueError):class_upper(degrees,mode)

if __name__=='__main__':unittest.main()
