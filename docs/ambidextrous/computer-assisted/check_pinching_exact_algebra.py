#!/usr/bin/env python3
"""Exact Q(sqrt(2)) algebra checks for PM1 pinching nonconcavity.

The pen-and-paper theorem proves the sign for sufficiently small epsilon.
This program verifies all displayed algebraic/rational constants exactly;
no angle mesh, floating quadrature, optimizer, Lean, or CI is used.
"""
from dataclasses import dataclass
from fractions import Fraction as F

@dataclass(frozen=True)
class Q2:
    a: F
    b: F = F(0)
    def __add__(self, other):
        y = to_q2(other)
        return Q2(self.a+y.a, self.b+y.b)
    __radd__ = __add__
    def __neg__(self):
        return Q2(-self.a,-self.b)
    def __sub__(self, other):
        return self+-to_q2(other)
    def __rsub__(self, other):
        return to_q2(other)+-self
    def __mul__(self, other):
        y = to_q2(other)
        return Q2(self.a*y.a+2*self.b*y.b,self.a*y.b+self.b*y.a)
    __rmul__ = __mul__
    def __truediv__(self, other):
        y=to_q2(other)
        norm=y.a*y.a-2*y.b*y.b
        assert norm!=0
        return self*Q2(y.a/norm,-y.b/norm)

def to_q2(x):
    return x if isinstance(x,Q2) else Q2(F(x))

s=Q2(F(0),F(1))
W=F(12,5)
kappa=2-s
rc=(F(17,10)-s)/kappa
assert rc==F(7,10)-F(3,20)*s
ac=F(6,5)-rc
dc=1-rc
assert 2*ac-s*dc==Q2(F(7,10))
assert 4*ac-s*dc==Q2(F(17,10),F(3,10))
H=lambda r: F(11,5)-s-(2-s)*r
assert H(rc)==Q2(F(1,2))
assert H(rc-F(1,1000))==F(1,2)+F(1,1000)*kappa
# Rational enclosures used for the exact near-mid-angle derivative bounds.
assert F(7,5)**2<2<(F(10,7)**2)
assert F(17,35)>F(12,25)
assert F(49,100)<F(1,2)
# Under r in [12/25,1/2], and |t-pi/4| <= 1/20:
# sin(2t) >= 199/200 and sin(t)+cos(t) <= 3/2.
x_upper=-2*F(7,10)*F(199,200)+F(13,25)*F(3,2)
y_second_upper=4*F(18,25)+F(13,25)*F(3,2)
assert x_upper==-F(613,1000)<-F(1,2)
assert y_second_upper==F(183,50)<4
print('PASS: critical radius, H(rc)=1/2, beta_c=7/10, gamma_c=(17+3sqrt2)/10')
print('PASS: exact uniform derivatives', x_upper, y_second_upper)
print('PASS: rational bracket', F(12,25), '< rc <', F(1,2))
print('Analytic consequence: pinch >= (2-sqrt2)^(3/2)*epsilon^(3/2)/2')
