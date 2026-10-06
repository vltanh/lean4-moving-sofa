"""Small outward dyadic interval implementation used by the kernel checker.

Standard library only. Trig is Taylor-enclosed after exact argument reduction.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial,isqrt
from functools import lru_cache
BITS=128
S=1<<BITS


def ceildiv(a,b):return -((-a)//b)


@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError('reversed interval')
    @staticmethod
    def cast(x):
        if isinstance(x,I):return x
        x=F(x);return I(x.numerator*S//x.denominator,ceildiv(x.numerator*S,x.denominator))
    def __add__(self,x):
        x=I.cast(x);return I(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,x):return self+-I.cast(x)
    def __rsub__(self,x):return I.cast(x)+-self
    def __mul__(self,x):
        x=I.cast(x);v=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
        return I(min(v)//S,ceildiv(max(v),S))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=I.cast(x)
        if x.lo<=0<=x.hi:raise ZeroDivisionError('interval denominator contains zero')
        return I(min(n*S//d for n in [self.lo,self.hi] for d in [x.lo,x.hi]),max(ceildiv(n*S,d) for n in [self.lo,self.hi] for d in [x.lo,x.hi]))
    def __rtruediv__(self,x):return I.cast(x)/self
    def square(self):
        lo=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        return I(lo//S,ceildiv(max(self.lo*self.lo,self.hi*self.hi),S))
    def sqrt(self):
        if self.lo<0:raise ValueError('negative radicand')
        lo=isqrt(self.lo*S);hi=isqrt(self.hi*S)
        return I(lo,hi+(hi*hi<self.hi*S))
    def upper(self):return F(self.hi,S)
    def lower(self):return F(self.lo,S)


SIN_COEFF=[I.cast(F((-1)**j,factorial(2*j+1))) for j in range(21)]
COS_COEFF=[I.cast(F((-1)**j,factorial(2*j))) for j in range(21)]
if F(1,factorial(42))>=F(1,S):raise ArithmeticError('insufficient Taylor degree')


def trig_interval(x):
    x=I.cast(x)
    if max(abs(x.lo),abs(x.hi))>4*S:raise ValueError('trig domain [-4,4] required')
    z=x/4;zz=z.square();p=SIN_COEFF[-1];q=COS_COEFF[-1]
    for j in range(19,-1,-1):p=p*zz+SIN_COEFF[j];q=q*zz+COS_COEFF[j]
    si=z*p+I(-1,1);co=q+I(-1,1)
    for _ in range(2):si,co=2*si*co,co.square()-si.square()
    return si,co


@lru_cache(maxsize=200000)
def trig(x):return trig_interval(I.cast(F(x)))


def pi_interval():
    def atan(n):
        p=sum((F((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(100)),F(0))
        r=F(1,201*n**201)
        return I(I.cast(p).lo,I.cast(p+r).hi)
    return 16*atan(5)-4*atan(239)
