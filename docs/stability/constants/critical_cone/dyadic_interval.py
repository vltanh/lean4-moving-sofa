"""Small outward-rounded interval arithmetic using integers only.

Every endpoint is an integer / 2**BITS. Arithmetic rounds outward. Sin/cos
use a Taylor polynomial at the midpoint plus an explicit Lagrange remainder
and the global Lipschitz bound 1. Pi is enclosed by Machin's identity with
alternating rational arctangent bounds. No binary floating-point acceptance
predicate and no external numerical package is used in certificates.
"""
from __future__ import annotations
from fractions import Fraction
from functools import lru_cache
from math import factorial
BITS=90
SCALE=1<<BITS


def floorq(q):return q.numerator//q.denominator


def ceilq(q):return -((-q.numerator)//q.denominator)


class Interval:
    __slots__=('lo','hi')
    def __init__(self,lo=0,hi=None,_raw=False):
        if _raw:self.lo,self.hi=lo,hi;return
        if isinstance(lo,Interval) and hi is None:self.lo,self.hi=lo.lo,lo.hi;return
        if hi is None:hi=lo
        self.lo=floorq(Fraction(lo)*SCALE);self.hi=ceilq(Fraction(hi)*SCALE)
        if self.lo>self.hi:raise ValueError('reversed interval')
    @classmethod
    def raw(cls,a,b):return cls(a,b,_raw=True)
    @property
    def a(self):return Interval.raw(self.lo,self.lo)
    @property
    def b(self):return Interval.raw(self.hi,self.hi)
    def __add__(self,o):
        o=Interval(o);return Interval.raw(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval.raw(-self.hi,-self.lo)
    def __sub__(self,o):return self+-Interval(o)
    def __rsub__(self,o):return Interval(o)+-self
    def __mul__(self,o):
        o=Interval(o);p=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return Interval.raw(min(p)//SCALE,-((-max(p))//SCALE))
    __rmul__=__mul__
    def reciprocal(self):
        if self.lo<=0<=self.hi:raise ZeroDivisionError(str(self))
        a=Fraction(SCALE*SCALE,self.hi);b=Fraction(SCALE*SCALE,self.lo)
        return Interval.raw(floorq(a),ceilq(b))
    def __truediv__(self,o):return self*Interval(o).reciprocal()
    def __rtruediv__(self,o):return Interval(o)*self.reciprocal()
    def __pow__(self,n):
        if not isinstance(n,int):raise TypeError('only integer powers')
        if n<0:return self.reciprocal()**(-n)
        if n==0:return Interval(1)
        if n==2:
            a=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
            b=max(self.lo*self.lo,self.hi*self.hi)
            return Interval.raw(a//SCALE,-((-b)//SCALE))
        if n%2:return self*self**(n-1)
        return (self**(n//2))**2
    def __abs__(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return Interval.raw(0,max(-self.lo,self.hi))
    def __lt__(self,o):return self.hi<Interval(o).lo
    def __le__(self,o):return self.hi<=Interval(o).lo
    def __gt__(self,o):return Interval(o)<self
    def __ge__(self,o):return Interval(o)<=self
    def __str__(self):return f'[{Fraction(self.lo,SCALE)}, {Fraction(self.hi,SCALE)}]'
    def exact(self):return {'lower_numerator':self.lo,'upper_numerator':self.hi,'denominator':SCALE}
    def approx(self):return [self.lo/SCALE,self.hi/SCALE]  # display only


@lru_cache(maxsize=65536)
def _trig(lo,hi,cosine):
    # Use 48th order; the remainder bound is valid without a sign or monotonicity assumption.
    mid=(lo+hi)//2;x=Interval.raw(mid,mid)
    # Recurrence avoids multiplying huge powers by rounded tiny factorial
    # coefficients, which causes valid but useless enclosures near pi.
    degree=0 if cosine else 1
    term=Interval(1) if cosine else x
    total=term
    xx=x*x
    while degree+2<=48:
        term=-(term*xx)/((degree+1)*(degree+2))
        total+=term
        degree+=2
    m=Fraction(abs(mid),SCALE)
    remainder=m**49/factorial(49)
    error=ceilq(remainder*SCALE)+max(mid-lo,hi-mid)
    return Interval.raw(max(-SCALE,total.lo-error),min(SCALE,total.hi+error))


def sin(x):x=Interval(x);return _trig(x.lo,x.hi,False)
def cos(x):x=Interval(x);return _trig(x.lo,x.hi,True)
def tan(x):return sin(x)/cos(x)


def atan_small_bounds(q,n):
    q=Fraction(q)
    s=sum(((-1)**j*q**(2*j+1)/Fraction(2*j+1) for j in range(n)),Fraction(0))
    nextterm=(-1)**n*q**(2*n+1)/Fraction(2*n+1)
    return Interval(min(s,s+nextterm),max(s,s+nextterm))


pi=16*atan_small_bounds(Fraction(1,5),80)-4*atan_small_bounds(Fraction(1,239),24)


class API:
    pi=pi
    dps='90-bit exact dyadic'
    sin=staticmethod(sin);cos=staticmethod(cos);tan=staticmethod(tan)
    @staticmethod
    def mpf(x=0):
        if isinstance(x,list):
            a,b=map(Interval,x);return Interval.raw(a.lo,b.hi)
        return Interval(x)
iv=API()
