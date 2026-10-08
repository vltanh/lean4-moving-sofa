"""Rigorous integer/rational upper area for full-turn sofa hulls near Romik's reference.

All support constants are enclosed by exact scaled-interval radical arithmetic.
Finite-angle outer/inner wall bounds are evaluated on a horizontal cell grid
with directed integer division. This proves a *local* statement only.

Usage: python certified_near_reference_165.py [512] [cells] [radius_in_1e12_units]
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
import sys, time, json, hashlib
import numpy as np

P = 10**12

def fl(a,b):return a//b

def ce(a,b):return -((-a)//b)

@dataclass(frozen=True)
class Iv:
    lo:int; hi:int
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError('inverted interval')
    @staticmethod
    def q(a,b=1):
        return Iv(fl(a*P,b),ce(a*P,b))
    def __add__(self,o):
        if not isinstance(o,Iv):o=Iv.q(o)
        return Iv(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Iv(-self.hi,-self.lo)
    def __sub__(self,o):return self+(-o if isinstance(o,Iv) else Iv.q(-o))
    def __rsub__(self,o):return Iv.q(o)-self
    def __mul__(self,o):
        if not isinstance(o,Iv):o=Iv.q(o)
        prods=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return Iv(fl(min(prods),P),ce(max(prods),P))
    __rmul__=__mul__
    def __truediv__(self,o):
        if not isinstance(o,Iv):o=Iv.q(o)
        if o.lo<=0<=o.hi:raise ValueError('zero in divisor')
        vals=[F(a*P,b) for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return Iv(min(v.numerator//v.denominator for v in vals),max(ce(v.numerator,v.denominator) for v in vals))
    def sqrt(self):
        if self.lo<0:raise ValueError('sqrt negative')
        a=isqrt(self.lo*P);b=isqrt(self.hi*P)
        return Iv(a,b+(b*b<self.hi*P))
    def aslist(self):return [self.lo,self.hi]


def support_samples(n):
    # Isolate the positive zero of 4Y^3+3Y-1 exactly.
    y0,y1=F(298035818991,10**12),F(298035818993,10**12)
    f=lambda y:4*y*y*y+3*y-1
    assert f(y0)<0<f(y1)
    Y=Iv(int(y0*P),int(y1*P)); one=Iv.q(1);two=Iv.q(2)
    sb=(one+Y*Y).sqrt()
    m=sb/(3*Y)
    cb=one/sb; sbeta=Y/sb
    cb2=((one+cb)/2).sqrt();sb2=((one-cb)/2).sqrt()
    sinpi8=((two-two.sqrt()).sqrt())/2
    cospi8=((two+two.sqrt()).sqrt())/2
    cos3b2=cb*cb2-sbeta*sb2
    sin3b2=sbeta*cb2+cb*sb2
    cost=sinpi8*cos3b2+cospi8*sin3b2
    R=cb/cost
    assert 1167000000000 <m.lo <= m.hi< 1170000000000
    print('m interval, R interval (scaled 1e12):',m.aslist(),R.aslist(),flush=True)
    rows=[]
    for j in range(1,n):
        d=n*n+j*j; cn=n*n-j*j; sn=2*n*j
        c=Iv.q(cn,d);s=Iv.q(sn,d)
        tangent=F(sn,cn)
        if tangent < y0:
            fs=m*c+s/2
            gs=m*s/2+c/2+Iv.q(1,2)
            mode=0
        elif tangent>1/y0:
            fs=m*c/2+s/2+Iv.q(1,2)
            gs=m*s+c/2
            mode=2
        elif (tangent>y1 and tangent<1/y1):
            halfden=Iv.q(d).sqrt()
            ch=Iv.q(n)/halfden;sh=Iv.q(j)/halfden
            fs=R*(ch*cospi8-sh*sinpi8)+s/2
            gs=R*(sh*cospi8+ch*sinpi8)+c/2
            mode=1
        else:
            raise ValueError('mesh point too close to phase switch')
        rows.append((cn,sn,d,fs.lo,fs.hi,gs.lo,gs.hi,mode))
    return m,rows


def compute(n,N,radius):
    start=time.perf_counter();m,rows=support_samples(n)
    # Fix generous box [-117/100,117/100] and add axis support bound
    # |x|<=m_hi+radius, which tightens the finite integration range.
    Xlim=m.hi+radius
    # Use an exactly uniform integer grid; N divides 2*Xlim only rarely,
    # so cover [-Xlim,Xlim] by uniform rational grid with denominator N*P.
    # Instead use fixed box [-117/100,117/100] with integer-cell grid.
    xmin=-117*P//100; xmax=117*P//100
    assert m.hi+radius<xmax
    assert (xmax-xmin)%N==0
    dx=(xmax-xmin)//N
    Xleft=xmin+dx*np.arange(N,dtype=np.int64)
    Xright=Xleft+dx
    Umax=np.full(N,P,dtype=np.int64)
    nmin=np.zeros(N,dtype=np.int64)
    pad=P+radius
    for cn,sn,d,fl0,fh0,gl0,gh0,mode in rows:
        # All 64-bit products must be <2^63 throughout, checked by scalar bounds.
        assert max(abs((v+pad)*d) for v in (fh0,gh0))<2**62
        oa=np.floor_divide((fh0+radius)*d-cn*Xleft+sn-1,sn)
        ob=np.floor_divide((gh0+radius)*d+sn*Xright+cn-1,cn)
        Umax=np.minimum(Umax,np.minimum(oa,ob))
        na=np.floor_divide((fl0-radius-P)*d-cn*Xright,sn)
        nb=np.floor_divide((gl0-radius-P)*d+sn*Xleft,cn)
        nmin=np.maximum(nmin,np.minimum(na,nb))
    length=np.maximum(0,2*np.minimum(Umax,P-nmin)-P)
    numerator=int(np.sum(length,dtype=np.int64))*dx
    den=P*P
    answer=F(numerator,den)
    print(json.dumps({'n':n,'cells':N,'neighborhood_radius':f'{radius}/{P}',
        'conservative_area_upper':str(answer),'area_decimal':float(answer),
        'margin_below_33_20':str(F(33,20)-answer),'runtime_seconds':time.perf_counter()-start,
        'certified':answer<F(33,20),'min_max_roof':[int(Umax.min()),int(Umax.max())],
        'sum_slice_length_scaled':int(np.sum(length,dtype=np.int64))},indent=2))

if __name__=='__main__':
    n=int(sys.argv[1]) if len(sys.argv)>1 else 512
    N=int(sys.argv[2]) if len(sys.argv)>2 else 100000
    radius=int(sys.argv[3]) if len(sys.argv)>3 else 700000000
    compute(n,N,radius)
