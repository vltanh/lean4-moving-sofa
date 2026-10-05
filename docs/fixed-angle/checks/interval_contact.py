"""Outward-rounded intervals and interval-AD for contact-root verification.

Assumes IEEE-754 binary64 correctly rounded basic operations, as used by
Python on supported platforms. Trigonometric enclosures use Taylor
polynomials, not the platform sin/cos functions. No CI or Lean invocation.
"""
import math
import sys
from fractions import Fraction
from contact_core import events

if (sys.float_info.radix, sys.float_info.mant_dig, sys.float_info.max_exp) != (2,53,1024):
    raise RuntimeError("This verifier requires IEEE-754 binary64 floats.")
if (2.0**-1022)*(2.0**-52) != math.nextafter(0.0,1.0):
    raise RuntimeError("Subnormal arithmetic does not match the verifier assumptions.")

MINF=float('-inf'); PINF=float('inf')
def down(x): return math.nextafter(x,MINF)
def up(x): return math.nextafter(x,PINF)
class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi; return
        self.lo=float(lo); self.hi=float(lo if hi is None else hi)
        if not(math.isfinite(self.lo) and math.isfinite(self.hi) and self.lo<=self.hi):
            raise ArithmeticError(('invalid interval',self.lo,self.hi))
    @staticmethod
    def exact_rational(n,d=1):
        r=Fraction(n,d); f=float(r); q=Fraction.from_float(f)
        return I(down(f) if q>r else f,up(f) if q<r else f)
    def __add__(a,b):
        if isinstance(b,AD): return b+a
        b=I(b); return I(down(a.lo+b.lo),up(a.hi+b.hi))
    __radd__=__add__
    def __neg__(a): return I(-a.hi,-a.lo)
    def __sub__(a,b): return a+-b if isinstance(b,(I,AD)) else a+(-float(b))
    def __rsub__(a,b): return -a+b
    def __mul__(a,b):
        if isinstance(b,AD): return b*a
        b=I(b); v=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi)
        return I(down(min(v)),up(max(v)))
    __rmul__=__mul__
    def __truediv__(a,b):
        if isinstance(b,AD): return AD(a)/b
        b=I(b)
        if b.lo<=0<=b.hi: raise ArithmeticError(('division through zero',b))
        return a*I(down(1/b.hi),up(1/b.lo))
    def __rtruediv__(a,b): return I(b)/a
    def __repr__(a): return f'[{a.lo:.17g},{a.hi:.17g}]'
    def mag(a): return max(abs(a.lo),abs(a.hi))
    def sin(a): return trig_range(a,True)
    def cos(a): return trig_range(a,False)
    def hull(a,b): return I(min(a.lo,b.lo),max(a.hi,b.hi))

# The alternating arctangent series gives a reproducible enclosure for pi.
def atan_small(q):
    z=I.exact_rational(1,q); z2=z*z; term=z; total=I(0)
    for j in range(80):
        total=total+term/(2*j+1) if j%2==0 else total-term/(2*j+1)
        term=term*z2
    tail=term.mag()/161
    return total+I(-up(tail),up(tail))

def trig_point(x,sine):
    if abs(x)>2: raise ArithmeticError('Taylor argument outside [-2,2]')
    z=I(x); zz=z*z; coeff=SIN_COEF if sine else COS_COEF
    ans=coeff[-1]
    for co in reversed(coeff[:-1]): ans=ans*zz+co
    if sine: ans=ans*z
    return ans+TAIL

def trig_range(z,sine):
    out=trig_point(z.lo,sine).hull(trig_point(z.hi,sine))
    if sine:
        if z.lo<=HALF_PI.hi and z.hi>=HALF_PI.lo: out=out.hull(I(1))
        if z.lo<=-HALF_PI.lo and z.hi>=-HALF_PI.hi: out=out.hull(I(-1))
    elif z.lo<=0<=z.hi: out=out.hull(I(1))
    return out

class AD:
    __slots__=('val','grad')
    def __init__(self,val,grad=None):
        if isinstance(val,AD): self.val,self.grad=val.val,val.grad; return
        self.val=I(val); self.grad=tuple(I(0) for _ in range(4)) if grad is None else tuple(I(t) for t in grad)
    def __add__(a,b):
        b=AD(b); return AD(a.val+b.val,[x+y for x,y in zip(a.grad,b.grad)])
    __radd__=__add__
    def __neg__(a): return AD(-a.val,[-x for x in a.grad])
    def __sub__(a,b): return a+-AD(b)
    def __rsub__(a,b): return AD(b)+-a
    def __mul__(a,b):
        b=AD(b); return AD(a.val*b.val,[x*b.val+a.val*y for x,y in zip(a.grad,b.grad)])
    __rmul__=__mul__
    def __truediv__(a,b):
        b=AD(b); return AD(a.val/b.val,[(x-(a.val/b.val)*y)/b.val for x,y in zip(a.grad,b.grad)])
    def __rtruediv__(a,b): return AD(b)/a
    def sin(a): return AD(a.val.sin(),[a.val.cos()*x for x in a.grad])
    def cos(a): return AD(a.val.cos(),[-a.val.sin()*x for x in a.grad])

PI=16*atan_small(5)-4*atan_small(239)
HALF_PI=PI/2
SIN_COEF=[I.exact_rational((-1)**j,math.factorial(2*j+1)) for j in range(16)]
COS_COEF=[I.exact_rational((-1)**j,math.factorial(2*j)) for j in range(16)]
if not (2**(33+65)<math.factorial(33) and 2**(32+65)<math.factorial(32)):
    raise ArithmeticError("Taylor remainder bound failed.")
TAIL=I(-(2.0**-65),2.0**-65) # larger than both remainders for |x|<=2

def all_orders(w,x,limit=64):
    ev=events(w,*x); keys=list(ev)
    preds={k:{j for j in keys if ev[j].hi<ev[k].lo} for k in keys}
    forced=[('0','a'),('a','b'),('b','c'),('c','w'),('0','dc'),('dc','db'),('db','za'),('za','w'),('0','m'),('m','w'),('a','m'),('m','za')]
    for lo,hi in forced: preds[hi].add(lo)
    out=[]
    def rec(order,left):
        if len(out)>limit: raise ArithmeticError('too many event orders')
        if not left: out.append(order);return
        for k in sorted(left):
            if not (preds[k]&left): rec(order+[k],left-{k})
    rec([],set(keys))
    # Event pairs are exact reflections about w/2.  Non-symmetric orders
    # have no open parameter region and cannot be actual propagations.
    mirror={'0':'w','w':'0','a':'za','za':'a','b':'db','db':'b',
            'c':'dc','dc':'c','m':'m'}
    out=[o for o in out if o==[mirror[k] for k in reversed(o)]]
    if not out: raise ArithmeticError('no admissible event ordering')
    return out

