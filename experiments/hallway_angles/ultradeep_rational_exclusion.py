"""512-bit exact rational-angle exclusion for the contact-model crossing.

Standalone exact-integer interval arithmetic. No floating point, optimizer,
NumPy, SciPy, Shapely, or platform trig is used in the proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt
import json

BITS=512
SCALE=1<<BITS

def ceil_div(a,b): return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    def __post_init__(self):
        if self.lo>self.hi: raise ValueError("reversed interval")
    @classmethod
    def rational(cls,x):
        q=Fraction(x)
        return cls(q.numerator*SCALE//q.denominator,
                   ceil_div(q.numerator*SCALE,q.denominator))
    @staticmethod
    def coerce(x):
        if isinstance(x,I): return x
        return I.rational(x)
    def __add__(self,o):
        o=I.coerce(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-I.coerce(o))
    def __rsub__(self,o): return I.coerce(o)+(-self)
    def __mul__(self,o):
        o=I.coerce(o)
        p=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(p)//SCALE,ceil_div(max(p),SCALE))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I.coerce(o)
        if o.lo<=0<=o.hi: raise ZeroDivisionError
        nums=(self.lo*SCALE,self.hi*SCALE)
        floors=[n//d for n in nums for d in (o.lo,o.hi)]
        ceils=[ceil_div(n,d) for n in nums for d in (o.lo,o.hi)]
        return I(min(floors),max(ceils))
    def __rtruediv__(self,o): return I.coerce(o)/self
    def square(self):
        lo=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        hi=max(self.lo*self.lo,self.hi*self.hi)
        return I(lo//SCALE,ceil_div(hi,SCALE))
    def sqrt(self):
        if self.lo<0: raise ValueError("negative sqrt")
        lo=isqrt(self.lo*SCALE); hi=isqrt(self.hi*SCALE)
        if hi*hi<self.hi*SCALE: hi+=1
        return I(lo,hi)

def atan_bounds(n,terms=400):
    s=sum((Fraction((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(terms)),Fraction())
    t=Fraction((-1)**terms,(2*terms+1)*n**(2*terms+1))
    return min(s,s+t),max(s,s+t)

def pi_interval():
    a0,a1=atan_bounds(5); b0,b1=atan_bounds(239)
    lo,hi=16*a0-4*b1,16*a1-4*b0
    return I(I.rational(lo).lo,I.rational(hi).hi)

def sincos_small(x,n=110):
    if max(abs(x.lo),abs(x.hi))>SCALE: raise ValueError("small trig domain")
    if Fraction(1,factorial(2*n+2))>=Fraction(1,SCALE):
        raise ArithmeticError("Taylor remainder too large")
    xx=x.square()
    ps=I.rational(Fraction((-1)**n,factorial(2*n+1)))
    pc=I.rational(Fraction((-1)**n,factorial(2*n)))
    for j in range(n-1,-1,-1):
        ps=ps*xx+I.rational(Fraction((-1)**j,factorial(2*j+1)))
        pc=pc*xx+I.rational(Fraction((-1)**j,factorial(2*j)))
    return x*ps+I(-1,1),pc+I(-1,1)

def sincos(x):
    if max(abs(x.lo),abs(x.hi))>4*SCALE: raise ValueError("trig domain")
    s,c=sincos_small(x/4)
    for _ in range(2):
        s,c=2*s*c,c.square()-s.square()
    return s,c

def sinhcosh(x,n=110):
    if max(abs(x.lo),abs(x.hi))>SCALE: raise ValueError("hyperbolic domain")
    xx=x.square()
    ps=I.rational(Fraction(1,factorial(2*n+1)))
    pc=I.rational(Fraction(1,factorial(2*n)))
    for j in range(n-1,-1,-1):
        ps=ps*xx+I.rational(Fraction(1,factorial(2*j+1)))
        pc=pc*xx+I.rational(Fraction(1,factorial(2*j)))
    return x*ps+I(-1,1),pc+I(-1,1)

def residual_and_dt(beta,T):
    q,d=sincos(beta); s,c=sincos(beta/2); st,ct=sincos(T)
    mu=(3/(4*q.square())-1).sqrt()
    eta=((-1-2*d)/(1-2*d)).sqrt()
    sh,ch=sinhcosh(mu*T); h=sh/ch
    A=3*s*st-c*ct-1
    B=s*st-3*c*ct-eta.square()
    F=eta*A+h*B
    Ft=eta*(3*s*ct+c*st)+(mu/ch.square())*B+h*(s*ct+3*c*st)
    return F,Ft

def model_gap(beta,T,pi):
    q,d=sincos(beta); s,c=sincos(beta/2); st,ct=sincos(T)
    mu=(3/(4*q.square())-1).sqrt(); eta=((-1-2*d)/(1-2*d)).sqrt()
    sh,ch=sinhcosh(mu*T); r=(1-2*d)/(2*(1+d)*mu); z0=-2*c/(1+2*d)
    B=-2*c/(3*mu*(ch+eta*sh)); A=I.rational(Fraction(1,3))
    zx,zy=A*st+B*sh,A*ct+r*B*ch+z0
    dx,dy=A*ct+mu*B*ch,-A*st+r*mu*B*sh
    alpha=beta/2-T; sa,ca=sincos(alpha)
    p=(s*zx+c*zy+(1-ca)/2)/sa
    g,gp=p*sa+ca/2,p*ca-sa/2
    f,fp=-s*zx+c*zy,-s*dx+c*dy
    W=(alpha/2-2*g*gp+p+2*T
       +2*c*(A*st+r*B*sh/mu+z0*T)
       -2*((1-d)*zx*dx+(1+d)*zy*dy)+2*(f+Fraction(1,2))*fp)
    e=pi-beta; qr,dr=sincos(e); m=2-dr
    er=(m/(2+dr)).sqrt(); K=e*(1+3/qr.square()).sqrt()/2
    sk,ck=sincos(K); R=er*sk/(ck+er*sk)
    V=e/m+(1+2*dr)/(4*qr)+3*dr.square()*R/(2*qr*m.square())
    return W-V

def interval(lo,hi):
    return I(I.rational(lo).lo,I.rational(hi).hi)

def isolate_T(beta):
    lo,hi=Fraction(65,100),Fraction(75,100)
    for _ in range(100):
        mid=(lo+hi)/2
        m=I.rational(mid)
        F,_=residual_and_dt(beta,m)
        bracket=interval(lo,hi)
        _,D=residual_and_dt(beta,bracket)
        if D.lo<=0: raise ArithmeticError("nonpositive Newton derivative")
        N=m-F/D
        nl=max(lo,Fraction(N.lo,SCALE)); nh=min(hi,Fraction(N.hi,SCALE))
        if not nl<nh: raise ArithmeticError("empty Newton interval")
        if nh-nl>=Fraction(9,10)*(hi-lo):
            if F.hi<0: nl=mid
            elif F.lo>0: nh=mid
            else: raise ArithmeticError("Newton stalled")
        lo,hi=nl,nh
        if hi-lo<Fraction(1,1<<500): break
    return interval(lo,hi)

PI=pi_interval()

LOWER=Fraction(
91134299355359730620075344463050084054257690016349718007751311644708802731,
120025694476154505239302526413929185366049268162850319859865885681419706546)

UPPER=Fraction(
709773526022809658397345482386942267278154400754731831515505447771213258,
934785925653429083453531927915416097528921388773413797802167515325735257)

def gap_at_ratio(r):
    beta=PI*I.rational(r)
    T=isolate_T(beta)
    g=model_gap(beta,T,PI)
    return Fraction(g.lo,SCALE),Fraction(g.hi,SCALE)

def prove():
    gl=gap_at_ratio(LOWER); gu=gap_at_ratio(UPPER)
    if gl[0]<=0 or gu[1]>=0:
        raise ArithmeticError("endpoint gap signs not certified")
    det=UPPER.numerator*LOWER.denominator-LOWER.numerator*UPPER.denominator
    if det!=1: raise ArithmeticError("not Farey neighbours")
    bound=LOWER.denominator+UPPER.denominator
    return {
      "format":"ultradeep-rational-exclusion-v1",
      "precision_bits":BITS,
      "lower":str(LOWER),"upper":str(UPPER),
      "lower_gap":[str(x) for x in gl],"upper_gap":[str(x) for x in gu],
      "farey_determinant":det,
      "minimum_denominator":bound,
      "conclusion":f"if beta_model/pi=p/q in lowest terms then q>={bound}",
      "scope":"analytic contact-model crossing only; not the unrestricted global transition"
    }

if __name__=="__main__":
    print(json.dumps(prove(),indent=2))
