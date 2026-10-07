"""Exact scalar certification of a three-phase CONTACT-MODEL crossing.

This does NOT certify the unrestricted phase transition, nor forward-class
optimality or the geometry of the assumed contact pattern. It verifies the
specified analytic equation and signed-area crossing only.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from math import factorial
import argparse,json
from parameter_certificate import Interval as I,SCALE,sin_cos,pi_interval

ZERO=I.rational(0)

@dataclass(frozen=True)
class Jet:
    v:I
    db:I=ZERO
    dt:I=ZERO
    @staticmethod
    def cast(x):
        if isinstance(x,Jet):return x
        if isinstance(x,I):return Jet(x)
        return Jet(I.rational(F(x)))
    def __add__(self,x):
        x=self.cast(x);return Jet(self.v+x.v,self.db+x.db,self.dt+x.dt)
    __radd__=__add__
    def __neg__(self):return Jet(-self.v,-self.db,-self.dt)
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        x=self.cast(x);return Jet(self.v*x.v,self.db*x.v+self.v*x.db,self.dt*x.v+self.v*x.dt)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=self.cast(x);den=x.v.square()
        return Jet(self.v/x.v,(self.db*x.v-self.v*x.db)/den,(self.dt*x.v-self.v*x.dt)/den)
    def __rtruediv__(self,x):return self.cast(x)/self
    def square(self):return Jet(self.v.square(),2*self.v*self.db,2*self.v*self.dt)
    def sqrt(self):
        r=self.v.sqrt();return Jet(r,self.db/(2*r),self.dt/(2*r))


def reduced_sin_cos(x:I):
    """Reduce to |x/4|<=1 before Horner, then use two exact double angles.

    Direct fixed-precision degree-73 Horner coefficients at x around 2.4
    greatly magnify rounding intervals, even for point inputs. This changes
    neither the mathematical function nor the inherited remainder bound.
    """
    if max(abs(x.lo),abs(x.hi))>4*SCALE:
        raise ValueError('trigonometric reduction domain exceeded')
    s,c=sin_cos(x/4)
    for _ in range(2):
        s,c=2*s*c,c.square()-s.square()
    return s,c


def trig(x:Jet):
    s,c=reduced_sin_cos(x.v)
    return Jet(s,c*x.db,c*x.dt),Jet(c,-s*x.db,-s*x.dt)


def hyper_interval(x:I):
    if max(abs(x.lo),abs(x.hi))>4*SCALE:raise ValueError('hyperbolic Taylor domain exceeded')
    if not (F(81*4**75,factorial(75))<F(1,SCALE) and F(81*4**74,factorial(74))<F(1,SCALE)):
        raise ArithmeticError('unproved hyperbolic remainder')
    xx=x.square();ps=I.rational(1,factorial(73));pc=I.rational(1,factorial(72))
    for j in range(35,-1,-1):
        ps=ps*xx+I.rational(1,factorial(2*j+1));pc=pc*xx+I.rational(1,factorial(2*j))
    return x*ps+I(-1,1),pc+I(-1,1)


def hyper(x:Jet):
    s,c=hyper_interval(x.v)
    return Jet(s,c*x.db,c*x.dt),Jet(c,s*x.db,s*x.dt)


def model(beta:Jet,T:Jet,pi:I):
    q,d=trig(beta);s,c=trig(beta/2);st,ct=trig(T)
    mu=(3/(4*q.square())-1).sqrt();eta=((-1-2*d)/(1-2*d)).sqrt()
    sh,ch=hyper(mu*T);r=(1-2*d)/(2*(1+d)*mu);z0=-2*c/(1+2*d)
    B=-2*c/(3*mu*(ch+eta*sh));A=Jet.cast(F(1,3))
    residual=eta*(3*s*st-c*ct-1)+(sh/ch)*(s*st-3*c*ct-eta.square())
    zx=A*st+B*sh;zy=A*ct+r*B*ch+z0
    dx=A*ct+mu*B*ch;dy=-A*st+r*mu*B*sh
    alpha=beta/2-T;sa,ca=trig(alpha)
    p=(s*zx+c*zy+(1-ca)/2)/sa
    g=p*sa+ca/2;gp=p*ca-sa/2
    f=-s*zx+c*zy;fp=-s*dx+c*dy
    W=alpha/2-2*g*gp+p+2*T+2*c*(A*st+r*B*sh/mu+z0*T)-2*((1-d)*zx*dx+(1+d)*zy*dy)+2*(f+F(1,2))*fp
    e=Jet.cast(pi)-beta;qr,dr=trig(e)
    mr=2-dr;etar=(mr/(2+dr)).sqrt();Kr=e*(1+3/qr.square()).sqrt()/2
    skr,ckr=trig(Kr);R=etar*skr/(ckr+etar*skr)
    V=e/mr+(1+2*dr)/(4*qr)+3*dr.square()*R/(2*qr*mr.square())
    return residual,W-V,W,alpha


def interval(lo:F,hi:F):return I(I.rational(lo).lo,I.rational(hi).hi)

def at(beta:I,t:I,pi:I):return model(Jet(beta,I.rational(1),ZERO),Jet(t,ZERO,I.rational(1)),pi)


def isolate_t(beta:I,pi:I,steps:int=64):
    lo,hi=F(65,100),F(75,100)
    if at(beta,I.rational(lo),pi)[0].v.hi>=0 or at(beta,I.rational(hi),pi)[0].v.lo<=0:
        raise ArithmeticError('invalid T bracket')
    for _ in range(steps):
        mid=(lo+hi)/2;v=at(beta,I.rational(mid),pi)[0].v
        if v.hi<0:lo=mid
        elif v.lo>0:hi=mid
        else:
            # An ambiguous midpoint need not leave a wide old bisection
            # bracket. Interval Newton retains every root at every beta in
            # the input interval, with a derivative enclosure on that bracket.
            derivative=at(beta,interval(lo,hi),pi)[0].dt
            if derivative.lo<=0:
                raise ArithmeticError('cannot certify interval-Newton derivative')
            newton=I.rational(mid)-v/derivative
            lo=max(lo,F(newton.lo,SCALE));hi=min(hi,F(newton.hi,SCALE))
            if lo>hi:raise ArithmeticError('empty interval-Newton root enclosure')
            break
    return interval(lo,hi)


def prove_model(cells:int=256):
    if isinstance(cells,bool) or not isinstance(cells,int) or cells<1:
        raise ValueError('positive cell count required')
    pi=pi_interval();minimum_Ft=None;maximum_derivative=None;records=[]
    # First establish F_T > 0 on the entire contact-parameter rectangle.
    # This checks uniqueness of T before using the implicit derivative.
    for j in range(16):
        beta=pi*interval(F(135,180)+F(5*j,180*16),F(135,180)+F(5*(j+1),180*16))
        f0=at(beta,I.rational(65,100),pi)[0].v
        f1=at(beta,I.rational(75,100),pi)[0].v
        if f0.hi>=0 or f1.lo<=0:
            raise ArithmeticError(f'T bracket not certified in beta cell {j}')
        for k in range(16):
            t=interval(F(65,100)+F(k,160),F(65,100)+F(k+1,160))
            f=at(beta,t,pi)[0]
            if f.dt.lo<=0:
                raise ArithmeticError(f'no monotonic T proof at {j},{k}')
            minimum_Ft=f.dt.lo if minimum_Ft is None else min(minimum_Ft,f.dt.lo)
    # The area derivative is needed only along the now unique root branch,
    # not everywhere in a large off-root rectangle. Enclose that whole branch
    # by a verified interval tube for each beta cell.
    for j in range(cells):
        lo=F(135)+F(5*j,cells);hi=F(135)+F(5*(j+1),cells)
        beta=pi*interval(lo/180,hi/180)
        t=isolate_t(beta,pi)
        f,g,_,_=at(beta,t,pi)
        if f.dt.lo<=0:
            raise ArithmeticError(f'nonpositive interval denominator in tube {j}')
        along=g.db-g.dt*f.db/f.dt
        if along.hi>=0:
            raise ArithmeticError(f'no decreasing crossing proof in tube cell {j}')
        maximum_derivative=along.hi if maximum_derivative is None else max(maximum_derivative,along.hi)
        records.append(dict(beta_degrees=[str(lo),str(hi)],T=[t.lo,t.hi],derivative_upper=along.hi))
    endpoints=[]
    for deg,sign in [(F(136672184698,1000000000),1),(F(136672184699,1000000000),-1)]:
        beta=pi*I.rational(deg/180);t=isolate_t(beta,pi)
        f,g,w,a=at(beta,t,pi)
        if sign==1 and g.v.lo<=0:
            raise ArithmeticError('lower endpoint is not above reverse value')
        if sign==-1 and g.v.hi>=0:
            raise ArithmeticError('upper endpoint is not below reverse value')
        endpoints.append(dict(bend_degrees=str(deg),T=[t.lo,t.hi],gap=[g.v.lo,g.v.hi],area=[w.v.lo,w.v.hi],alpha=[a.v.lo,a.v.hi]))
    return dict(format='forward-contact-model-crossing-v1',status='unique scalar model crossing certified',
                warning='NOT a forward-class or unrestricted phase-transition theorem; contact geometry and optimality remain separate',
                beta_degrees_interval=['135','140'],T_interval=['13/20','3/4'],tube_cells=cells,
                monotonicity_grid=[16,16],denominator=SCALE,minimum_F_T=minimum_Ft,
                maximum_along_branch_derivative=maximum_derivative,tube_records=records,
                root_bend_degrees_interval=['136.672184698','136.672184699'],endpoint_records=endpoints)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cells',type=int,default=256);p.add_argument('--output')
    args=p.parse_args();text=json.dumps(prove_model(args.cells),indent=2)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:print(text,end='')
