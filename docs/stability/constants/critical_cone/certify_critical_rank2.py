"""Interval certificate for a rank-two CONTINUUM zero-slack relaxation.

The exact deficit, active-contact identities, and four-arc reconstruction
are analytic inputs. This is not a global sofa-entry certificate.
"""
from __future__ import annotations
from dataclasses import dataclass
from dyadic_interval import iv, Interval, SCALE
import json,time,hashlib
from fractions import Fraction
from pathlib import Path
Z=iv.mpf(0);ONE=iv.mpf(1)


def lower(x): return x.a


def upper(x): return x.b


def hull(a,b): return iv.mpf([a.a,b.b])


def imin(a,b):return iv.mpf([min(a.a,b.a),min(a.b,b.b)])


def imax(a,b):return iv.mpf([max(a.a,b.a),max(a.b,b.b)])


def positive_part_bound(x):return imax(x,Z)


def cot(x):return iv.cos(x)/iv.sin(x)


def sq(x):return x**2


def scalar_text(x):return str(x)


@dataclass
class Model:
    phi: object
    theta: object
    def __post_init__(self):
        self.v=iv.pi/2;self.T=iv.pi-self.phi;self.b=self.v-self.phi
        self.c=self.v-self.theta;self.d=self.v+self.theta
        self.A=ONE/iv.cos(self.phi)
        self.DB=iv.tan(self.c)-iv.tan(self.phi)
        self.DD=cot(self.T-self.d)-iv.tan(self.phi)
        assert self.DB.a>0 and self.DD.a>0
        self.P0=self.pieces('first',Z)
        self.Pp=self.pieces('first',self.phi)
        self.Pc=self.pieces('middle',self.c)
        self.Pd=self.pieces('last',self.d)
        self.PT=self.pieces('last',self.T)
        self.VB=self.scale(self.Pp,ONE/iv.cos(self.phi))+self.scale(self.Pc,-ONE/iv.cos(self.c))
        self.VD=self.scale(self.Pd,ONE/iv.sin(self.T-self.d))+self.scale(self.PT,-self.DD)
        self.G11=self.inner(self.VB,self.VB)
        self.G12=self.inner(self.VB,self.VD)
        self.G22=self.inner(self.VD,self.VD)
        self.S11=self.DB+self.G11;self.S22=self.DD+self.G22;self.S12=self.G12
        self.det=self.S11*self.S22-self.S12**2
        assert self.det.a>0
        self.w01=self.inner(self.P0,self.VB);self.w02=self.inner(self.P0,self.VD)
    def scale(self,P,a):return [(j,lo,hi,a*x,a*y) for j,lo,hi,x,y in P]
    def pieces(self,kind,t):
        p,v,b,T,A=self.phi,self.v,self.b,self.T,self.A
        C=iv.cos(t);S=iv.sin(t)
        if kind=='first':
            return [(0,t,p,C,Z),(1,p,b,C*A,Z),(2,b,v,C*A,Z),
                    (3,v,v+p,C*A*(A-iv.sin(p)),Z),(3,v+p,T,C*A*A,C*A)]
        if kind=='middle':
            return [(1,t,b,ONE,Z),(2,b,v,ONE,Z),
                    (3,v,v+t,A-S,Z),(3,v+t,T,A,ONE)]
        if kind=='third':return [(2,t,v,iv.sin(T-t),Z),(3,v,T,A*C*iv.sin(p),Z)]
        if kind=='last':return [(3,v,t,-S,Z)]
        raise ValueError(kind)
    def value(self,j,u,a,b):
        if j==0:return a/iv.cos(u)
        if j==1:return a
        if j==2:return a/iv.sin(self.T-u)
        return a/iv.sin(u)+b*cot(u)
    def cross(self,p,q):
        j,l1,h1,a,b=p;J,l2,h2,c,d=q
        if j!=J:return Z
        lo=imax(l1,l2);hi=imin(h1,h2)
        if hi.b<=lo.a:return Z
        if hi.a<lo.b:
            # Possible overlap; bound the whole range, including the empty case.
            U=iv.mpf([lo.a,hi.b]);prod=self.value(j,U,a,b)*self.value(j,U,c,d)
            length=hi.b-lo.a
            return iv.mpf([min(Z,prod.a*length),max(Z,prod.b*length)])
        if j==0:return a*c*(iv.tan(hi)-iv.tan(lo))
        if j==1:return a*c*(hi-lo)
        if j==2:return a*c*(cot(self.T-hi)-cot(self.T-lo))
        i0=cot(lo)-cot(hi)
        i1=ONE/iv.sin(lo)-ONE/iv.sin(hi)
        i2=i0-(hi-lo)
        return a*c*i0+(a*d+b*c)*i1+b*d*i2
    def inner(self,P,Q):return sum((self.cross(p,q) for p in P for q in Q),Z)
    def centered_norm(self,kind,t):
        A=self.A;C=iv.cos(t);S=iv.sin(t);p=self.phi
        if kind in ('first','end'):return A*A*C*C/2
        if kind=='middle':return A*C-A*A*C*C/2
        B=A*iv.sin(p)-A*A/2
        if kind=='third':return S*C+B*C*C
        if kind=='fourth_a':return -S*C+B*C*C
        if kind=='fourth_b':return -A*C-A*A*C*C/2
        raise ValueError(kind)
    def bound(self,kind,t):
        pk='last' if kind in ('fourth_a','fourth_b','end') else kind
        P=self.pieces(pk,t);ct=iv.cos(t)
        w1=self.inner(P,self.VB)-ct*self.w01/2
        w2=self.inner(P,self.VD)-ct*self.w02/2
        correction=(self.S22*w1**2-2*self.S12*w1*w2+self.S11*w2**2)/self.det
        correction=positive_part_bound(correction)
        D=self.centered_norm(kind,t)
        a1=(self.S22*w1-self.S12*w2)/self.det/iv.cos(self.c)
        a2=(self.S11*w2-self.S12*w1)/self.det/iv.sin(self.T-self.d)
        return 2*(D-correction), abs(a1)+abs(a2)
    def ranges(self):
        return [('first',Z,self.phi),('middle',self.phi,self.b),('third',self.b,self.v),
            ('fourth_a',self.v,self.v+self.phi),('fourth_b',self.v+self.phi,self.T),('end',self.T,iv.pi)]


def certify(C='0.98',max_depth=16):
    p=iv.mpf(['0.039177264','0.039177465']);th=iv.mpf(['0.681301409','0.681301610'])
    model=Model(p,th);C_exact=str(Fraction(C));C=iv.mpf(C);limit=C**2
    records=[];stack=[(kind,a,b,0,1,0) for kind,a,b in model.ranges()]
    visited=0;failed=[];worst=Z;start=time.time()
    while stack:
        kind,a,b,i,den,depth=stack.pop();visited+=1
        # t=a+u(b-a), with u in one exact dyadic interval, covers uncertain endpoints.
        u=iv.mpf([iv.mpf(i)/den,iv.mpf(i+1)/den]);t=a+u*(b-a)
        try:
            B,sensitivity=model.bound(kind,t)
        except ZeroDivisionError:
            # A broad trigonometric enclosure can contain zero even though
            # the analytic integration interval avoids it. Refine, never certify.
            B=sensitivity=iv.mpf([0,1000000])
        if B.b<limit.a and sensitivity.b<iv.mpf('0.5').a:
            worst=max(worst,B.b);records.append({'region':kind,'i':i,'denominator':den,'squared_bound':B.exact(),'slack_sensitivity_bound':sensitivity.exact()})
        elif depth>=max_depth:
            failed.append({'region':kind,'i':i,'denominator':den,'upper':scalar_text(B.b),'sensitivity':str(sensitivity)})
        else:
            stack.append((kind,a,b,2*i,2*den,depth+1));stack.append((kind,a,b,2*i+1,2*den,depth+1))
        if visited%1000==0:print('progress',visited,len(stack),len(failed),flush=True)
    return {'status':'passed' if not failed else 'inconclusive','coefficient':C_exact,'slack_sensitivity':'1/2',
        'phi_interval':['0.039177264','0.039177465'],'theta_interval':['0.681301409','0.681301610'],
        'arithmetic':'exact integers with 90-bit dyadic outward rounding','scale':SCALE,'visited':visited,'leaves':len(records),'worst_squared_upper':scalar_text(worst),
        'failed':failed,'seconds':time.time()-start,'leaf_certificate':records,
        'matrix':{s:str(getattr(model,s)) for s in ['DB','DD','G11','G12','G22','det']},
        'source_hashes':{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                         for name in ['certify_critical_rank2.py','dyadic_interval.py']},
        'scope':'continuum rank-two norm and slack sensitivity; analytic identities are inputs',
        'not_claimed':['global original-sofa entry','sharp feasible-Q constant','Lean verification']}
if __name__=='__main__':
 r=certify();Path(__file__).with_name('critical_rank2_certificate.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='leaf_certificate'},indent=2))
