"""Exact interval energy bound for the committed continuously feasible trial.

The support/containment proof is analytic (notes 23 and 25); this program
certifies its full six-residual energy, uniformly over the reference box.
There is no floating-point acceptance, optimizer, or Lean invocation here.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import time
from dyadic_interval import Interval as I, iv, SCALE

ZERO=I(0)
ONE=I(1)


def hull(xs):
    if not xs: raise ValueError('empty piece cover')
    return I.raw(min(x.lo for x in xs), max(x.hi for x in xs))


def sinc(w):
    """Taylor enclosure including w=0; degree ten with explicit remainder."""
    total=sum(((-1)**j*w**(2*j)/factorial(2*j+1) for j in range(6)), ZERO)
    error=abs(w).b**12/factorial(13)
    return total+I.raw(-error.hi,error.hi)


class Trial:
    def __init__(self, data):
        if data['subdivisions'] != 8: raise ValueError('expected seventeen Hermite nodes')
        self.p=I('0.039177264','0.039177465')
        self.th=I('0.681301409','0.681301610')
        self.v=iv.pi/2;self.c=self.v-self.th;self.b=self.v-self.p;self.T=iv.pi-self.p
        free=[I(F(s)) for s in data['free_coefficients']]
        if len(free)!=31: raise ValueError('wrong number of rational coefficients')
        self.q=free[0]
        self.node_keys=[(1-F(i,8),-F(i,8),F(i,16)) for i in range(9)]+[
            (F(0),-1+F(j,8),F(1,2)) for j in range(1,9)]
        self.nodes=[self.at(k) for k in self.node_keys]
        gp=-iv.cos(self.p)+self.q*iv.sin(self.p)
        dp=iv.sin(self.p)+self.q*iv.cos(self.p)
        self.y=[gp]+free[1:16]+[ZERO]
        self.d=[ZERO]*17;self.d[0]=dp
        for k,s in zip([*range(1,8),*range(9,17)],free[16:]):self.d[k]=s
        self.d[8]=(self.y[8]*iv.cos(self.c-self.p)-gp)/iv.sin(self.c-self.p)
        self.coeffs=[]
        for j in range(16):
            h=self.nodes[j+1]-self.nodes[j]
            if h.lo<=0:raise AssertionError('node separation not certified')
            y0,y1=self.y[j:j+2];d0,d1=self.d[j:j+2]
            self.coeffs.append((y0,h*d0,3*(y1-y0)-h*(2*d0+d1),2*(y0-y1)+h*(d0+d1)))
        h=self.nodes[-1]-self.nodes[-2]
        a,b,c,d=self.coeffs[-1]
        self.last_a=(c+3*d)/h**2
        self.last_b=-d/h**3
    def at(self,key):
        a,b,c=key
        return I(a)*self.p+I(b)*self.th+I(c)*iv.pi
    def eval(self,t):
        values=[];derivs=[]
        if t.lo<=self.p.hi:
            s=I.raw(t.lo,min(t.hi,self.p.hi))
            values.append(-iv.cos(s)+self.q*iv.sin(s))
            derivs.append(iv.sin(s)+self.q*iv.cos(s))
        for j,(a,b,c,d) in enumerate(self.coeffs):
            lo=max(t.lo,self.nodes[j].lo);hi=min(t.hi,self.nodes[j+1].hi)
            if lo>hi:continue
            h=self.nodes[j+1]-self.nodes[j]
            z=(I.raw(lo,hi)-self.nodes[j])/h
            values.append(a+z*(b+z*(c+z*d)))
            derivs.append((b+z*(2*c+3*z*d))/h)
        return hull(values),hull(derivs)
    def residual(self,kind,t):
        g,dg=self.eval(t)
        if kind=='r2':return self.eval(self.v-t)[0]-dg
        if kind=='r3':return (self.y[0]-g*iv.cos(self.T-t))/iv.sin(self.T-t)-dg
        if kind=='r4':return dg-(iv.cos(t)*g+1)/iv.sin(t)
        if kind=='B':
            if t.lo>=self.nodes[-2].hi:
                w=self.v-t
                # g(v-w)=w*(-d_v+alpha*w+beta*w^2). Avoid 0/0 at v.
                return iv.cos(w)*(-self.d[-1]+self.last_a*w+self.last_b*w**2)/sinc(w)+dg
            return iv.tan(t)*g+dg
        if kind=='D':return dg+(self.y[0]-g*iv.cos(t-self.p))/iv.sin(t-self.p)
        raise ValueError(kind)
    def cuts(self,kind):
        pkey=(F(1),F(0),F(0));vkey=(F(0),F(0),F(1,2))
        bkey=(-F(1),F(0),F(1,2));ckey=(F(0),-F(1),F(1,2))
        lo,hi={'r2':(pkey,bkey),'r3':(bkey,vkey),'r4':(pkey,vkey),
               'B':(ckey,vkey),'D':(ckey,vkey)}[kind]
        keys=set(self.node_keys+[lo,hi])
        if kind=='r2':keys.update((-a,-b,F(1,2)-c) for a,b,c in self.node_keys)
        # Sorting is not acceptance: every retained adjacent ordering is proved below.
        mid=lambda key:(self.at(key).lo+self.at(key).hi)
        keys=sorted([k for k in keys if mid(lo)<=mid(k)<=mid(hi)],key=mid)
        if keys[0]!=lo or keys[-1]!=hi:raise AssertionError('wrong arc endpoints')
        for a,b in zip(keys,keys[1:]):
            if not self.at(a)<self.at(b):raise AssertionError('uncertified breakpoint order')
        return keys
    def energy(self,n):
        components={'r1':self.q**2*iv.tan(self.p)};cells=0
        for kind in ['r2','r3','r4','B','D']:
            keys=self.cuts(kind);total=ZERO
            for a,b in zip(keys,keys[1:]):
                lo=self.at(a);length=self.at(b)-lo
                for j in range(n):
                    t=lo+I(F(j,n),F(j+1,n))*length
                    total+=self.residual(kind,t)**2*(length/n)
                    cells+=1
            components[kind]=total
        db=iv.tan(self.c)-iv.tan(self.p)
        components['B_gap']=(self.y[0]/iv.cos(self.p)-self.y[8]/iv.cos(self.c))**2/db
        return sum(components.values(),ZERO)/2,components,cells


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--subcells',type=int,default=512)
    ap.add_argument('--output',type=Path,default=Path('feasible-trial-certificate.json'))
    a=ap.parse_args()
    if a.subcells<=0:raise ValueError('subcells must be positive')
    path=Path(__file__).with_name('feasible-trial-data.json')
    data=json.loads(path.read_text());t0=time.time();model=Trial(data)
    energy,components,cells=model.energy(a.subcells)
    cap=F(147,125);lower=F(461,500)
    accepted=energy.b<I(cap) and lower**2*cap<1
    result={'status':'passed' if accepted else 'inconclusive',
        'energy_enclosure':energy.exact(),'energy_display':energy.approx(),
        'strict_energy_upper':'147/125','strict_quotient_lower':'461/500',
        'rational_final_check':str(lower**2*cap),
        'parameter_box':{'phi':['0.039177264','0.039177465'],'theta':['0.681301409','0.681301610']},
        'subcells_per_analytic_piece':a.subcells,'cells':cells,
        'unhalved_components':{k:v.exact() for k,v in components.items()},
        'arithmetic':'90-bit outward dyadic intervals; no floating-point acceptance',
        'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [path,Path(__file__),Path(__file__).with_name('dyadic_interval.py')]},
        'scope':'full six-residual energy of specified trial; support-feasibility proof is analytic',
        'not_claimed':['effective original-sofa entry','optimal feasible coefficient','Lean verification'],
        'seconds':time.time()-t0}
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if not accepted:raise SystemExit(2)


if __name__=='__main__':main()
