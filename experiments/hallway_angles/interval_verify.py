"""Independent continuous-motion checker for unions of dyadic rectangles.

No optimizer, SciPy, Shapely, or platform sin/cos is used in verification.
Trigonometry uses integer interval Taylor series with an explicit remainder.
Other operations use binary64 intervals expanded outward with nextafter.
Assumptions: IEEE-754 binary64 basic operations and correct Python integers.
This is a numerical certificate checker, not a Lean formalization.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import lru_cache
import json
import math
from pathlib import Path
import time
import numpy as np

BITS=90
Q=1<<BITS
GRID=1<<30

def ceildiv(a: int,b: int)->int:
    return -((-a)//b)

def _atan(q: int,n: int):
    s=sum((Fraction((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),Fraction())
    r=Fraction((-1)**n,(2*n+1)*q**(2*n+1))
    return min(s,s+r),max(s,s+r)

def _pi_bounds():
    a,b=_atan(5,50);c,d=_atan(239,15)
    lo,hi=16*a-4*d,16*b-4*c
    return (lo.numerator*Q//lo.denominator,ceildiv(hi.numerator*Q,hi.denominator))
PI=_pi_bounds()
assert Fraction(4**67,math.factorial(67)) < Fraction(1,Q)
assert Fraction(4**66,math.factorial(66)) < Fraction(1,Q)

def _imul(a,b):
    p=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(p)//Q,ceildiv(max(p),Q)

def _ineg(a): return -a[1],-a[0]
def _idiv(a,d): return a[0]//d,ceildiv(a[1],d)
def _iadd(a,b): return a[0]+b[0],a[1]+b[1]

@lru_cache(maxsize=65536)
def trig_point(coefficient: Fraction):
    """Enclose sin(pi*a), cos(pi*a), for -1 <= a <= 1, in units 2^-90."""
    if abs(coefficient)>1: raise ValueError('angle outside Taylor domain')
    products=[PI[0]*coefficient.numerator,PI[1]*coefficient.numerator]
    x=(min(products)//coefficient.denominator,ceildiv(max(products),coefficient.denominator))
    x2=_imul(x,x)
    s=st=x;c=ct=(Q,Q)
    for k in range(1,33):
        st=_ineg(_idiv(_imul(st,x2),(2*k)*(2*k+1)))
        ct=_ineg(_idiv(_imul(ct,x2),(2*k-1)*(2*k)))
        s=_iadd(s,st);c=_iadd(c,ct)
    # Taylor remainder <= 4^67/67! for sine, 4^66/66! for cosine.
    return (s[0]-1,s[1]+1),(c[0]-1,c[1]+1)

def trig_range(a: Fraction,b: Fraction):
    if a>b: a,b=b,a
    s,c=trig_point((a+b)/2)
    radius=(b-a)/2
    e=ceildiv(PI[1]*radius.numerator,radius.denominator)
    # Both sine and cosine are 1-Lipschitz in radians.
    def out(z):
        lo=max(-Q,z[0]-e);hi=min(Q,z[1]+e)
        return np.nextafter(float(Fraction(lo,Q)),-np.inf),np.nextafter(float(Fraction(hi,Q)),np.inf)
    return out(s),out(c)

def down(x): return np.nextafter(x,-np.inf)
def up(x): return np.nextafter(x,np.inf)
def add(a,b): return down(a[0]+b[0]),up(a[1]+b[1])
def neg(a): return -a[1],-a[0]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    p=np.broadcast_arrays(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1])
    lo=np.minimum.reduce(p);hi=np.maximum.reduce(p)
    if not (np.isfinite(lo).all() and np.isfinite(hi).all()):
        raise ArithmeticError('nonfinite interval operation')
    return down(lo),up(hi)

def normals_interval(beta: Fraction,mode: str,u0: Fraction,u1: Fraction):
    turn=beta if mode=='forward' else beta-1
    theta0,theta1=turn*u0,turn*u1
    s1,c1=trig_range(theta0,theta1)
    s2,c2=trig_range(beta-theta0,beta-theta1)
    return [(neg(s1),c1),(s2,c2)]

def _corner_interval(a,b,s0,s1):
    def at(s):
        # s and 1-s are exact dyadic binary64 values at the allowed depths.
        v=float(s)
        return add(mul((a,a),(1.-v,1.-v)),mul((b,b),(v,v)))
    aa,bb=at(s0),at(s1)
    return np.minimum(aa[0],bb[0]),np.maximum(aa[1],bb[1])

def _dot(n,dx,dy): return add(mul(n[0],dx),mul(n[1],dy))

def interval_safe(boxes,corner,ns):
    """Sufficient containment of every whole rectangle over a time interval."""
    dx=(down(boxes[:,0]-corner[1][0]),up(boxes[:,1]-corner[0][0]))
    dy=(down(boxes[:,2]-corner[1][1]),up(boxes[:,3]-corner[0][1]))
    f=[_dot(n,dx,dy) for n in ns]
    outer=(f[0][1]<=1.) & (f[1][1]<=1.)
    inner=(f[0][0]>=0.) | (f[1][0]>=0.)
    # For a rectangle and wedge, useful separating directions include their
    # wall normals and the coordinate axes. Candidate weights need not be
    # optimal: the ensuing interval inequality is independently sufficient.
    for axis in (0,1):
        a=sum(ns[0][axis])/2.;b=sum(ns[1][axis])/2.
        if a==b: continue
        weight=b/(b-a)
        if not 0.<=weight<=1.: continue
        v=1.-weight  # interpreted as its exact binary64 value, also >= 0
        normal=tuple(add(mul(ns[0][j],(weight,weight)),mul(ns[1][j],(v,v))) for j in (0,1))
        inner |= _dot(normal,dx,dy)[0]>=0.
    return outer & inner

def largest_rectangle_component(boxes):
    """Exact integer connectivity/area; rectangles occupy disjoint row slabs."""
    if len(boxes)==0: return [],0
    rows={}
    for i,(x0,x1,y0,y1) in enumerate(boxes):
        if x0>=x1 or y0>=y1: raise ValueError('degenerate rectangle')
        rows.setdefault((y0,y1),[]).append(i)
    rowkeys=sorted(rows)
    for k,(lo,hi) in enumerate(rowkeys):
        if k and rowkeys[k-1][1]>lo: raise ValueError('overlapping row slabs')
        ids=sorted(rows[(lo,hi)],key=lambda i:boxes[i][0])
        for a,b in zip(ids,ids[1:]):
            if boxes[a][1]>boxes[b][0]: raise ValueError('overlapping rectangles')
    parent=list(range(len(boxes)))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]];i=parent[i]
        return i
    for prev,nextrow in zip(rowkeys,rowkeys[1:]):
        if prev[1]!=nextrow[0]: continue
        for i in rows[prev]:
            for j in rows[nextrow]:
                if max(boxes[i][0],boxes[j][0]) < min(boxes[i][1],boxes[j][1]):
                    parent[root(i)]=root(j)
    components={}
    for i in range(len(boxes)):components.setdefault(root(i),[]).append(i)
    def area(ids): return sum((boxes[i][1]-boxes[i][0])*(boxes[i][3]-boxes[i][2]) for i in ids)
    best=max(components.values(),key=area)
    return best,area(best)

def verify(data: dict,max_depth: int=18):
    if not isinstance(max_depth,int) or not 0<=max_depth<=30: raise ValueError('invalid depth')
    if data.get('format')!='hallway-dyadic-rectangles-v1' or data.get('grid_denominator')!=GRID:
        raise ValueError('unsupported certificate format or grid')
    beta=Fraction(str(data['bend_degrees']))/180
    mode=data['mode']
    if not 0<beta<1 or mode not in ('forward','reverse'): raise ValueError('invalid hallway')
    corners=np.array([[float.fromhex(v) for v in row] for row in data['corner_hex']],dtype=float)
    if corners.ndim!=2 or corners.shape[1]!=2 or len(corners)<2 or not np.isfinite(corners).all():
        raise ValueError('invalid corner path')
    if corners[0,1]!=0. or corners[-1,1]!=(0. if mode=='forward' else 1.):
        raise ValueError('invalid entry/exit heights')
    boxes=data['boxes']
    if any(len(b)!=4 or any(not isinstance(x,int) or isinstance(x,bool) or abs(x)>2**50 for x in b) for b in boxes):
        raise ValueError('boxes must be bounded integer quadruples')
    if any(not 0<=b[2]<b[3]<=GRID for b in boxes): raise ValueError('box outside entry strip')
    # This also validates the exact disjoint-row representation.
    largest_rectangle_component(boxes)
    bf=np.asarray(boxes,dtype=float).reshape(-1,4)/GRID
    active=np.ones(len(boxes),dtype=bool)
    count=max_seen=0
    start=time.monotonic()
    n=len(corners)-1
    def visit(i,a,b,ids,depth):
        nonlocal count,max_seen
        ids=ids[active[ids]]
        if not len(ids): return
        count+=1;max_seen=max(max_seen,depth)
        ns=normals_interval(beta,mode,(i+a)/n,(i+b)/n)
        ci=_corner_interval(corners[i],corners[i+1],a,b)
        safe=interval_safe(bf[ids],ci,ns)
        unresolved=ids[~safe]
        if not len(unresolved): return
        if depth==max_depth:
            active[unresolved]=False
            return
        mid=(a+b)/2
        visit(i,a,mid,unresolved,depth+1)
        visit(i,mid,b,unresolved,depth+1)
    for i in range(n):visit(i,Fraction(0),Fraction(1),np.flatnonzero(active),0)
    ids=np.flatnonzero(active).tolist()
    selected,numerator=largest_rectangle_component([boxes[i] for i in ids])
    selected=[ids[j] for j in selected]
    area=Fraction(numerator,GRID*GRID)
    return {'status':'interval checked under documented binary64/integer assumptions',
        'proposed_rectangles':len(boxes),'verified_rectangles':len(ids),
        'connected_rectangles':len(selected),'selected_indices':selected,
        'area_numerator':area.numerator,'area_denominator':area.denominator,
        'area_float_display':float(area),'interval_nodes':count,
        'max_depth_reached':max_seen,'max_depth_limit':max_depth,
        'elapsed_seconds':time.monotonic()-start}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',type=Path)
    p.add_argument('--max-depth',type=int,default=18)
    p.add_argument('--output',type=Path)
    args=p.parse_args();report=verify(json.loads(args.certificate.read_text()),args.max_depth)
    text=json.dumps(report,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print({k:v for k,v in report.items() if k!='selected_indices'})
if __name__=='__main__':main()
