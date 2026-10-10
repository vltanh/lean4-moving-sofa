#!/usr/bin/env python3
"""Exact unit-span full-turn Steiner-centering obstruction.

Uses only rational arithmetic; the finite grid is upgraded to all angles
by an exact diameter bound and analytic control of both endpoint sectors.
Read the accompanying .md for the endpoint support comparisons.
"""
from fractions import Fraction as F

P = ((F(0), F(90,113)), (F(180,113), F(100,113)),
     (F(180,113), F(0)), (F(135,113), F(0)))
X = F(1,2)
Q = (X, F(1))
BASE = (X, F(90,113)+X/F(18))
SEG = (BASE, Q)
OUTER = P+(Q,)
N = 1024
MAXK = (N*10+10)//11  # ceil(10*N/11)

def dot(p,u):
    return p[0]*u[0]+p[1]*u[1]

def peak(poly, outer, u, v):
    """Exact max_p min(depth_u,depth_v) on a convex polygon/segment."""
    hu = max(dot(z,u) for z in outer)
    hv = max(dot(z,v) for z in outer)
    def depths(p):
        return (hu-dot(p,u), hv-dot(p,v))
    best = max(min(depths(p)) for p in poly)
    edges = (zip(poly, poly[1:]+poly[:1]) if len(poly)>2
             else ((poly[0],poly[1]),))
    for a,b in edges:
        da,db=depths(a),depths(b)
        fa=da[0]-da[1]
        fb=db[0]-db[1]
        if fa*fb<0:
            lam=fa/(fa-fb)
            z=(a[0]+lam*(b[0]-a[0]),a[1]+lam*(b[1]-a[1]))
            best=max(best,min(depths(z)))
    return best

def verify(reflected):
    transform=lambda z:(z[0],-z[1] if reflected else z[1])
    outer=tuple(map(transform,OUTER))
    components=(tuple(map(transform,P)),tuple(map(transform,SEG)))
    best=F(0)
    argmax=(-1,-1)
    k0=N//25 if reflected else 0
    for k in range(k0,MAXK+1):
        den=N*N+k*k
        u=(F(N*N-k*k,den), F(2*N*k,den))
        v=(-u[1],u[0])
        for j,poly in enumerate(components):
            d=peak(poly,outer,u,v)
            if d>best:
                best,argmax=d,(k,j)
    # Every q=tan(t/2) in the covered interval is within 1/(2N)
    # of some sampled k/N. As dt/dq <= 2 and diameter(S) < 2,
    # D(t) <= best+2/N. The two omitted sectors are treated below.
    bound=best+F(2,N)
    assert best<=F(997,1000),(reflected,best,argmax)
    assert bound<1,(reflected,bound)
    return best,argmax,bound

def main():
    diameter_sq=max((a[0]-b[0])**2+(a[1]-b[1])**2
                    for a in OUTER for b in OUTER)
    assert diameter_sq==F(40500,12769)<4
    for reflect in (False,True):
        best,argmax,bound=verify(reflect)
        print('reflected=',reflect,'max_sample=',best,
              'argmax=',argmax,'interior_bound=',bound)
    # q>=10/11 => tan(t)>=220/21>247/26:
    # for S, h(u)=Q.u and h(v)=A.v; split x at 1/2.
    # for reflected S, h(u)=C.u and h(v)=A'.v; split at 3/4.
    assert F(220,21)>F(247,26)
    assert F(220,21)>F(2,3)
    assert F(90,113)**2+F(1,4)<1
    assert F(3,4)+F(23,113)*F(21,220)<1
    assert F(100,113)+(F(180,113)-F(3,4))*F(21,220)<1
    # q<=1/25 => tan(t)<=25/312<26/247:
    # for reflected S, h(v)=D'.v and Q' minimizes p.v,
    # so every depth_v is <= cos(t)-(135/113-1/2)sin(t)<=1.
    assert F(25,312)<F(26,247)
    assert F(25,312)<F(2,3)
    # The centered S contains this centered copy of P.
    centered=((F(0),F(0)),(F(135,113),F(195,452)),
              (F(180,113),F(50,113)),(F(180,113),-F(50,113)),
              (F(135,113),-F(195,452)))
    u=(F(3,5),F(4,5))
    v=(-u[1],u[0])
    z=(F(26640,27007),-F(9620,27007))
    assert z[1]==-F(13,36)*z[0]
    hu=max(dot(p,u) for p in centered)
    hv=max(dot(p,v) for p in centered)
    d1,d2=hu-dot(z,u),hv-dot(z,v)
    assert (hu,hv)==(F(148,113),F(0))
    assert d1==d2==F(27084,27007)>1
    # Horizontal Steiner rearrangement of P, in CCW order:
    hpoly=((-F(45,226),F(0)),(F(45,226),F(0)),
           (F(90,113),F(90,113)),(F(0),F(100,113)),
           (-F(90,113),F(90,113)))
    def polygon_area(vs):
        return abs(sum(dot((a[0],a[1]),(b[1],-b[0]))
                       for a,b in zip(vs,vs[1:]+vs[:1])))/2
    assert polygon_area(P)==polygon_area(hpoly)==F(11025,12769)
    # The horizontal rearrangement also contains the spike tip (0,1).
    hs=hpoly+((F(0),F(1)),)
    for n in ((F(1),F(1)),(-F(1),F(1))):
        raw_support=max(dot(z,n) for z in hs)
        assert raw_support==F(180,113)
        assert raw_support**2>2  # h(unit n) = raw_support/sqrt(2) > 1
    print('horizontal_Steiner_midturn_depth_squared=',F(180,113)**2/2)
    print('diameter_squared=',diameter_sq)
    print('centered_forbidden_depth=',d1,'excess=',d1-1)
    print('PASS: exact full-turn certificate and centered failure')

if __name__=='__main__':
    main()
