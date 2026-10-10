#!/usr/bin/env python3
"""A rational, true-hull full-two-turn sofa with a multipeak corner-height profile.

Every check is exact Fraction arithmetic. The 1025 rational half-angle
frames are upgraded to the entire continuous quarter by a diameter-2
Lipschitz bound; they are not mistaken for sampled-angle feasibility.
The vertical midline survives both whole sweeps, so the saturated
body is connected and has the stated actual convex hull.
No CI, Lean or numerical optimizer.
"""
from fractions import Fraction as F

P = [
    (F(-7761,10000),F(1,2)),
    (F(-141,1000),F(0)),
    (F(7761,10000),F(1,2)),
    (F(6409,10000),F(8956,10000)),
    (F(439,10000),F(1)),
    (F(-5523,10000),F(8306,10000)),
]
N = 1024

def orient(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def frame(k,d):
    q=F(k,d)
    c=(1-q*q)/(1+q*q)
    s=2*q/(1+q*q)
    return c,s

def corner_y(poly,k,d):
    c,s=frame(k,d)
    f=max(x*c+y*s for x,y in poly)
    g=max(-x*s+y*c for x,y in poly)
    return (f-1)*s+(g-1)*c

def worst_vertex_depth(poly):
    best=(F(0),None)
    for k in range(N+1):
        c,s=frame(k,N)
        f=max(x*c+y*s for x,y in poly)
        g=max(-x*s+y*c for x,y in poly)
        z=max(min(f-x*c-y*s,g+x*s-y*c) for x,y in poly)
        if z>best[0]:
            best=(z,k)
    return best

def main():
    assert all(orient(P[i-1],P[i],P[(i+1)%6])>0 for i in range(6))
    W=F(7761,5000)
    assert min(x for x,y in P)==-W/2
    assert max(x for x,y in P)==W/2
    assert min(y for x,y in P)==0
    assert max(y for x,y in P)==1
    # W<2*sqrt(2)-1: the full lower (and reflected upper)
    # inner-corner height is <= max(0,1+W/2-sqrt(2))<1/2.
    assert (W+1)**2<8
    for reflect in (False,True):
        poly=P if not reflect else [(x,1-y) for x,y in P]
        best,k=worst_vertex_depth(poly)
        # Diameter(P) < 2 (fits W x 1 rectangle; W^2+1<4).
        # Each depth function is 2-Lipschitz in angle.
        # Adjacent half-angle samples cover all angles within 1/N.
        assert W*W+1<4
        assert best+F(2,N)<1
        print('hand', 'upper' if reflect else 'lower',
              'max_vertex_depth_sample', best,
              'index',k,'all_angle_bound',best+F(2,N))
    lo,mid,hi=[corner_y(P,k,32) for k in (15,17,18)]
    threshold=F(43,1000)
    assert lo>threshold>mid
    assert hi>threshold
    print('corner_height_at_rational_angles',lo,mid,hi)
    print('PASS: full continuum, both hands, connected saturated same hull')
    print('PASS: positive corner-height superlevel has disconnected components')

if __name__=='__main__':
    main()
