#!/usr/bin/env python3
"""Exact rational audit of CD1's independent noncomplementary-corner example.

The mathematical coverage of all real turning angles is proved by
diameter-Lipschitz interpolation between 257 *exactly rational* half-angle
normals, not by treating a finite mesh as continuous feasibility.
Only Python Fraction is used; no CI, Lean or numerical root solver.
"""
from fractions import Fraction as F

H = [
    (F(-61,50),F(48,125)),
    (F(-147,500),F(0)),
    (F(136,125),F(13,500)),
    (F(61,50),F(213,500)),
    (F(149,125),F(897,1000)),
    (F(-263,500),F(1)),
]
LOWER=(F(3,5),F(4,5))
UPPER=(F(20,29),F(21,29))


def convex_cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def area(poly):
    return sum(
        p[0]*q[1]-q[0]*p[1] for p,q in zip(poly,poly[1:]+poly[:1])
    )/2


def raw_width(poly,c,s):
    values=[x*c+y*s for x,y in poly]
    return max(values)-min(values)


def corner(poly,normal):
    c,s=normal
    assert c*c+s*s==1 and c>0 and s>0
    f=max(x*c+y*s for x,y in poly)
    g=max(-x*s+y*c for x,y in poly)
    x=(f-1)*c-(g-1)*s
    y=(f-1)*s+(g-1)*c
    margins=[1-min(f-xx*c-yy*s,g+xx*s-yy*c) for xx,yy in poly]
    return x,y,f,g,min(margins)


def upper_roof(poly,x):
    vals=[]
    for (a,b),(c,d) in zip(poly,poly[1:]+poly[:1]):
        if min(a,c)<=x<=max(a,c):
            if a==c:vals.extend([b,d])
            else:vals.append(b+(d-b)*(x-a)/(c-a))
    return max(vals)


def single_roof_gap(poly,normal):
    c,s=normal
    xi,eta,*_=corner(poly,normal)
    knots=sorted(set([x for x,y in poly]+[xi]))
    def tent(x):
        return eta-(xi-x)*s/c if x<=xi else eta-(x-xi)*c/s
    return max(tent(x)-upper_roof(poly,x) for x in knots)


def main():
    assert all(convex_cross(H[i-1],H[i],H[(i+1)%len(H)])>0 for i in range(len(H)))
    assert area(H)==F(1902703,1000000)
    assert (F(61,25)**2+1)<9  # diameter < 3

    N=256
    sampled_max=F(0)
    argmax=0
    for j in range(N+1):
        q=F(j,N)
        c=(1-q*q)/(1+q*q)
        s=2*q/(1+q*q)
        u=raw_width(H,c,s)
        v=raw_width(H,-s,c)
        if min(u,v)>sampled_max:
            sampled_max,argmax=min(u,v),j
    assert (sampled_max,argmax)==(F(4866293,2468500),116)
    assert sampled_max+F(3,N)==F(2)-F(2673873,157984000)<2
    print("PASS: all complementary directions have min perpendicular width < 2")
    print("exact sampled maximum",sampled_max,"at index",argmax)
    print("rigorous all-angle upper =",sampled_max+F(3,N))

    rhoH=[(x,1-y) for x,y in H]
    a=corner(H,LOWER)
    b=corner(rhoH,UPPER)
    assert a[:2]==(F(591,6250),F(1469,3125))
    assert b[:2]==(F(3827,42050),F(228147,420500))
    assert a[-1]==F(18,625)>0
    assert b[-1]==F(1053,14500)>0
    assert single_roof_gap(H,LOWER)==-F(10581061,21475000)
    assert single_roof_gap(rhoH,UPPER)==-F(65405631,145282750)
    xi,eta=a[:2];zeta,theta=b[:2]
    assert zeta<xi
    penalty=min(LOWER[1]/LOWER[0], UPPER[0]/UPPER[1])*(xi-zeta)
    assert penalty==F(37312,11038125)
    assert eta+theta-penalty-1==F(2431,262500)>0
    print("PASS: each separate pose retains a connected full-projection same-hull body")
    print("CERTIFIED: noncomplementary pair eliminates an interior fiber by",F(2431,262500))


if __name__=="__main__":
    main()
