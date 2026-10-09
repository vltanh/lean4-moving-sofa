#!/usr/bin/env python3
"""Exact Fraction certificate: convex two-45-degree sofa area <= 31/20.

Hand geometric reduction: a convex body avoiding the two opposed open
inner corner quadrants can be separated from each by a half-plane
through the respective corner, with nonnegative normal weights.
The width of the incoming strip in the rotated sum coordinate is sqrt(2).

For each rational parameter subbox, form a rational POLYGON enclosing all
possible convex bodies in that box. Its maximal intersection with ANY
sum-coordinate band of width 283/200 > sqrt(2) is obtained exactly by
1D piecewise-linear section integration and rational stationary points.
This self-contained rational verifier exhaustively partitions [1,4]^2 x [0,1]^2.
No floating-point, optimization code, CI, or Lean.
"""
from fractions import Fraction as F
from bisect import bisect_right
from time import monotonic

D=F(283,200)  # > sqrt(2), because 283**2 > 2*200**2
TARGET=F(31,20)

def clip_polygon(poly, a,b,c):
    """Keep exact rational halfspace ax+by<=c."""
    if len(poly)<3:return []
    result=[]
    old=poly[-1]; d0=a*old[0]+b*old[1]-c
    for new in poly:
        d1=a*new[0]+b*new[1]-c
        if (d1<=0)!=(d0<=0):
            t=d0/(d0-d1)
            point=(old[0]+t*(new[0]-old[0]),old[1]+t*(new[1]-old[1]))
            result.append(point)
        if d1<=0:result.append(new)
        old=new;d0=d1
    return result

def area(poly):
    if len(poly)<3:return F(0)
    return abs(sum(a[0]*b[1]-b[0]*a[1] for a,b in zip(poly,poly[1:]+poly[:1])))/2

def graph(poly):
    if len(poly)<3 or area(poly)==0:return None
    zz=sorted({p[0]+p[1] for p in poly})
    if len(zz)<2:return None
    gg=[]
    for z in zz:
        uu=[]
        for a,b in zip(poly,poly[1:]+poly[:1]):
            za=a[0]+a[1];zb=b[0]+b[1]
            if za==zb==z:uu.extend([a[0],b[0]])
            elif (za<=z<=zb or zb<=z<=za) and za!=zb:
                t=(z-za)/(zb-za)
                uu.append(a[0]+t*(b[0]-a[0]))
        assert uu, (poly,z)
        gg.append(max(uu)-min(uu))
    return zz,gg

def max_band_area(poly,d=D):
    """Exact max_a area(poly ∩ {a<=x+y<=a+d})."""
    data=graph(poly)
    if data is None:return F(0)
    z,g=data
    prefix=[F(0)]
    for j in range(1,len(z)):
        prefix.append(prefix[-1]+(z[j]-z[j-1])*(g[j]+g[j-1])/2)
    def antiderivative(x):
        if x<=z[0]:return F(0)
        if x>=z[-1]:return prefix[-1]
        j=bisect_right(z,x)-1
        return prefix[j]+(x-z[j])*(g[j]+(g[j+1]-g[j])*(x-z[j])/(2*(z[j+1]-z[j])))
    def density(x):
        if x<z[0] or x>z[-1]:return F(0)
        j=min(bisect_right(z,x)-1,len(z)-2)
        return g[j]+(g[j+1]-g[j])*(x-z[j])/(z[j+1]-z[j])
    a_min=z[0]-d;a_max=z[-1]
    breaks=sorted(set([a_min,a_max]+z+[x-d for x in z]))
    cand=[x for x in breaks if a_min<=x<=a_max]
    for left,right in zip(breaks,breaks[1:]):
        if left<a_min or right>a_max:continue
        p=(3*left+right)/4;q=(left+3*right)/4
        s1=density(p+d)-density(p)
        s2=density(q+d)-density(q)
        if s1!=s2:
            root=p-(q-p)*s1/(s2-s1)
            if left<root<right:
                cand.append(root)
    return max((antiderivative(a+d)-antiderivative(a) for a in cand),default=F(0))

def enclosure(box):
    """Enclose all actual K with (P,Q,lower_weight,upper_weight) in box."""
    (P0,P1),(Q0,Q1),(lam0,lam1),(mu0,mu1)=box
    # Any K is inside 0<=u<=P1, 0<=v<=Q1.
    lam=(lam0+lam1)/2;dlam=(lam1-lam0)/2
    mu=(mu0+mu1)/2;dmu=(mu1-mu0)/2
    R=max(P1,Q1)
    # Lower support condition: lam0actual*(u-P+1)
    # +(1-lamactual)*(v-Q+1) >= 0, with lamactual in [lam0,lam1].
    # Recenter lam and lower P,Q, losing at most dlam*(|P0-Q0|+R).
    err=dlam*(abs(P0-Q0)+R)
    a=lam;b=1-lam
    lower=a*(P0-1)+b*(Q0-1)-err
    # Upper safe halfplane: muactual*u+(1-muactual)*v<=1.
    # Recenter mu; |u-v|<=max(P1,Q1).
    upper=1+dmu*R
    poly=[(F(0),F(0)),(P1,F(0)),(P1,Q1),(F(0),Q1)]
    poly=clip_polygon(poly,-a,-b,-lower)
    poly=clip_polygon(poly,mu,1-mu,upper)
    return poly

def prove(target=TARGET, verbose=True, max_nodes=1000000):
    root=((F(1),F(4)),(F(1),F(4)),(F(0),F(1)),(F(0),F(1)))
    pending=[(root,0)]
    nodes=leaves=depth=0
    worst=F(0)
    start=monotonic()
    while pending:
        box,n=pending.pop();nodes+=1;depth=max(depth,n)
        if nodes>max_nodes:raise RuntimeError(('unresolved',nodes,box))
        P1=box[0][1];Q1=box[1][1]
        if D*min(P1,Q1)<=target:
            leaves+=1;continue
        poly=enclosure(box)
        ub=area(poly)
        if ub>target:
            ub=max_band_area(poly)
        if ub<=target:
            leaves+=1
            if ub>worst:worst=ub
            continue
        # Split parameter with the largest normalized relative width.
        index=max(range(4),key=lambda j:(box[j][1]-box[j][0])/((3,3,1,1)[j]))
        l,h=box[index];m=(l+h)/2
        child1=list(box);child2=list(box)
        child1[index]=(l,m);child2[index]=(m,h)
        pending.append((tuple(child2),n+1))
        pending.append((tuple(child1),n+1))
    assert 283**2>2*200**2
    assert 31*5 < 8*20  # 31/20 < 8/5 < Romik M
    assert target == TARGET
    if verbose:
        print('PASS: exact rational exhaustive certificate: convex two-midpoint area <=',target)
        print('nodes =',nodes,'leaves =',leaves,'maximum depth =',depth)
        print('maximum accepted enclosed area =',worst)
        print('seconds =',round(monotonic()-start,3))
    return nodes,leaves,depth,worst

def self_test():
    square=[(F(0),F(0)),(F(1),F(0)),(F(1),F(1)),(F(0),F(1))]
    rectangle=[(F(0),F(0)),(F(1),F(0)),(F(1),F(3)),(F(0),F(3))]
    triangle=[(F(0),F(0)),(F(2),F(0)),(F(0),F(2))]
    assert max_band_area(rectangle)==D
    assert max_band_area(square)==1-(2-D)**2/4
    assert max_band_area(triangle)==2*D-D*D/2
    assert max_band_area(enclosure(((F(3,2),F(3,2)),(F(3,2),F(3,2)),(F(1,2),F(1,2)),(F(1,2),F(1,2)))))==F(5,4)
    print('PASS: exact analytic rectangle, square, triangle and separated-corner test geometries')

if __name__=='__main__':
    self_test()
    prove()
