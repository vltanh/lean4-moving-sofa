#!/usr/bin/env python3
"""Exact continuous-angle certificate: actual full-turn convex hulls are not
closed under horizontal-reflection Minkowski averaging.

The exact grid check is converted to a proof for *every* t in [0,pi/2]
using a uniform diameter Lipschitz bound. Uses Python Fraction only.
No CI, Lean, sampled-area assertion, or numerical optimization.
"""
from fractions import Fraction as Q
from itertools import combinations

P = (
    (Q(-3, 4), Q(319, 500)),
    (Q(-1493, 10000), Q(0)),
    (Q(3, 4), Q(409, 500)),
    (Q(161, 2500), Q(1)),
)
N = 1024


def dot(x, y):
    return x[0]*y[0] + x[1]*y[1]


def orient(a, b, c):
    return ((b[0]-a[0])*(c[1]-a[1])
            -(b[1]-a[1])*(c[0]-a[0]))


def worst_depth_at_frame(vertices, u, v):
    """Exact max over every *point*, not just vertices, of min(depth_u,depth_v).

    For interior p, moving in direction -(u+v) increases both depths
    until reaching the polygon boundary. On each edge the minimum of
    two affine functions is piecewise affine; maxima occur at endpoints
    or where the two affine depths agree.
    """
    hu = max(dot(p,u) for p in vertices)
    hv = max(dot(p,v) for p in vertices)
    du = [hu-dot(p,u) for p in vertices]
    dv = [hv-dot(p,v) for p in vertices]
    best = max(min(a,b) for a,b in zip(du,dv))
    for j in range(len(vertices)):
        k=(j+1)%len(vertices)
        a,b=du[j]-dv[j],du[k]-dv[k]
        if a*b<0:
            f=a/(a-b)
            best=max(best,du[j]+f*(du[k]-du[j]))
    return best


def certify_one_hand(reflect_vertical):
    vertices = tuple((x, -y if reflect_vertical else y) for x,y in P)
    best=Q(0)
    best_k=None
    for k in range(N+1):
        den=N*N+k*k
        u=(Q(N*N-k*k,den),Q(2*N*k,den))
        v=(-u[1],u[0])
        d=worst_depth_at_frame(vertices,u,v)
        if d>best:
            best,best_k=d,k
    # Nearest half-angle parameter knot is <=1/(2N) away;
    # dt/dq=2/(1+q²)<=2; |delta t|<=1/N.
    # Diameter of P is strictly <2, so depths are 2-Lipschitz in t.
    strict_all_angles=best+Q(2,N)
    assert strict_all_angles<1,(reflect_vertical,best,best_k)
    return best,best_k,strict_all_angles


def main():
    assert all(orient(P[i],P[(i+1)%4],P[(i+2)%4])>0
               for i in range(4))
    diameter2=max(
        sum((a[j]-b[j])**2 for j in range(2))
        for a,b in combinations(P,2)
    )
    assert diameter2 == Q(2853,1250) < 4
    for hand in (False,True):
        best,k,bound=certify_one_hand(hand)
        print("vertical_reflection=",hand,
              "sample_max=",best,"sample_index=",k,
              "continuous_angle_upper=",bound)
    area=abs(sum(P[i][0]*P[(i+1)%4][1]
                 -P[(i+1)%4][0]*P[i][1] for i in range(4)))/2
    assert area == Q(730767,1000000)
    # J(x,y)=(-x,y), K=(P+JP)/2.
    # P has unique bottom point B, JP has unique bottom point JB;
    # their midpoint O=(0,0) is K's unique bottom point.
    O=(Q(0),Q(0))
    R=(Q(3,4),Q(91,125))
    L=(-R[0],R[1])
    u=(Q(3,5),Q(4,5))
    v=(-u[1],u[0])
    assert dot(R,u)-dot(O,u) == Q(2581,2500) > 1
    assert dot(L,v)-dot(O,v) == Q(648,625) > 1
    # Quantitative saturation loss: every vertex is in a wedge about B;
    # the Minkowski average lies in |x| <= (6/5)y, so at y<=1/50
    # both forbidden-wall depths remain strictly greater than 1.
    bottom_x=P[1][0]
    assert all(abs(x-bottom_x)<=Q(6,5)*y for x,y in P)
    first_depth=Q(2581,2500)-Q(38,1250)
    second_depth=Q(648,625)-Q(39,1250)
    assert first_depth==Q(501,500)>1
    assert second_depth==Q(1257,1250)>1
    # The average also contains (0,1/2), which survives every normal
    # since the hull is inside the (3/2) by 1 incoming rectangle.
    assert Q(3,4)**2+Q(1,2)**2==Q(13,16)<1
    print("excluded_bottom_band_through_y=",Q(1,50),
          "support_depth_margins=",first_depth-1,second_depth-1)
    print("diameter_squared=",diameter2,"exact_area=",area)
    print("mean_hull_forbidden_support_lower_bounds=",dot(R,u),dot(L,v))
    print("PASS: genuine convex two-full-turn body; reflection-mean hull is inadmissible")


if __name__ == "__main__":
    main()
