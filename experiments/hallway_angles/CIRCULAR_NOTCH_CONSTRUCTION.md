# A circular-notch forward sofa for every bend

Status: analytic construction with explicit motion. This generalizes the elementary Hammersley stadium-minus-disk construction; no priority claim is made for the family or its formula. The purpose is a closed-form lower bound available at every angle, independent of numerical optimization and of the reverse proof.

Fix 0<beta<pi and r>0. Let K_r be the upper half of the unit-radius stadium around the horizontal segment [-r,r] x {0}. Its area is pi/2+2r and its height is one. Put

    R=r/sin beta,  a=-r cot beta,
    D_r={(x,y): x^2+(y-a)^2<R^2},
    S_{beta,r}=K_r minus D_r.

Assume r tan(beta/2)<1. Then the closed circular segment being removed has top height R+a=r tan(beta/2)<1 and is contained in the full stadium: for every unit normal n,

    a n_y + R <= 1+r|n_x|

when a>=0 by R+a<1, and the corresponding upper-half containment when a<0 follows directly from the horizontal slices. More explicitly for a<0 and y>=0, the disk half-width is at most r, because R^2-(y-a)^2<=R^2-a^2=r^2. For a>=0 the entire disk fits even inside the unit disk about the origin since R+a<1. Thus S is compact, connected, regular closed, and has a positive-height connecting region above its notch.

## Complete forward motion

For 0<=theta<=beta choose inner corner

    C_x(theta)=r sin(beta-2theta)/sin beta,
    C_y(theta)=r[cos(beta-2theta)-cos beta]/sin beta.

The outer normals are n1=(-sin theta,cos theta) and n2=(sin(beta-theta),cos(beta-theta)). Their lines through C pass through (-r,0) and (r,0), respectively:

    n1.C=r sin theta,  n2.C=r sin(beta-theta).

The stadium therefore satisfies both outer-wall inequalities n_j.(p-C)<=1 at every pose.

At height y>=0, the forbidden inner wedge has horizontal section

    -r+y cot theta < x < r-y cot(beta-theta),

whenever this interval is nonempty. It is nonempty exactly when y<C_y(theta). For 0<y<R+a, the eligible theta form an interval [theta_1,theta_2]. Both displayed endpoints decrease continuously with theta; the union of the nonempty intervals is an interval. Its extreme endpoints occur where the wedge collapses to C(theta_1) and C(theta_2). Since C lies on the circle of center (0,a) and radius R, that union is

    -sqrt(R^2-(y-a)^2) < x < sqrt(R^2-(y-a)^2).

At y=0 the limiting interval is (-r,r). Above R+a the union is empty. Thus the union of forbidden wedges inside y>=0 is exactly the open disk segment D_r in that half-plane. The sofa avoids every forbidden wedge, not only a finite list of poses.

At theta=0 and theta=beta the appropriate arm strip is the original horizontal strip. The standard entry/exit translations attach, giving a complete rigid passage. The sofa belongs to the aligned forward class.

## Exact area and optimization in r

The removed circular segment has central angle 2beta and area

    R^2(beta-sin beta cos beta).

Consequently

    area(S_{beta,r})=pi/2+2r-D(beta)r^2,
    D(beta)=(beta-sin beta cos beta)/sin(beta)^2>0.

This concave scalar quadratic is maximized at r=1/D(beta). The feasibility condition is automatic there:

    r tan(beta/2)<1
      iff sin beta(1-cos beta)<beta-sin beta cos beta
      iff sin beta<beta.

Hence for EVERY 0<beta<pi,

    M_plus(beta) >= H(beta)
      :=pi/2+sin(beta)^2/[beta-sin beta cos beta].      (1)

At beta=pi/2 this is the classical Hammersley area pi/2+2/pi. It is not Gerver's area and is not claimed globally optimal.

The derivative of the nonconstant term is

    H'(beta)=2 sin beta [beta cos beta-sin beta]
                    /[beta-sin beta cos beta]^2<0.

Indeed beta cos beta-sin beta has derivative -beta sin beta<0 and vanishes at zero. Thus H is strictly decreasing. At the endpoints,

    H(beta)=3/(2beta)+pi/2+O(beta) as beta->0+,
    H(beta)=pi/2+O((pi-beta)^2) as beta->pi-.

The first estimate improves the initial elementary 1/beta forward construction; it is not a sharp small-bend asymptotic theorem.

## Intended comparison

Combining (1) with the exact reverse-class value V(pi-beta) gives an explicit sufficient range where the reverse class is strictly inferior. A root of H(beta)=V(pi-beta) is a crossing of THIS LOWER BOUND and the reverse optimum, not necessarily the true forward/reverse transition. That distinction must be retained in any theorem or plot.
