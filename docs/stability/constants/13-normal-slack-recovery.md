# Euclidean-normal recovery: leading factor 100/49 instead of 10.2

Analytic argument only. The previous factor 10.2 controlled vertical roof depth.
The distance theorem needs Euclidean distance, which is much smaller than
vertical depth near a steep smooth part of the roof.

Write x'=-a*u+b*v on the fixed reference core, with a,b>0, q=sqrt(a^2+b^2),
and n=(b*u+a*v)/q, the unit normal pointing into the sofa above the core.

## 1. Balance the slacks for an arbitrary displacement direction

For a unit vector w and p=x(t)+d*w, test the hallway at

    s=t+lambda*d,
    lambda=(<w,v_t>-<w,u_t>)/(a(t)+b(t)).

At d=0 the two inner-wall slacks vanish. Differentiation with t,w held fixed gives

    F1'(0)=<w,u_t>+a*lambda,
    F2'(0)=<w,v_t>-b*lambda.

Both equal

    (b*<w,u_t>+a*<w,v_t>)/(a+b) = [q/(a+b)]*<w,n>.

The exact inequality q/(a+b)>=1/sqrt(2) is just (a-b)^2>=0.
For a regular nearest core point, w=-n, so both violations have first-order
size at least d/sqrt(2). The steepness of the core as a vertical graph has
disappeared from this Euclidean calculation.

The derivative computation is valid across reference phase junctions: it uses
only the reference path and its continuous first derivative. The extra frame
rotation term vanishes at d=0 because p-x(s)=0 there.

## 2. Nearest points at a tail/core corner

There are two inward normals n1,n2, one for each incident arc. Their angle is
less than pi/2, as established by the boundary-angle audit in note 12.
For a point outside the sofa whose nearest point is this corner, the unit
displacement direction w lies in the outward normal cone of the corner.
Consequently

    max(-<w,n1>,-<w,n2>) >= cos(angle(n1,n2)/2) >= 1/sqrt(2).

This follows by writing w's direction between the two outward unit normals;
one is at angular distance at most half their separation. At a reflex corner,
the polar of the union of the two tangent half-planes has no nonzero vector,
so such a corner cannot be a nearest point of a distinct exterior point.

If the selected arc is the core, Section 1 makes both wall derivatives at most
-1/2. If it is a tail, one wall is active with that normal and derivative at
most -1/sqrt(2), while the other wall has a fixed strictly negative reference
slack. Thus the tail witness also achieves the weaker common coefficient 1/2.

On a regular tail point the same argument is easier: w is its outward normal,
the active violation is exactly -d, and the other wall has a negative margin.
At the two endpoints where the tail joins the floor, the boundary is tangent
to the floor. A nearest-point displacement must be vertically down; this cannot
occur for a point of the niche with nonnegative height. Thus the forbidden angle
endpoints 0 and pi/2 need not be used as actual witnesses. Uniform tail margins
still follow by compactness up to those endpoints and the positive inactive
endpoint frame speeds.

## 3. Uniform error control

The core parameters form a compact subset of (0,pi/2), a+b has a positive
minimum there, and lambda(t,w) is continuous on its product with the unit
circle. Choose d0>0 so every shifted angle remains inside (0,pi/2). The two
slack derivatives are jointly continuous in (t,w,d). Restrict to the closed
set of directions with <w,n><=-1/sqrt(2); the value at d=0 is at most -1/2.
Uniform continuity then supplies a common smaller d0 with derivative at most
-c for

    c=49/100 < 1/2.

Integrating from zero gives both slacks <=-c*d for 0<d<=d0. Tail witnesses
have a uniform inactive margin and give the same conclusion after shrinking
d0 again. The finite corner/arc covering makes this bound uniform over all
nearby exterior points, not just along a fixed sequence or at smooth points.

Therefore there is d0>0 such that every p in the reference niche with
0<dist(p,G)<=d0 has a legal hallway angle at which both reference slacks are
at most -(49/100)*dist(p,G).

## 4. Keep deep points out before using the local estimate

The existing clipped vertical roof margin implies that approximate hallway
constraints with vanishing support/slack error exclude points a fixed positive
distance below G. Equivalently, one can cover the compact part of the closed
niche at distance at least d0 by finitely many open strict-violation witnesses.
This supplies a positive error threshold, not a new leading distance factor.

For p outside the reference cap, Euclidean cap closeness supplies a reference
cap point within delta. That point lies in the actual sofa when delta is below
the positive outer-wall/niche margin; otherwise the same margin would put p
inside the reference cap, a contradiction. This is the existing outer-margin
step and costs only delta.

Combining the cases: if K is a normalized nearby cap, S subset K satisfies the
full-angle inner walls up to slack zeta, and upper supports differ by delta,
then, for sufficiently small delta+zeta,

    directed_distance(S,G) <= (100/49)*(delta+zeta).                (1)

This compares actual Euclidean distances, not vertical depth. The reference
threshold in (1) is not computed here.

## 5. Global near-optimal use

The prior local terminal reduction gives zeta<=B*alpha and
alpha<=3.1*(epsilon-e), with fixed B. At centered cap error

    delta<=1.001*sqrt(e),

(1) gives

    directed_distance(S,G)
       <= (100/49)*1.001*sqrt(e) + (100/49)*3.1*B*(epsilon-e).

The first coefficient is about 2.042858. Every larger chosen square-root
coefficient absorbs the linear term by reducing the positive entry threshold.
For the old left-support pin, replace 1.001 by 2.002, giving leading coefficient
about 4.085715. These improvements are independent of the reverse sector-area
argument and of the old vertical slope/interior-ball construction.

No new differentiability is assumed for S or K. Only the fixed reference
geometry supplies the unit normals and uniform Taylor control.
