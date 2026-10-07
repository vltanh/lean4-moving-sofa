# Numerical reference scales for Euclidean normal and sector recovery

Analytic proof, not Lean verification. This note replaces the two remaining
compact reference-chart choices in the 2.3 argument. The scales are deliberately
much smaller than necessary.

## 1. Reference boundary data and curvature bounds

The actual Gerver set is the region between its upper cap graph and its
zero-extended lower niche roof on [l,r]. The explicit contact description gives:

* both graphs are32-Lipschitz in horizontal coordinates;
* the upper graph is concave and the lower graph is zero on the wings;
* their vertical separation at abscissa x is at least
  min(x-l,r-x,1/3);
* the only corners are the two outer floor corners and two tail/core joins;
  consecutive corner abscissas differ by more than1/10;
* the outer corner openings are pi/2-phi, the two roof corner openings exceed
  pi/2, and all other joins have matching tangent;
* on every regular piece, the unit tangent is2^20-Lipschitz in arclength.

Here are explicit reasons for the last bound. The nonconstant outer contacts
have curvature density at least1/2, so their curvature is at most2. The tails
have speed at least1/8 and a unit tangent rotating with their angle parameter,
so their curvature is at most8. On the core, |x'|>=1/16 and |x''|<=100 on every
analytic piece, giving curvature at most25600<2^20. Matching first derivatives
allow this tangent bound across a phase seam. Stationary contact intervals do
not define additional boundary arcs or corners.

The upper graph slope is bounded by cot(phi)<32 because its nonconstant normal
angles lie in [phi,pi-phi]; the top segment has slope zero. The lower slope bound
189/20 from note06 is smaller than32. For the vertical separation, the two
wing triangles give heights at least x-l and r-x (D<1), while the central
rectangle has height one and the niche roof height is below2/3. The corner
coordinates come directly from x(phi), its reflection, and l,r. Their order
and the stated coarse separation are checked in the reference interval receipt.

## 2. An explicit translated-sector radius

Set

    beta=153/100,   R=10^(-20),   ell=10^6*R.

The minimum corner opening exceeds

    pi/2-0.04 >1.530795>beta+1/2000.                           (1)

We claim that for every p in G, a suitably rotated cone W_p of aperture beta
satisfies

    (p+W_p) intersect closedBall(p,R) subset G.                (2)

The following quantitative chart argument proves uniformity, not merely local
existence at each fixed boundary point.

If dist(p,boundary G)>=R, any such cone works. Otherwise choose a boundary point
q with |p-q|<R (use a slightly larger radius in the equality case; equality also
follows by closedness). Split into two cases.

### Near a corner

If p is within2ell of a corner, use that corner's inward angle bisector as the
vertical chart direction. Work within a ball of radius8ell about the corner.
Every part of either incident boundary graph in that ball has arclength from
the corner at most1024ell: graph length is at most33 times its horizontal
span. Its tangent therefore deviates from the corner tangent by at most

    2^20*1024ell <1/10000.                                  (3)

The incident tangent projections onto the chart's horizontal axis are bounded
below by1/2, using the opening bound (1). They consequently give the two branches
of a single epigraph in this chart. Their slopes have absolute value at most
cot(beta/2), because the angular reserve in (1) exceeds twice (3). Translating
a cone of aperture beta from any point of that epigraph stays in the epigraph
while inside the chart. The whole radius-R cone from p stays in the radius8ell
chart. No other corner enters this chart, since8ell<1/1000. At a roof corner,
the opposite upper boundary is separated by at least1/3 before its32-Lipschitz
variation; at an outer corner, the two incident graphs are exactly the two
boundary branches. Thus no additional boundary cuts the cone.

### Away from all corners

If p is farther than2ell from every corner, q is farther thanell from them.
A radius4R neighborhood of q intersects no corner. The piece of its boundary
graph in that neighborhood has arclength at most264R, so (3) bounds its tangent
variation by much less than1/10000. Rotate the tangent at q to horizontal.
The resulting graph admits a cone much wider than beta and therefore the
selected beta cone from every point of its local epigraph.

The other global graph cannot enter that neighborhood. Its vertical gap at
q.x is at least min(ell/33,1/3): otherwise the32-Lipschitz graph would place q
withinell of an outer corner. Variation over4R changes the gap by at most128R,
whereas ell/33>1000R. Hence the radius-R cone from p does not cross another
boundary component. This proves (2).

The scalar margins in (1)--(3) are checked exactly. The graph/epigraph reasoning
is a mathematical proof, not something established by angular sampling.

## 3. Explicit Euclidean normal-slack scale

On the fixed reference core write x'=-A*u+B*v and Q=sqrt(A^2+B^2). The reference
bounds are

    A+B>=1, |x'|<=10, Lip(x')<=100.

For a unit displacement direction w, use

    lambda=(<w,v>-<w,u>)/(A+B),  s=t+lambda*d,
    F_j(d)=<x(t)+d*w-x(s), n_j(s)>.

Here |lambda|<=2. At d=0 both slacks vanish and their derivatives agree:

    F_j'(0)=[Q/(A+B)]*<w,n>,   n=(B*u+A*v)/Q.

For a regular nearest core point w=-n. At a nearest roof corner, at least one
of the two incident inward normals has <-w,n> >=1/sqrt(2), because their angular
separation is less thanpi/2. If the core normal is selected, Q/(A+B)>=1/sqrt(2)
gives F_j'(0)<=-1/2.

For every d>=0 with the shifted angle legal, differentiate the displayed F_j.
Using |lambda|<=2, the global speed/Lipschitz bounds, and
|x(t)+d*w-x(t+lambda*d)|<=21d gives

    |F_j'(d)-F_j'(0)|<= (2+440+42)d <=1024d.                 (4)

Take d0=10^(-8). Then |lambda|d0<phi/2 and1024d0<1/100. Integrating (4) yields

    both slacks <=-(49/100)d,    0<=d<=d0.                   (5)

If the selected nearest arc is a tail, its active wall has derivative at most
-1/sqrt(2), while the inactive wall has reference slack at most-9/10. A unit
displacement changes that inactive slack by at mostd. The same d0 therefore
works for tails and their joins. At the tail/floor endpoints, a distinct nearest
exterior point would be vertically below the floor, so it is absent from the
nonnegative-height niche case. No derivative of a competing cap or sofa occurs.

## 4. An explicit threshold excludes the deep niche

The earlier vertical certificate is already explicit: coefficient5/51 and
clipping slack tau=1/2040000. For a point of the reference niche at Euclidean
distance at leastd0 from G, its vertical roof depth is at leastd0. That witness
has both slacks at most

    -min((5/51)d0,tau)=-(5/51)d0.

Thus approximate full-angle constraints with support/slack error z satisfying

    z<=10^(-10)<(5/51)d0                                    (6)

exclude all such deep points. For the remaining points use (5). Points outside
the reference cap have distance at mostdelta to a reference cap point; the
explicit outer-wall margin1/5 ensures that point belongs to G when delta<1/5.
The nonnegative floor condition is kept throughout this argument.

Consequently, if K contains S, their upper supports agree, cap support error
is at mostdelta, and the full-angle inner walls hold for S up to slack zeta,
then delta+zeta<=10^(-10) implies

    directed_distance(S,G)<=(100/49)*(delta+zeta).             (7)

This is the intended Euclidean estimate with a numerical hypothesis, not the
weaker vertical estimate or an uncomputed continuity threshold.

## Scope

The sector radius10^-20 and normal depth10^-8 are sufficient reference scales,
not optimized ones. Their proof relies on the fixed reference boundary/contact
classification, the graph description, and the curvature/speed bounds stated
above. The numerical checker covers those scalar enclosures and margins; it
cannot replace independent review of the geometric chart argument.
