# A certified coarse angle entry, not yet the effective local stability threshold

## Result actually computed

An exact rational search excludes every original moving sofa of area at least
2219/1000 whose reduced terminal angle satisfies

    arccos(5/11) <= omega <= 2*atan(4/5).

The existing reference lower enclosure M>=2774/1250=2.2192 therefore gives

    M-area(S)<1/5000  ==>  omega>2*atan(4/5)                     (1)

for every admissible reduced angle of S. The latter angle is approximately
77.3196 degrees; the statement uses its exact arctangent expression.

This is an actual finite numerical separation computation, unlike the earlier
unexecuted pixel-cover design. It is ONLY coarse terminal-angle entry. It does
not put the cap or actual sofa inside the local Gerver neighborhood required
by the 2.3 stability theorem, and does not establish its numerical epsilon0.

## 1. Exact terminal-strip outer envelope

For omega<pi/2, translate horizontally until h_S(omega)=1, retaining the initial
horizontal strip 0<=y<=1. The terminal unit strip then gives

    0<=x*cos(omega)+y*sin(omega)<=1.

Parameterize a normal by r=tan(omega/2), so

    n(r)=((1-r^2)/(1+r^2), 2r/(1+r^2)).

Rational r gives an EXACT rational unit normal. For a terminal slab r in [a,b],
with 0<a<=b<1, let n_a,n_b be the endpoint normals. Every relevant point belongs
to the butterfly outer envelope defined by

    0<=y<=1,
    <p,n_b>=0 or greater,
    <p,n_a><=1 OR <p,n_b><=1.

For fixed y, the smallest lower x endpoint is -y*tan(omega_b). The upper endpoint
sec(omega)-y*tan(omega) has derivative proportional to sin(omega)-y, hence only
an interior minimum, not a maximum. Its maximum occurs at a slab endpoint.
Thus the envelope is conservative for every angle in the slab, not merely
sampled angles. A containing rectangle is

    [-tan(omega_b), sec(omega_b)] x [0,1].

The program partitions the butterfly into two convex polygons with disjoint
interiors. Shared boundaries have zero area and are retained where needed.

## 2. Supporting-hallway boxes

Use intermediate half-angle tangents 1/10,1/4,2/5,3/5. These angles are visited
by every reduced motion in the searched slabs. At a fixed intermediate angle,
let u,v be its orthonormal frame and U=h_S(t), V=h_S(t+pi/2). The supporting
hallway condition is

    <p,u><=U, <p,v><=V,
    <p,u>>=U-1 OR <p,v>>=V-1.

If U in [Ul,Uu] and V in [Vl,Vu], replace upper bounds by Uu,Vu and lower
thresholds by Ul-1,Vl-1. The resulting set contains the hallway for EVERY
support choice in the box. Intersect these relaxed hallways with the butterfly
and add the areas of all resulting polygon pieces. This gives an upper bound
for every sofa in that parameter box. Disconnected pieces are all counted;
no unjustified largest-component or regularity reduction is used.

Exact rational Sutherland--Hodgman clipping and the shoelace formula compute
the polygon areas. The disjunctive hallway split has disjoint interiors, so
summing areas does not underestimate the union. Discarding lower-dimensional
pieces changes no area and is not used for connected-component pruning.

This is a Kallus--Romik-style finite-hallway outer-bound method, not a claim to
have invented branch-and-bound for the moving-sofa problem. The implementation
here is independent Python/Fraction code, not their CGAL program. Their primary
implementation was consulted at ykallus/SofaBounds, especially a_priori_bounds
and rotated_ell. The new receipts are for the normalization and bounds stated
here, not imported results from that software.

## 3. Safe support contraction

For any surviving subset S of the current envelope E with area(S)>=a0,
its support in direction n is at most max_E <p,n>. Also, if

    area(E intersect {<p,n><=h})<a0,

then h_S(n)>h. These two implications contract the support box without losing
a feasible high-area sofa. The second is stronger than merely using E's
extreme vertices as a lower support bound.

All arithmetic, clipping, comparisons, and branch decisions use Fractions.
The support bounds are rounded onto a 32-bit dyadic grid OUTWARD: lower bounds
down and upper bounds up. This controls rational denominator growth and cannot
exclude a feasible support value. It is not a floating-point tolerance.

The widest coordinate is bisected. Both children cover the parent. A child is
removed only when its exact area bound is below a0 or a support contradiction
is proved under the hypothesis area(S)>=a0. An exhausted frontier proves the
claimed exclusion. An interrupted or nonempty frontier is reported inconclusive.

## 4. Complete finite cover actually exhausted

The 20 closed slabs [i/100,(i+1)/100], i=60,...,79, cover [3/5,4/5]. The
fixed-angle lower endpoint arccos(5/11) lies strictly ABOVE 2*atan(3/5), because
5/11<8/17=cos(2*atan(3/5)). Thus these slabs cover every relevant angle for (1).

At target a0=2219/1000, the replay exhausted all 20 searches:

    4,848 visited branching nodes,
    4,868 terminal/pruned boxes,
    zero boxes left on every frontier.

The source-hashed per-slab receipts and the coverage checker are retained. The
positive area separation is the exact rational difference

    2774/1250-2219/1000=1/5000.

Small sofas do not create an uncovered class: area(S)<2.2 is already strictly
below the search target. No claim is made that a finite set of hallways alone
characterizes valid motion; only necessity is used for the upper bound.

## 5. Failed and incomplete attempts

The first search kept the sofa horizontally centered and allowed the terminal
strip position to vary. On [37/50,3/4], 1,000 branch visits left an upper bound
above 3.18. It is retained as an inconclusive baseline.

The terminal-pinned version closes that slab in 270 branch visits. But on
[89/100,9/10], a 1,500-node unrounded run still left upper bound about 2.89767.
A separate intermediate-anchor experiment avoids division by small terminal
cosines and improves that surviving bound to about 2.647 after 800 visits,
but still does not prove separation. These are search upper bounds, not
areas of actual sofas, and they are not reported as counterexamples.

A floating-point search of the finite hallway relaxation initially terminated
on the flat empty-intersection region. Seeding it with a positive-area feasible
intersection repaired this optimizer failure, but produced no verified
relaxation counterexample above the target. The absence of such a witness is
not proof that the relaxation can close every remaining slab.

## 6. Remaining effective-entry problem

The proof still needs a global exclusion of actual shapes outside a specified
Gerver neighborhood, INCLUDING motions arbitrarily close to pi/2. Shrinking
the Q-deficit threshold of note19 cannot supply this unless the original sofa
has already been assigned a continuously feasible canonical triple with the
geometric inequality area(S)<=Q. That assignment is precisely one of the local
certificates whose entry is in question.

A practical next certificate should combine support-box outer envelopes with
both directed distance tests, allowing local Q certificates only on boxes where
their hypotheses are certified. It must retain arbitrary missing subsets of
the envelope, rather than testing only the envelope's convex cap. A finite-net
missing-area test for such subsets is recorded in the continuation handoff.

Accordingly (1) is a completed coarse-angle result, but the numerical epsilon0
for unrestricted local stability is NOT completed by this investigation.
