# Better area and angle estimates

These are analytic arguments supplementing note 04. No Lean compilation,
verification, or numerical entry-threshold certificate is claimed. Their scalar
budgets are written in `RefinedConstantAlgebra.lean`; the complete geometric
specializations are not yet assembled there.

Use the same normalization, e=M-|U|, epsilon=M-|S|, and

    0<=e<=epsilon,   g=|S minus U|<=epsilon-e,
    delta<=k*sqrt(e),   k<=1001/500.

## 1. Symmetric difference does not need the Hausdorff coefficient 80

The previous area argument first bounded d_H(S,G) and then bounded the area of
a whole neighborhood of G. This unnecessarily amplifies the missing-set error
by a large Hausdorff coefficient. Instead compare U to G using the SMALL CAP
error delta, and add the actual surplus g.

### A sharper convex parallel-layer bound

Let K_G have horizontal width W and vertical width 1. For any h>=0,

    |(K_G + [-h,h]^2) minus K_G| = 2*(W+1)*h + 4*h^2.

Proof: extend each nonempty horizontal fiber by a segment of length 2h. Since
K_G is convex, those fibers are intervals and Cavalieri gives added area 2h.
Then extend vertically by length 2h; the horizontal projection now has length
W+2h, so the second increment is 2h*(W+2h). This argument does not assume
smooth boundary or use the Steiner formula. All sets are bounded and measurable.

A Euclidean h-neighborhood is contained in this square neighborhood. The
reference enclosures give W<13/4, hence

    |(K_G + Bbar_h) minus K_G| <= (17/2)*h + 4*h^2.

In particular, support/Hausdorff cap error delta bounds |K minus K_G| by that
quantity. The dilation-about-an-inscribed-disk estimate is much less efficient.

### The excess of U inside the reference cap lies in a thin roof band

If p belongs to (U minus G) intersect K_G, then p is in the reference niche.
Let d=gamma(p.x)-p.y>0. The reference slack certificate with c_roof=1/26
provides a hallway for which both slacks are at most -min(d/26,tau).
Since p is in U, at least one competing slack is nonnegative. Support error
delta therefore gives

    min(d/26,tau)<=delta.

Choose the fixed near-optimal threshold so delta<tau. It follows that d<=26*delta.
Thus these points occupy a vertical band of thickness at most 26*delta over
the reference niche interval. Its width w=b-a is less than 13/8, so its area is
at most (169/4)*delta. This needs no estimate on the boundary of the competitor.

Adding the cap layer gives

    |U minus G| <= (203/4)*delta + 4*delta^2.

### Use the finite-area identity, not a second Hausdorff conversion

Because |G|-|S|=epsilon,

    |S symmetric_difference G| = epsilon+2*|S minus G|.

Also S minus G is contained in (S minus U) union (U minus G), so

    |S triangle G|
      <= epsilon+2*g+(203/2)*delta+8*delta^2
      <= 3*epsilon-2*e+(203/2)*k*sqrt(e)+8*k^2*e.

This is the useful TWO-BUDGET estimate. It can be kept in this form when e is
available rather than replaced everywhere by epsilon.

For a universal coefficient, use k<=1001/500, k^2<=401/100 and e<=epsilon:

    |S triangle G| <= (203203/1000)*sqrt(epsilon)+(827/25)*epsilon.

For sqrt(epsilon)<=1/50, this is less than 204*sqrt(epsilon). Intersect this
explicit smallness requirement with the other local-entry thresholds. Therefore:

**Derived area theorem.** There exists epsilon0>0 such that every original
moving sofa of deficit epsilon<epsilon0 satisfies

    |normalizedSofa P S triangle G| <= 204*sqrt(epsilon).

No numerical epsilon0 is thereby obtained, because the other entry conditions
remain existential. This estimate is independent of the interior-ball ratio
and does not use the global Hausdorff coefficient 80 at all.

### Full-angle contained sofas

When S is contained in U, g=0 and the same argument improves to

    |S triangle G| <= epsilon+(203/2)*k*sqrt(e)+8*k^2*e.

For S=U, e=epsilon. When the cap deficit e is much smaller than epsilon, the
set-area conclusion is substantially better than simply inserting epsilon
into every term.

## 2. The terminal slice can be a trapezoid instead of a rectangle

Let D=a-l>403/500 be the left-wing width. Choose

    eta = D/1000,     lambda = 999/1000,
    I = [l+eta,a-eta].

For every sufficiently small positive alpha, consider

    F_alpha = {(x,y): x in I, 0<=y<=lambda*alpha*(a-x)}.

Its area is exactly

    lambda*alpha*[(D-eta)^2-eta^2]/2
      = (999/1000)*(499/1000)*D^2*alpha.

The interval I is a fixed compact subset of the interior of the reference left
wing's floor interval. The reference cap has a positive upper-wall margin on
I x [0,h] for some h>0, and reference niche localization leaves that rectangle
outside the competing niche for all sufficiently nearby caps. Once alpha is
small enough, F_alpha lies in that rectangle and hence in U. This is the same
floor-persistence argument used by the earlier rectangular slice, now applied
to a larger fixed floor interval.

### Why the tilted terminal strip excludes this trapezoid

For a nearby cap, its top supporting face has a point q=(q.x,1) with q.x>=a-zeta,
where zeta>0 can be made arbitrarily small by reducing the support neighborhood.
This is exactly the existing exposed-face stability at the top normal; it does
not assume a top contact near the right endpoint of that face.

Write v=a-x, so eta<=v<=D-eta. For a point of F_alpha,

    (q-p) dot u_(pi/2-alpha) - 1
      >= (v-zeta)*sin(alpha)+cos(alpha)-1-lambda*alpha*v.

Using sin(alpha)>=alpha-alpha^3/6 and cos(alpha)>=1-alpha^2/2, the right side is
at least

    alpha*((1-lambda)*v-zeta-alpha/2-v*alpha^2/6).

Fix zeta<eta/4000. Then take alpha>0 small enough that
alpha/2+D*alpha^2/6<eta/4000. Since (1-lambda)*v>=eta/1000, the last expression
is strictly positive. Hence p violates the terminal lower strip wall and cannot
belong to S. There is no assertion that S can complete the remaining rotation.

### Omitted wedges still have arbitrarily small linear gain

The existing floor-coverage/localization argument confines newly admitted late
wedges to two arbitrarily short endpoint windows, with their height O(alpha).
Choose those windows and then the support/angle neighborhood so that the gain
is at most alpha/1000. This choice is fixed before the input sofa is considered.

Consequently,

    |S| <= |U| - [lambda*(499/1000)*D^2-1/1000]*alpha.

Exact rational arithmetic at D=403/500 gives

    (999/1000)*(499/1000)*D^2-1/1000 > 10/31.

Therefore:

    |S| <= |U|-(10/31)*alpha,
    alpha <= (31/10)*(epsilon-e) <= (31/10)*epsilon.

**Derived angle theorem.** After reducing a fixed positive deficit threshold,
every admissible reduced angle of every near-maximal sofa satisfies

    0<=pi/2-omega <= 3.1*(M-|S|).

This improves the older coefficient 4 budget. It is not claimed optimal.
The coefficients approach D^2/2 as the interval and height truncations vanish,
so this particular floor argument permits every angle coefficient strictly
larger than 2/D^2. It does not show that a matching family of actual sofas exists.

## 3. The three constants can be used simultaneously

Intersect the positive thresholds in note 04 and this note. One obtains a
single existential epsilon0 for coefficients

    Hausdorff: 80,    symmetric difference: 204,    terminal angle: 31/10.

The area and angle improvements are separate geometric arguments, not numerical
optimizations of a solver output. They do not affect the faithful Baek proof,
the main uniqueness proof, or the bridge. These analytic conclusions require
independent review and the new formal adapters before any claim of Lean-checked
numerical constants.
