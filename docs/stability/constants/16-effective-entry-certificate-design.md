# Effective entry: a convergent finite certificate scheme, not a computed epsilon0

The new coefficients do not make the old entry threshold numerical. This note
separates an implementable finite certificate from two tempting circular or
incomplete substitutes. No global enumeration has been run in this continuation.

## 1. What must actually be excluded

Fix a positive computable radius eta in the chosen normalization. The desired
certificate is

    every moving sofa S with d_H(S,G)>=eta has area(S)<=U_eta<M.    (1)

Then epsilon<M-U_eta forces Hausdorff entry. A certificate that only excludes
far CAP variables is insufficient unless they are tied to the support of the
actual connected sofa; an artificially oversized unused cap can be far from
G while containing a copy of G of area M.

It is circular to insert epsilon<(eta/2.3)^2 into the new near-optimal estimate
to prove its own entry hypothesis. Likewise, the earlier 1e-14 calculation
still certifies only downstream smallness after the local certificates apply.

## 2. A finite outer-pixel scheme

For deficits below 0.01, the prior area/reduced-angle bounds put the relevant
motion angle in [omega0,pi/2], omega0=acos(5/11)>pi/4. The connected supporting-
hallway argument in SofaBounds bounds horizontal span by six, independently of
local entry. After horizontal midpoint/top normalization, m(G) lies in (-1,0),
so the sofa lies in the fixed rational box B=[-4,3] x [0,1].

For h=2^(-n), enumerate nonempty unions V of closed h-by-h grid squares in B.
Their interiors are disjoint, and |V| is exactly an integer times h^2. Retain
only unions whose closed-square adjacency graph is connected, including corner
adjacency. This matches the original closed-connected set class; requiring
path-connected interior would wrongly exclude admissible sofas.

Enumerate motion angles omega_l=omega0+(pi/2-omega0)*l/2^n. The endpoints and
trigonometric values are computable and can be enclosed by rational intervals.
For each V and omega_l, test its OWN support function h_V, not an unrelated
cap support variable. Necessary approximate conditions are:

* top support equals one and horizontal midpoint is within O(h) of m(G);
* at every occupied square center p and t_j=j*omega_l/2^n, both upper support
  walls are built from h_V and

      max(<p,u_tj>-h_V(t_j)+1,
          <p,v_tj>-h_V(t_j+pi/2)+1) >= -100h;

* the terminal strip obeys

      <p,u_omega_l>-h_V(omega_l)+1 >= -100h;

* an interval enclosure of d_H(V,G), of width at most h, is not wholly below
  eta/2.

All of these are finite tests with conservative rational interval arithmetic.
The tolerance 100h is deliberately loose: points and supports change by at
most a fixed multiple of h under pixel rounding and angle rounding, since
B is bounded. Rational interval evaluation can use an additional absolute error
at most h, still absorbed by that margin. This is an outer test: uncertain
candidates are kept, not discarded.

Exact support evaluation of V is the maximum over finitely many square vertices.
Distance to the fixed computable finite-arc reference can be enclosed by
subdividing its arc parameters and bounding their derivatives. Compact polygon
versus reference distance in both directions must be checked; distance of
convex hulls is not a replacement.

## 3. Why every truly excluded sofa has a retained cover

Let S be normalized with d_H(S,G)>=eta. Take all squares meeting S. Their union
V contains S and lies within sqrt(2)h of it, remains connected, and lies in B.
For sufficiently small h its midpoint and top tests pass. Choose the nearest
omega_l to the actual reduced angle omega.

At matching sampled parameters, replacing a point of S by a square center costs
at most sqrt(2)h in each unit-normal projection. Replacing h_S by h_V costs
at most sqrt(2)h. Angle rounding costs at most a uniform radius bound times h
for both the point projection and support. These errors are strictly smaller
than the stated 100h tolerance on the fixed box. The terminal test is handled
by the same estimate.

Finally d_H(V,G)>=eta-sqrt(2)h>eta/2 for small h. Thus this cover is retained
and |S|<=|V|. The largest retained pixel area U_n is an upper bound for every
sofa in (1). If no candidate is retained, the excluded class is empty.

## 4. Why the certificates eventually separate from M

Suppose no positive separation is obtained as h tends to zero. Choose retained
pairs (V_n,omega_n) with areas tending to at least M. The containing box is compact;
extract Hausdorff convergence V_n->S_* and omega_n->omega_*. Nonemptiness and
connectedness pass to the limit. The approximate support/hallway conditions
pass through the dense angular samples by support continuity and boundedness.
The limiting set lies in the normalized horizontal strip, satisfies every
supporting hallway, and lies in the terminal unit strip.

The canonical-support motion construction used in SofaLimitMotion therefore
makes S_* an actual moving sofa. This step is why the terminal test and use of
h_V matter. It does not assume convergence of arbitrary original motion paths.
Area upper semicontinuity gives |S_*|>=limsup |V_n|>=M. Optimality and normalized
uniqueness identify S_*=G. But the retained distance test gives
d_H(S_*,G)>=eta/2, a contradiction.

Accordingly U_n is eventually bounded strictly below M. At each stage, compare
U_n with a certified lower enclosure M_n^- of Gerver's area, with M_n^-->M.
When U_n<M_n^-, the positive rational difference M_n^--U_n is a certificate
for (1). Monotonicity of U_n is not needed for this termination argument.

This is a theoretical convergent certificate scheme for a prescribed computable
neighborhood, conditional only on the established normalized-limit and uniqueness
results. It does not give a feasible complexity bound or a completed program.

## 5. Why this has not yet produced a numerical threshold

The brute-force state count is 2^(7*4^n), before the angle enumeration. The
scheme must be implemented with interval branch-and-bound, connectivity bounds,
area pruning, and support-extremum consistency to be practical. No such global
cover was executed here. The prior floating-point Q experiments do not provide
this certificate.

In addition, the desired eta and angle tolerance must be chosen within every
local cap/terminal/normal/cone certificate. Their positive reference scales
can be attacked by interval subdivision of the explicit finite reference arcs,
but the new sector and normal chart radii have not been numerically enclosed in
this continuation. The leading coefficients 2.3 and 4.22 do not depend on those
radii; the usable epsilon0 does.

Thus the status remains: explicit analytic coefficients, existential entry
threshold, and a substantially more precise route to an effective threshold.
There is no claim of a certified numerical epsilon0 or a global-in-deficit bound.
