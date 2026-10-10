# Height saturation and continuous finite-angle approximation for signed caps

This note supplies the compact approximation needed for an actual maximizing-cap variation, rather than assuming that a numerical polygon optimum represents the continuous problem. The domain extends PA.1 temporarily to all nonempty compact convex, downward-closed subsets of a fixed strip, with height at most one. The niche remains the full positive-height union, not clipped surviving area. Labels HV are local.

## 1. A subunit-height cap can be improved

Let U have horizontal projection I=[l,r], width W>0, and height H<1. For 0<e<1-H put

$$U_e=U+[0,e]e_y.$$

It is a cap of the same width and height H+e. Its area increases by eW. For every upward normal its support increases by e sin(theta), so each lower-turn forbidden quadrant translates vertically by e. The untruncated sweep consequently translates by the same vector. Its section at any fixed x is a downward half-line (possibly empty or the whole line), so intersecting it with y>=0 changes its section length by at most e. All relevant positive sections are finite by the following estimate.

If (x,y) belongs to N(U_e), the outer rectangle bounds on the two supports give

$$
x-l>\frac{1-(H+e)\cos t}{\sin t}\ge d_e,
\qquad r-x>\frac{1-(H+e)\sin t}{\cos t}\ge d_e,
\qquad d_e=\sqrt{1-(H+e)^2}>0.
$$

The last bounds follow by minimizing the elementary quotients, or by Cauchy--Schwarz. Thus the positive niche projection has length at most (W-2d_e)_+. Since the niches grow under vertical extrusion,

$$
|N(U_e)|-|N(U)|\le e(W-2d_e)_+.
$$

**Lemma HV1 (strict height saturation).** For every width penalty lambda, which is unchanged by this operation,

$$
\boxed{\Psi_\lambda(U_e)-\Psi_\lambda(U)
\ge e\min(W,2d_e)>0.}
$$

In particular a positive global maximum of Psi over caps of height at most one must have height exactly one. A cap of zero horizontal width has nonpositive objective and cannot supply the positive maximum PA2. This extends PA2's value to the larger height-at-most-one domain without assuming that height is automatically pinned under every variation.

The same argument applies to a finite set of interior hallway angles: its untruncated union also translates, and the displayed support estimates still hold.

## 2. Continuity of full niche area on a bounded cap class

Fix R>0 and let K_R be all nonempty compact convex downward-closed subsets of [-R,R] times [0,1]. This class is compact in Hausdorff distance. Downward closure and the strip constraint pass to limits. Degenerate caps are retained for compactness.

All full niches lie in [-R,R] times [0,R]: the two wall inequalities imply their x-coordinate is strictly between the cap's extreme abscissae, and the corner-height estimate gives y<W/2<=R. Support functions converge uniformly under Hausdorff convergence.

**Lemma HV2 (niche-area continuity).** If U_j converges to U in K_R, then |N(U_j)| converges to |N(U)|.

**Proof.** At any point of N(U) with y>0, one interior angle witnesses strict inequalities, so that point belongs to N(U_j) eventually. Conversely, suppose a point p with y>0 belongs to infinitely many N(U_j). Along a subsequence choose witnessing angles t_j and take a limit t in [0,pi/2]. An endpoint is impossible: at t=0 or pi/2 one limiting inequality gives y<=height(U)-1<=0. Thus t is interior, and p satisfies both non-strict limiting inequalities. Subtracting any sufficiently small positive multiple of e_y makes both strict. Hence p lies in the closure of N(U).

Above y=0, the closure of N(U) adds only the upper endpoint of each nonempty vertical section. To see this, take a sequence of sweep points tending to p with y>0 and repeat the compact-angle argument; p-e e_y belongs to N(U) for every sufficiently small e>0. The section endpoints form a planar null set by Fubini. The sweep and its closure are measurable. Therefore the indicators converge almost everywhere outside this null boundary and y=0. Dominated convergence in the fixed bounding rectangle gives the assertion. QED.

Convex area and horizontal width are continuous on K_R as well (including zero-area limits). Consequently Psi is continuous on this bounded cap class. This strengthens PA.5's sufficient upper-semicontinuity statement; it does not compute its maximum.

## 3. Uniform dyadic approximation

Let n=2^k>=2, delta=pi/(2n), and let N_n(U) use just the lower-turn angles j delta, 1<=j<n. For fixed n its area is continuous in U: it is the area of a finite union of triangles whose bounding lines depend continuously on finitely many supports; alternatively apply the preceding indicator argument with a fixed finite list of angles.

The angle sets are nested, and their union is dense. Since the defining inequalities are strict and continuous in the angle,

$$N_n(U)\uparrow N(U),\qquad |N_n(U)|\uparrow|N(U)|.$$

The convergence of areas is uniform for U in K_R. Here is the compactness proof rather than an assumed discretization error rate. If not, choose U_j and increasing mesh indices n_j with discrepancy at least eps>0. Pass to U_j -> U. For any fixed mesh m and n_j>=m, monotonicity gives

$$
|N(U_j)|-|N_{n_j}(U_j)|\le |N(U_j)|-|N_m(U_j)|.
$$

Pass to the limit using continuity and then take m to infinity. This contradicts eps>0.

Thus, with the exact, nonnegative number

$$e_n=\sup_{U\in K_R}(|N(U)|-|N_n(U)|),$$

we have e_n -> 0 and

$$
\boxed{\Psi(U)\le F_n(U):=|U|-|N_n(U)|-W(U)/2\le\Psi(U)+e_n.}
\tag{HV.1}
$$

These numbers are not claimed computable at a particular rate by this proof. A finite algorithm seeking a numerical certificate would still need explicit error bounds or complete exact covering.

## 4. Why this is directly useful

HV1 permits variations in a height-at-most-one cap domain without silently assuming that the top supporting line stays active. HV2 and HV.1 justify selecting polygonal maximizers for the signed objective. They do not justify optimizing the clipped objective in the imported script and calling it Psi.

Only pen-and-paper arguments are used here. Compactness of bounded convex bodies, elementary support convergence and dominated convergence are the standard inputs. No CI, Lean/Lake compilation, optimization run or interval certificate is used. These are self-reviewed proofs, not an independent audit of the earlier branch.
