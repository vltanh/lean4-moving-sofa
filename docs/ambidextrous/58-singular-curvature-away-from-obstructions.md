# 58. Singular-continuous curvature also admits an improving replacement at clear contacts

This extends the maximizer-specific operation of Note 56, not the protected-candidate neighborhood theorem. At a nonatomic singular-curvature point, a short circular replacement gains hull area of order m(r)^2 r, while the changed corner costs at most order m(r) r^2. At singular-density scales m(r)/r tends to infinity, so the gain dominates.

The strict outer-contact and fiber-clearance conditions are retained explicitly. This note does not eliminate singular curvature at obstructed or coincident contacts, and it does not prove the unrestricted curvature cap.

## 58.1 A local mass condition with an improving scale

Let sigma=h+h'' be the curvature measure of a compact convex hull K, and let t_0 be a nonatomic normal in the interior of a floating angular interval. Suppose there are radii r_j decreasing to zero such that, with

\[
J_j=[t_0-r_j,t_0+r_j],\qquad
m_j=\sigma([t_0-r_j/2,t_0+r_j/2]),
\]

\[
\sigma(J_j)\leq4m_j,\qquad m_j/r_j\longrightarrow\infty.
\tag{58.1}
\]

Because t_0 is nonatomic, sigma(J_j) tends to zero. The original support derivative has the same two traces at t_0 and hence the exposed face there is a single point

\[
P_0=h(t_0)\mu_{t_0}+h'(t_0)\nu_{t_0}.
\]

For each radius replace h on J_j by the solution f_c of f_c''+f_c=1 with the old endpoint values, leaving the rest of the circle unchanged. Write u=f_c-h on J_j and zero elsewhere. We will use r<pi/4 and m>=16r, which hold at all sufficiently small scales in (58.1).

**Lemma 106 (mass-controlled circular replacement).** The replacement is a convex support function h_c>=h. For absolute constants c,C>0,

\[
u(t_0)\geq mr/16,\qquad
\|u\|_\infty\leq Cmr,\qquad
\|u'\|_{L^\infty(J)}\leq Cm,
\tag{58.2}
\]

and

\[
|K_c|-|K|\geq c m^2r.
\tag{58.3}
\]

The derivative norm in (58.2) is an almost-everywhere bound, also bounding the one-sided traces; no absolute continuity of the original curvature is assumed.

**Proof.** Use the positive Green kernel G for -d^2/dt^2-1 on J from Note 56. For s in the middle half of J and every t in J,

\[
G(t,s)\geq\tfrac14G(t,t_0).
\]

This follows from its two sine factors: on either side of s and t_0 the relevant ratio is at least sin(r/2)/sin(r)>=1/2, and if t lies between them the additional ratio is at least one. The smaller constant 1/4 is sufficient. Also, by the explicit constant-forcing solution,

\[
\int_JG(t,s)\,ds\leq2\sin r\,G(t,t_0)\leq2rG(t,t_0).
\]

Indeed the integral is cos(t-t_0)/cos(r)-1, and division by G(t,t_0)=sin(r-|t-t_0|)/(2cos r) gives at most 2sin r. Since u=G*(sigma-dt), (58.1) yields

\[
u(t)\geq(m/4-2r)G(t,t_0)\geq(m/8)G(t,t_0)\geq0.
\]

As G(t_0,t_0)=tan(r)/2>=r/2, this proves the first bound. The kernel satisfies sup|G|<=Cr and its one-sided t-derivatives are bounded by an absolute constant on intervals with r<pi/4. Integrating against sigma+dt, whose mass is at most 4m+2r, proves the other bounds.

The endpoint gluing argument in Lemma 103 applies because u>=0 and u vanishes at both endpoints. Its inward one-sided derivatives have the signs that add nonnegative endpoint curvature atoms. In the interior the new curvature is exactly dt. Thus h_c is a convex support and K_c contains K.

Pairing u with u''+u=dt-sigma on J, with zero endpoint values, gives

\[
\int_Ju\,d\sigma=\int_Ju+\int_Ju'^2-\int_Ju^2.
\]

This is integration by parts for an H^1 function whose derivative has bounded variation; endpoint atoms contribute zero because u=0 there. The exact support-area expansion is consequently

\[
|K_c|-|K|=\int_Ju-\tfrac12\int_Ju^2+\tfrac12\int_Ju'^2.
\]

For small r, ||u||_infinity<=2, so the first two terms have nonnegative sum. Cauchy-Schwarz on each half interval gives

\[
\int_Ju'^2\geq2u(t_0)^2/r.
\]

Combining these estimates proves (58.3), for example with c=1/256. QED.

## 58.2 The complete niche cost is smaller than the hull gain

Consider first a first-quarter change in the lower turn. The wall-family and corner-band arguments of Sections 56.2–56.3 apply to the same replacement, without an atom at the center. The R supremum on J is exactly preserved and L is unchanged.

The old and new corner abscissae over J lie in an interval I_r of length at most Cr. To see this, the original corner is Lipschitz because the support functions are Lipschitz, and the changed corner differs by u mu. Its uniform displacement is O(mr)=o(r). The new roof equals the old roof outside I_r and rises by at most Cmr inside it. Therefore

\[
\text{lost old surviving area}\leq C m r^2.
\tag{58.4}
\]

This estimate uses the actual max-min roof. It is not a signed-area approximation and does not posit a fixed contact pattern. The other quarter and reflected turn have the identical estimate after exchanging the two wall families or reflecting coordinates.

## 58.3 When all the new hull area survives

Assume P_0 is disjoint from the closures of both swept niches. Since the exposed face at t_0 is a single point, every face at a normal in J converges to P_0 as r decreases to zero. One direct proof takes a convergent subsequence of points in those faces and passes their supporting equality to the limiting normal; uniqueness of its face identifies the limit.

Every point z in K_c minus K has a nearest point p in K with an outer normal in J. Otherwise the support in that normal would be unchanged, contradicting z dot n>h_K(n). Its distance from K is at most ||u||_infinity. Thus **all** added hull area lies in a shrinking neighborhood of P_0 and avoids the two old niches for small r.

It also avoids the changed niche. If P_0,x differs from the old corner abscissa x_0=c_x(t_0), the added hull is outside I_r for small r, where the roof is unchanged. If these abscissae are equal, then

\[
(P_0-c(t_0))\cdot\mu_{t_0}=1
\]

implies P_0,y-c_y(t_0)=1/sin(t_0)>1. Since P_0,y<=1, the old corner lies strictly below y=0. All old and new corners in J then remain below the strip for small r, so their downward forbidden quadrants have no part in the strip at all. In that case there is no new niche loss anywhere in K_c.

For a second-quarter wall use its normal nu_t in the same argument, obtaining the vertical difference 1/cos(t)>1. The upper turn is its reflected version. Thus strict outer clearance suffices to retain all the added hull area; an artificial assumption separating those two abscissae is unnecessary.

## 58.4 The geometric admissibility condition

Let S be a compact connected canonical saturation in K, with correctly signed complete motions possibly ending at partial angles. The replacement window must avoid every normal that fixes an incoming or outgoing strip width. Assume P_0 has the strict outer clearance above. In addition assume one of the following:

- the changed lower corners are strictly below the incoming strip at t_0 (or the reflected upper version holds);
- x_0 is outside the horizontal projection of K;
- on a neighborhood of x_0, all surviving fibers over the projection of K have length at least some eta>0.

These conditions ensure the new full envelope is connected: outside I_r old fibers are retained, and inside it any positive uniform gap is reduced by only O(mr); in the below-strip case there is no loss. Its projection is unchanged because the axis supports are unchanged. All endpoint widths are unchanged as well. Consequently the new full envelope S_c is a compact connected feasible body for the same endpoint angles.

**Theorem 107 (non-atomic singular-density improvement).** Under (58.1) and the geometric conditions in this section, S cannot be globally maximizing. For sufficiently small chosen radii the replacement gives

\[
\boxed{|S_c|-|S|\geq c m^2r-Cmr^2>0.}
\tag{58.5}
\]

**Proof.** Section 58.3 retains the whole added hull area from Lemma 106. Equation (58.4) bounds every possible lost point of the old body. Their difference gives the first inequality. The second follows from m/r tending to infinity. The preceding fiber and endpoint argument establishes genuine two-motion feasibility and connectedness, not merely an area calculation for a disconnected relaxation. QED.

## 58.5 Why the local mass condition applies to singular-continuous curvature

The only external measure-theory input in this paragraph is the standard differentiation theorem for locally finite Radon measures on the line. A precise primary statement is [Besicovitch.ae_tendsto_rnDeriv in the mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Covering/Besicovitch.html#Besicovitch.ae_tendsto_rnDeriv): the ratio of two measures on shrinking centered closed balls tends to their Radon-Nikodym density. Reading this statement does not constitute a Lean verification of the present result; no compilation was performed.

Apply it to Lebesgue measure with respect to sigma. On the singular part of sigma the density is zero. Hence at sigma-singular-almost every t_0,

\[
\sigma([t_0-r,t_0+r])/(2r)\longrightarrow\infty.
\]

After removing atoms, these are nonatomic points. Arbitrarily small r satisfy the doubling inequality sigma(B_r)<=4sigma(B_{r/2}). Otherwise, at all sufficiently small dyadic scales the reverse strict inequality would give sigma(B_{r/2^k})<4^{-k}sigma(B_r), contradicting the preceding infinite-density limit after division by r/2^k. At the good scales the central mass divided by r also tends to infinity. Thus (58.1) holds.

Consequently the singular-continuous curvature of a maximizing hull gives zero mass to the set of floating normals satisfying the strict outer-contact and fiber-clearance conditions of Section 58.4. Together with Theorem 105, this excludes both atoms and singular-continuous curvature from the corresponding unobstructed geometry.

This is not yet global absolute continuity: coincident/masked outer contacts, pinching fibers, and pinned endpoint normals remain outside these conclusions. It is also not the sharp density cap rho<=1 for the remaining absolutely continuous measure. Those are separate unresolved parts of the unrestricted structural theorem.

Only pen-and-paper estimates and the cited standard measure differentiation theorem were used. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
