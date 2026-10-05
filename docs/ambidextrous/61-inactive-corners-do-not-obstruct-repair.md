# 61. A pinching fiber is irrelevant when the changed corner is inactive

The clearance conditions in Notes 56 and 58 can be weakened without a smoothness assumption. A zero-length surviving fiber does not automatically obstruct a local support change. The obstruction matters only when the changed corner reaches that fiber.

This note uses the circular replacements and corner-band identity already proved in those notes. It proves a containment-preserving case: the new constraints remove no point of the old saturated body at all. The argument is global with respect to candidate location and allows partial endpoint angles.

## 61.1 Strict inactivity is witnessed by one fixed constraint

Let K be a common hull in the incoming strip, and let S be its connected canonical saturation for correctly signed motions. Consider a first-quarter lower-turn support change about an interior floating angle t_0. Put

\[
x_0=c_x(t_0),\qquad y_0=c_y(t_0).
\]

Assume x_0 is in the interior of the horizontal projection of K. Let

\[
\lambda_S(x_0)=\min\{y:(x_0,y)\in S\}
\]

be its lowest surviving point on that fiber. Because the lower quadrant at t_0 is one of the constraints, lambda_S(x_0)>=y_0.

**Lemma 111 (strict inactivity has a fixed lower witness).** If

\[
\lambda_S(x_0)>y_0,
\tag{61.1}
\]

then there are a neighborhood U of x_0 and a number delta>0 such that every (x,y) in S with x in U satisfies y>=y_0+2delta.

**Proof.** A saturated vertical fiber has lower endpoint equal to the maximum of the convex hull's lower boundary and the thresholds of the lower forbidden quadrants, including the incoming lower strip bound. The upper sweep only imposes upper thresholds and does not alter this description when the fiber is nonempty.

If the hull's lower boundary at x_0 exceeds y_0, take a nonvertical supporting line to the lower boundary there. Such a line exists at an interior projection coordinate; convexity of that boundary gives an affine lower bound attaining its value at x_0. Continuity of this line supplies the required neighborhood and margin.

Otherwise some fixed lower constraint has threshold strictly above y_0 at x_0, by the definition of a supremum. At any angle strictly between 0 and pi/2 its threshold is min(R_t(x),L_t(x)), a continuous function of x. This includes a partial terminal angle alpha<pi/2: such a terminal constraint is not discarded. Only the axis-angle quadrants at 0 and pi/2 have no positive-height part above the incoming baseline; the baseline itself can be used when it supplies the strict gap. Shrink the neighborhood and choose delta so that the chosen fixed bound remains above y_0+2delta. Every point of S satisfies that bound. QED.

The proof does not assume continuity of the entire swept envelope, and does not assume that the fiber length is positive. The fiber can be a single point strictly above the inactive corner.

## 61.2 The short support replacement leaves the old body intact

Use a circular replacement on J_r=[t_0-r,t_0+r] from Note 56 (an atom) or Note 58 (a nonatomic singular-density scale). The support is unchanged outside J_r, is raised by u>=0 inside it, and u tends uniformly to zero. The new corner range and the old corner range lie in a band I_r shrinking to x_0.

**Proposition 112 (no old-body loss under strict corner inactivity).** Under (61.1), for all sufficiently small replacement scales,

\[
S\subseteq E_{K_c},
\tag{61.2}
\]

where E_{K_c} is the full new canonical envelope for the same endpoint angles.

**Proof.** Lemma 104 and its use in Note 58 give exact equality of the old and new lower roofs outside I_r. On I_r, every altered quadrant has threshold at x equal to its corner height plus the minimum of two linear terms in x-c_x(t). The two slopes are uniformly bounded because J_r stays in a compact interior angular interval. The corner heights tend uniformly to y_0 and the band shrinks to x_0. Consequently the thresholds of all altered quadrants on I_r are at most y_0+delta for sufficiently small r.

Lemma 111 says all old body points there have height at least y_0+2delta. They therefore satisfy every changed lower constraint. Outside the band they satisfy the unchanged roof; all opposite-turn constraints are unchanged. The outer hull only enlarges, and all pinned endpoint supports were excluded from the replacement window. This proves (61.2). QED.

No rate comparison is needed here. The strict inactive-corner margin makes the entire possible loss vanish, even if that band contains pinching fibers.

## 61.3 Consequence for maximizing singular curvature

If, in addition, the edge subsegment used in Theorem 105 is strictly clear of both old sweeps, its added triangular region still survives. Since (61.2) preserves the old body, no fiber-clearance assumption is required for this version of the atomic improvement.

Likewise, at a nonatomic singular-density point whose exposed point is strictly clear of both sweeps, Note 58 retains the added hull region. Its gain is at least c m(r)^2 r, and (61.2) makes the old-body loss zero in this case. Again no positive fiber-gap assumption is necessary.

Connectedness is not inferred just from area. The old S is retained, the horizontal projection remains the same because the axis supports are unchanged, and every new vertical fiber is an interval containing a point of the old S. The compact interval-fiber argument from Theorem 26 gives a connected new envelope. The endpoint angles and complete two-turn feasibility are unchanged.

**Corollary 113 (strictly inactive corners cannot protect clear singular curvature).** Under the outer-clearance and floating-normal hypotheses of Theorem 105 or 107, a global maximizer cannot have the corresponding singular curvature when (61.1) holds, even if a surviving fiber in the corner band has zero length.

**Proof.** Use Proposition 112, the positive added-area region in the cited replacement, and the preceding connectivity argument. The result is a strictly larger feasible connected body. QED.

The second-quarter and upper-turn versions follow by exchanging the two roof families or reflecting the vertical coordinate. For an upper-turn change, strict inactivity means that the changed corner lies strictly above the old highest surviving point, not below it.

## 61.4 Exact scope of the zero-gap observation

When the old fiber at x_0 is collapsed, strict inactivity leaves no obstruction by the preceding proof. The remaining collapsed-fiber case has

\[
\lambda_S(x_0)=y_0
\quad\text{and}\quad
\max\{y:(x_0,y)\in S\}=y_0.
\]

That is, the changed corner itself is the pinching point. An unrelated inactive corner sharing the same horizontal coordinate is not an obstruction. Turning positivity of the fiber at one point into a uniform neighborhood gap is a separate continuity assertion; it must not be inferred solely from compactness. Note 63 supplies that assertion for these canonical envelopes.

Note 62 treats an actual pinching point when a nonparallel affine ceiling is available. Corner/corner pinches and parallel degeneracies are not assumed away.

This is a continuation of the global structural argument, not a new candidate-local result. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
