# Paper-proof review and failure log

This is an internal mathematical review, not an independent referee report or machine-verification certificate. No Lean, `lake`, CI, workflow dispatch, axiom audit, or TeX compilation was run. Every research commit uses `[skip ci]`. The papers should receive independent mathematical review before being promoted into the main manuscript.

## Current theorem boundary

The continuation supplies a complete written argument for unrestricted optimality and uniqueness on `0 <= omega <= 1`, plus qualitative Hausdorff stability at each fixed positive angle in that interval. It also proves the maximizing-cap majorization and strict relaxation kernel throughout `0 < omega < pi/2`.

For `1 < omega < pi/2`, the exact optimum and unique optimizer are **not** determined. What is established is the strict inequality below the relaxed value and a feasible strict improvement of the relaxed-cap sofa. The notes distinguish those two negative statements; the second does not follow merely from the first.

The first-pass `relaxation.tex` deliberately retains Baek's injectivity-and-fan hypotheses in its restricted theorem. The continuation does not delete a hypothesis from that theorem. Instead it proves a new direct signed-area majorization and supplies its geometric premise for every maximizing cap.

## Dependency audit

The main new theorem imports the companion's fixed-angle cap/monotonization identities, penalized selection, and floating first variation at commit `1ade045936f32cf76572ee668ed8aa1627772bde`. These inputs already quantify over the prescribed angle; the new proof does not infer them from a right-angle specialization.

The imported selection targets **any chosen positive maximizing cap**, not merely a selected balanced maximizer. This quantifier is what permits the equality analysis to classify all maximizers. Fixed-angle curvature, the arm certificate, signed-area comparison, compactness-based attainment, and equality recovery are written out in the new notes. Neither the final Gerver upper bound nor right-angle rigidity is used.

Baek's earlier *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, is credited for `A_1`, `K_(omega,1)`, and its relaxed value. Constructing a cap from a specified boundary measure is not confused with proving that it is the only relaxed maximizer; that conclusion comes from the strict quadratic gap.

## Definitions and quantifiers checked

- **Net angle:** angular lift starts at zero and ends at `-omega`; backtracking is allowed. Intermediate-angle exclusions use the intermediate value theorem.
- **Normalization:** two upper support equations fix one translation because `cos(omega)>0`. Width bounds imply containment in the endpoint parallelogram. Arbitrary sofas need not touch both lower walls.
- **Fan versus cap:** the niche is the fan intersected with the union of open quarter-planes. It is not silently truncated to the cap or parallelogram.
- **Feasibility:** explicit families have continuous motions, compactness and path-connectedness proofs. Their cap/niche area difference is treated as actual sofa area only after niche containment is established.
- **Suprema:** the elementary strict strip bound is uniform; the later strict larger-angle bound uses cap attainment. Pointwise strictness alone is never used to conclude a strict supremal bound.
- **Scope:** zero angle, the solved closed interval `[0,1]`, the unresolved interval `(1,pi/2)`, and the companion's right-angle endpoint are distinguished.

## Fixed-angle curvature audit

The local polygon argument is not a blind substitution of omega for pi/2.

1. The defining normal set includes the two pinned normals `omega` and `pi/2`. The local estimate is applied only at floating normals `i*delta`, `0<i<n`, with the corresponding shifted neighbors available as supporting lines.
2. The ray on an inner wall meets the two fan boundary rays in at most two points when `0<t<omega`; these exceptions have zero length. The right-angle proof's single floor exception is therefore replaced explicitly.
3. The endpoint excluded quarter-planes lie outside the fan: at zero one coordinate is below the floor, and at omega the other is below the second fan boundary. They can be used as neighbors without adding endpoint angles to the niche union.
4. The atom estimate retains the actual penalty error `e_j(t)`, whose **total**, not merely each pointwise value, tends to zero.
5. On each grid cell the relevant vertices are fixed, giving the diameter-times-step estimate for the arm function. This justifies the Riemann-sum passage even though the polygon arm functions have jumps at grid points.
6. Almost-everywhere convergence of support points follows from uniqueness of the limiting support point at almost every normal and Hausdorff convergence. The fixed parallelogram supplies the dominating diameter bound.
7. Weak convergence of boundary measures is obtained directly from `sigma = h+h''` against smooth tests.
8. Test functions cross normal zero. Proving only a bound on `(0,omega)` would leave an endpoint atom uncontrolled and would not justify `f(0)=1`. Reflection similarly excludes the atom at `pi/2+omega`; the two pinned atoms remain allowed.
9. The measure density is bounded because the arms are bounded. This yields continuous one-sided support derivatives on the closed parameter arcs and the correct endpoint traces, hence the absolutely continuous arm inequalities.

The quadrilateral counterexample in `negative-results.tex` tests this audit: it has endpoint atoms of mass one and zero interior arms. It would invalidate an argument that omitted item 8.

## Bootstrap and majorization audit

### Short bootstrap

For length at most one, the first substitution gives `f>=1-t`, `g>=1-omega+t`. The next gives `f,g>=2/3`, using the global minimum of `1-t+3t^2/4`. Subsequent substitutions give `f,g>=1` and then the linear bounds. Only monotonicity and the stated piecewise formula of `m` are used.

### All-angle rational certificate

The twelve-cell, eight-step table in `all-angle-bootstrap.tex` uses integer lower bounds divided by 1000. Every floor rounds downward. Its printed recurrence is independently reproducible with integer and Fraction arithmetic. The final minimum is exactly `699/1000`, which is greater than `2/3`.

The certificate is proved for every interval length at most `8/5`, not by assuming that an arbitrary intermediate lower primitive is monotone in the interval length. The proof uses the identity `1+(L/R)(H-1) >= min(1,H)` for `L<=R`, and clips all stored lower bounds at one. This handles both positive and negative partial integrals.

### Signed-area comparison

The corner is represented as a graph because its first coordinate strictly decreases. The included region is the vertical subgraph **above the fan floor**. Subtracting a vertical displacement decreases both wall coordinates strictly at interior angles.

The integration-by-parts identity retains both endpoint corrections:

`I = integral(Y-ell) - (cot(omega)/2) alpha_-^2 - (sin(omega)cos(omega)/2) beta_-^2`.

These signs are essential. Dropping the corrections or assuming the endpoints lie on the positive fan rays would reintroduce an unproved fan-containment premise. The resulting defect bound is nonnegative, and equality forces the whole curve into the fan by continuity. No differentiability of the inverse graph parameterization is assumed; a primitive of the continuous graph function justifies the change of variable.

## Strict equality and recovery audit

The support-area identity includes all normal-gap terms, in particular the constant `c=sec(omega)-tan(omega)`. The gap calculation uses the correct traces of the support differences, `F(omega)=0` and `G(0)=0`, and the candidate's free endpoint derivative conditions.

For angles through one, an elementary one-ended estimate makes the gap coercive. For all angles below pi/2, the sharp one-ended Poincare constant `4omega^2/pi^2` does so. Its ground-state proof is first given for smooth functions with the zero endpoint trace and then extended by H1 approximation. Strict positivity is asserted only for `omega<pi/2`.

Area equality of an original sofa with its envelope is not enough by itself to identify the sets. The candidate is proved regular closed: the radial fan edges below the two corner endpoints are in the niche, the outer corner arc is not, and every surviving point admits an interior approximation. A proper closed subset of a regular-closed finite-area set misses a positive-area ball. This recovers an arbitrary closed original sofa without assuming it was regular closed.

For Hausdorff stability, one need not prove feasibility of a subsequential Hausdorff limit of arbitrary sofas. Strict niche witnesses show that the limit is contained in the unique candidate. Upper semicontinuity of compact-set area and regular-closedness then identify it. This avoids an unnecessary motion-compactness assertion.

## Larger-angle negative constructions audited

The inner-wall intercept formula is exact. For `omega>1`, its numerator divided by `t^2` tends to `(omega-1)/2>0`, so a later quarter-plane strictly contains the entire initial floor segment. The early fan-truncated quarter-planes converge to that segment. Compactness gives a **uniform positive containment margin**, not just pointwise redundancy.

The support perturbation is a nonnegative smooth bump supported strictly inside the redundant interval. Its curvature perturbation remains nonnegative for sufficiently small amplitude because the original density `omega-t` has a positive minimum on the support. The entire circular support function is retained elsewhere, so pinned supports, normal gaps and closure of the convex boundary are preserved.

The niche is unchanged exactly: all changed quarter-planes remain inside a fixed unchanged one, while increasing a support cannot remove niche points. The positive first-order cap-area change is then computed from the support-area identity; no differentiation of an uncountable union is required.

Feasibility of both the original and improved sofas uses a separate result: for each fixed `omega<pi/2`, the entire original niche lies in a disk of radius strictly less than one inside the fan, while the cap contains the unit fan sector. The perturbation enlarges the cap and leaves that niche fixed. The same radial connectedness proof and canonical motion therefore apply.

## Local checks actually used in the continuation

Python's exact Fraction arithmetic checked all eight certificate rows, including the downward-rounding rule and final minimum. The integer recurrence was checked independently. The source `checks/arm_certificate.py` records both methods; it has no external dependencies and is not wired into CI.

SymPy checked the relaxed candidate's corner derivative and the exact floor-intercept identity. Earlier first-pass symbolic checks covered the stationary equations, Taylor expansions and the limiting niche area `5/24`. None of these calculations replaces a geometric hypothesis in the paper proof.

Exploratory finite unions of sampled niche quadrilaterals were used to test support perturbations and possible convexity of the tail correction. They **underestimate** the true niche area and hence **overestimate** the corresponding cap-minus-niche area. At coarse resolution this even obscured the small positive tail near one radian. Adding an inscribed approximation of the known corner region reduced that sampling error but did not turn the computation into a rigorous enclosure. No sampled area is used as a certified feasible improvement; the improvement theorem is analytic.

## Failed or unproved routes, retained deliberately

- **Apply `A_1` to every feasible cap:** false, with an exact convex feasible counterexample.
- **Infer fan containment from injectivity alone:** not justified; replaced by the signed-area proof with endpoint corrections.
- **Ignore endpoint curvature atoms:** false; the same counterexample shows why the endpoint traces then fail.
- **Continue the relaxed stationary cap past one radian:** false as an optimality claim; a strict feasible improvement is proved.
- **Infer actual candidate suboptimality solely from non-sharp relaxed value:** logically invalid; the separate redundant-angle perturbation supplies the missing proof.
- **Infer a strict supremal upper bound from strictness for individual caps:** invalid without a uniform gap or attainment; the cap compactness proof supplies attainment.
- **Replace the niche by its convex hull:** not an identity and not used.
- **Assume convexity of `|N|-I(x_K)` from a few perturbation tests:** unproved. The exploratory tests do not establish it on any complete admissible class.
- **Invoke right-angle rigidity after extending a motion:** changing the feasible class does not preserve maximizing status.

The remaining exact larger-angle optimization must address the exposed-wall/tail correction. No candidate formula or uniqueness theorem for that interval is asserted by this review.
