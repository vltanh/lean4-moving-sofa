# Fixed net rotation angle: proof-exploration memo (PEM)

## Current status

**Closed at paper-proof level:** for every prescribed net rotation angle `0 <= omega <= 1` radian in the usual unit-width right-angled hallway,

`m(omega) = 1 + omega^2/2`,

and the normalized optimizer is unique. This includes arbitrary compact connected sofas and motions that backtrack, not just an injective monotone subclass. The proof also gives qualitative Hausdorff stability of near-maximizers at each fixed positive angle in this interval.

**Not closed:** the exact optimum and optimizer classification for `1 < omega < pi/2`. The new work proves a sharp boundary to the first regime: the unrestricted maximum is strictly below `1 + omega^2/2` there, and the actual sofa obtained from Baek's relaxed cap is itself strictly suboptimal. Its boundary must change; simply subtracting its extra niche area does not solve the remaining optimization.

The right-angle endpoint belongs to the companion Gerver optimality/uniqueness development, not to the new open-interval arguments. We do not present the full fixed-angle classification as complete.

These are paper proofs with explicit imported inputs, not independently refereed or Lean-checked theorems. No CI, workflow dispatch, Lean compilation, axiom audit, or TeX compilation was run. Every research commit uses `[skip ci]`. Changes remain under `docs/fixed-angle/`; Lean sources, workflows, and the original uniqueness manuscript are unchanged.

Starting reference: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`. Here PEM means proof-exploration memo.

## Problem and normalization

The hallway is `L = ((-infinity,1] x [0,1]) union ([0,1] x (-infinity,1])`. Feasibility at angle omega means a continuous motion whose angular lift starts at zero and ends at `-omega`. This is a prescribed **net** angle, not the minimum angle of a shape and not a change to the hallway corner.

For `0 < omega < pi/2`, the two upper endpoint supports uniquely translate a sofa into

`P_omega = { (x,y) : 0 <= y <= 1, 0 <= x cos(omega) + y sin(omega) <= 1 }`.

Write `u_t = (cos t,sin t)`, `v_t = (-sin t,cos t)`, and `F_omega = { y >= 0, z dot u_omega >= 0 }`. The cap functional is `A_omega(K) = |K| - |N_omega(K)|`. The niche uses the **fan**. For an arbitrary cap, niche containment and feasibility of the cap-minus-niche set are not automatic.

## The theorem assembly that closes the first regime

Read [optimality-uniqueness.tex](optimality-uniqueness.tex) for the assembly and equality recovery.

1. **Cap attainment.** The normalized cap class is Hausdorff compact inside the fixed parallelogram. Its defining normal set survives limits via the support-area measure. Niche area is lower semicontinuous by strict quarter-plane witnesses, hence the cap functional is upper semicontinuous. A positive competitor supplies a positive global cap maximizer. This proof does not invoke Gerver optimality.
2. **Reach every maximizer.** The companion's fixed-angle penalized selection and floating first variation approximate any prescribed positive maximizing cap with polygon caps whose total floating defect tends to zero.
3. **Fixed-angle curvature.** [fixed-angle-curvature.tex](fixed-angle-curvature.tex) proves the local wall estimate and weak-measure passage at arbitrary `0 < omega < pi/2`. The measure bounds include the outer endpoints `0` and `pi/2+omega`, excluding atoms there, while permitting the two pinned atoms.
4. **Arm bootstrap.** For `omega <= 1`, [arm-bootstrap.tex](arm-bootstrap.tex) gives the elementary three-step estimate `f(t) >= 1+t/2`, `g(t) >= 1+(omega-t)/2`. The integral inequalities follow from the curvature bounds and the now-justified endpoint values `f(0)=g(omega)=1`.
5. **Majorization without assumed fan containment.** [monotone-majorization.tex](monotone-majorization.tex) proves `|N(K)| >= I(x_K)` whenever the canonical corner's first coordinate strictly decreases. The proof retains nonnegative endpoint corrections for a curve outside the fan. The arm estimate supplies this horizontal monotonicity. Thus every global maximizing cap satisfies `A_omega <= A_1`.
6. **Sharpness and strict equality.** Baek's known relaxed cap has a directly verified feasible sofa of area `1+omega^2/2` when `omega <= 1`. The exact quadratic gap in [relaxation.tex](relaxation.tex) forces every maximizing cap to have the candidate's support functions.
7. **Recover every original sofa.** The candidate is regular closed, proved by the geometry of its niche and radial interior approximation. A closed subset of a regular-closed finite-area set with the same area equals that set. Applied to the monotone envelope, this gives uniqueness for arbitrary original sofas, without adding a regularity hypothesis to them.

The result is genuinely an optimality-plus-equality argument. No final Gerver area bound, right-angle equality theorem, assumed symmetry of the original optimizer, or unproved fan-containment hypothesis is used.

## Candidate and strict gap

The functional `A_1(K) = |K| - I(x_K)`, the cap `K_(omega,1)`, and its relaxed value `1+omega^2/2` are already in Baek, *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1. They are attributed to Baek, not claimed as discoveries here.

Put `c = sec(omega)-tan(omega)`, `o=(c,1)`. The active supports are

`p_*(t)=omega-t+o dot u_t`, `k_*(t)=t+o dot v_t`.

The cap is the convex hull of `O`, `o` and the arcs

`A(t)=o+(omega-t)u_t-v_t`, `C(t)=o+t v_t-u_t`.

The corner is `gamma(t)=o+(omega-t-1)u_t+(t-1)v_t`, with derivative `-t u_t+(omega-t)v_t`.

For support differences `F=p-p_*`, `G=k-k_*`, the exact relaxation gap is

`A_1(K_*)-A_1(K) = (1/2) integral [F'^2 + (G'+F)^2 - F^2]`.

For `omega <= 1`, the elementary one-ended estimate gives coercivity with coefficient `(1-omega^2/2)/2`. [beyond-one-radian.tex](beyond-one-radian.tex) uses the sharp one-ended Poincare inequality to improve it to `(1-4omega^2/pi^2)/2`, which stays positive for every `omega < pi/2`. Thus the normalized relaxed maximizer is unique throughout the whole open angle interval.

## Structural progress at every angle below pi/2

[all-angle-bootstrap.tex](all-angle-bootstrap.tex) replaces the short bootstrap by an exact finite rational certificate valid on every interval of length at most `8/5 > pi/2`. Twelve cells and eight integer recurrence steps give the lower bound `699/1000 > 2/3`, after which the same two substitutions give the linear arm bounds.

The certificate and its recurrence are printed in the paper. [checks/arm_certificate.py](checks/arm_certificate.py) independently checks it with integer and Fraction arithmetic; it is an optional local paper-certificate check, not CI.

Combined with the fixed-angle curvature theorem and the new signed-area argument, this proves `A_omega(K) <= A_1(K)` for **every positive global maximizing cap** at every `0 < omega < pi/2`. The majorization gap from the first research pass is therefore closed on the whole open interval. The remaining issue is sharpness of a stronger bound after one radian, not an unresolved injectivity premise for the old bound.

## Exact negative results

### Universal majorization is false

[negative-results.tex](negative-results.tex) gives the feasible convex monotone quadrilateral

`B_omega = conv{O, c u_0, (c,1), c v_omega}`.

Its niche is empty, its area is `c`, and `I(x_B)=omega+c-1>0`. Consequently

`A_1(B_omega)=1-omega < c=A_omega(B_omega)`.

Its open-arc arms vanish; curvature atoms at the two outer endpoints explain the failure. This disproves the tempting shortcut of applying the relaxation to every feasible or near-optimal cap without proving the needed geometry. It also verifies that the endpoint no-atom step is substantive.

### The sharp regime ends exactly at one radian

For the relaxed cap, put `r=omega+c-1` and let `W(t)` be the floor intercept of its inner b-wall. Then

`W(t)-r = ((omega-1)(1-cos t)+sin t-t)/cos t`.

When `omega > 1`, this is positive at sufficiently small positive t. A positive-area part of the niche therefore lies beyond the signed corner region. Hence `A_omega(K_(omega,1)) < 1+omega^2/2`. Cap attainment, all-maximizer majorization and strict relaxation rigidity turn this into the strict unrestricted supremal bound

`m(omega) < 1+omega^2/2` for `1 < omega < pi/2`.

This argument is in [beyond-one-radian.tex](beyond-one-radian.tex); it does not incorrectly pass from pointwise strictness to strictness of a supremum.

### The relaxed-cap sofa itself is suboptimal above one radian

[relaxed-candidate-feasibility.tex](relaxed-candidate-feasibility.tex) first proves that the cap-minus-niche sofa is feasible for every `omega < pi/2`: the whole niche lies in a disk of radius strictly less than one inside the fan, and radial paths connect its complement in the cap.

[redundant-angle-improvement.tex](redundant-angle-improvement.tex) then proves that a whole early interval of quarter-planes is strictly contained in a later quarter-plane when `omega > 1`. A small smooth outward bump of the cap support on that interval leaves the niche **exactly unchanged**, preserves convexity and feasibility, and increases area by

`epsilon integral (omega-t) psi(t) dt + (epsilon^2/2) integral (psi^2-psi'^2) dt > 0`.

Thus the actual relaxed-cap sofa is strictly suboptimal, not just smaller than its relaxed value. This is an analytic construction, not a numerical optimizer claim.

## Stability and earlier results

[stability.tex](stability.tex) proves that at each fixed `0 < omega <= 1`, every normalized sequence of feasible sofas whose areas tend to the optimum converges in Hausdorff distance to the unique optimizer. Their caps converge as well. This is a qualitative result with no asserted uniform rate.

The first-pass [paper.tex](paper.tex), [small-angle.tex](small-angle.tex), and [relaxation.tex](relaxation.tex) remain useful as independent component proofs and a record of the development. Statements in those files that say a particular note does not prove unrestricted optimality describe that note's own scope; the continuation now supplies the missing hypotheses. The small-angle expansion is superseded by the exact value theorem, while its rescaled missing-corner theorem remains a separate asymptotic geometric result.

## Remaining problem, stated without a false closure claim

The explicit optimal cap/sofa and uniqueness for `1 < omega < pi/2` are not yet determined by this PR. The first candidate is now ruled out throughout that interval. The exact tail correction to the relaxed objective must enter the next optimization.

Exploratory local support perturbations suggest that the niche-minus-signed-area correction may have useful convexity in restricted contact regimes, but no general convexity theorem is proved. Sampled unions of quarter-planes underestimate the niche and therefore overestimate the cap-minus-niche area; they cannot certify a feasible lower bound without a separate argument. Replacing the niche by its convex hull is also not an identity. These routes are not used as premises of any result above.

A productive next target is a sharp lifted functional or an exact exposed-wall/contact decomposition with a justified equality case. Merely reusing the quadratic relaxation, assuming its stationary cap remains optimal, or citing right-angle rigidity would contradict the negative results already proved.
