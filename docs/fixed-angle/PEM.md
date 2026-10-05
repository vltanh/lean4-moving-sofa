# Fixed rotation angle: proof-exploration memo (PEM)

## Scope and status

This workstream studies a prescribed **net rotation angle** in the existing unit-width, right-angled hallway. It does not change the hallway angle. A shape may admit several net rotation angles; feasibility at angle omega means it has a motion with that net angle, not that omega is its minimum possible rotation.

Starting point: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`. The work is separate under `docs/fixed-angle/`; the uniqueness manuscript, Lean sources, and workflows are unchanged. Here PEM means proof-exploration memo.

No CI, workflow dispatch, Lean compilation, or axiom audit was run. Every research commit carries `[skip ci]`. The TeX sources were not compiled. These are paper proofs for review, not machine-checked theorems. See [REVIEW.md](REVIEW.md) for the mathematical audit and the limits of the exploratory checks.

**The exact unrestricted optimizer and its uniqueness at positive angles are not yet established.** The first research pass supplies unrestricted asymptotics, an explicit exact-area feasible family, a strict relaxation equality case, and a precise restricted-class optimization theorem.

## Definitions

Let `L = ((-infinity,1] x [0,1]) union ([0,1] x (-infinity,1])`. Let `m(omega)` be the supremum of areas of nonempty compact connected sets admitting a continuous motion in L whose angular lift starts at zero and ends at `-omega`. Backtracking is allowed.

For `0 < omega < pi/2`, the two upper endpoint supports uniquely normalize a sofa into

`P_omega = { (x,y) : 0 <= y <= 1, 0 <= x cos(omega) + y sin(omega) <= 1 }`.

Write `u_t = (cos t, sin t)`, `v_t = (-sin t, cos t)`, `F_omega = { y >= 0, p dot u_omega >= 0 }`, and `J_omega = [0,omega] union [pi/2,pi/2+omega]`.

The cap functional remains `A_omega(K) = |K| - |N_omega(K)|`, using the **fan**, not the parallelogram, in the niche. For an arbitrary cap this difference must not silently be identified with the area of a connected feasible sofa.

## Important correction to the initial research direction

The first memo proposed searching for a fixed-angle quadratic majorant and candidate. A primary-source check found that Baek's earlier paper, *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1 (2024), already gives

`A_1(K) = |K| - I(x_K)`,

its explicit maximizing cap `K_(omega,1)`, and the maximum relaxed value `1 + omega^2/2` (Definition 5.1, Definition 5.12, Theorems 5.30 and 5.32). The relaxation and candidate are therefore attributed to Baek, not presented as new discoveries here.

The important qualification is Theorem 5.5: converting `A_1` into a sofa-area upper bound requires an injective canonical inner-corner curve lying in the fan. Finding a candidate is not the current bottleneck in the small-angle regime. The bottleneck is proving the majorization for the relevant unrestricted maximizers.

## Results now written

### 1. Elementary all-angle bounds and the zero-angle equality case

[paper.tex](paper.tex) proves `m(0) = 1`, with the square unique in the fixed initial orientation up to translation. For `0 < omega < pi/2` it constructs the feasible corner-rotation body

`C_omega = F_omega intersect { p dot u_t <= 1 : t in J_omega }`,

of area `omega + tan(pi/4 - omega/2)`, and proves a quantitative uniform strict upper bound

`m(omega) <= sec(omega) - d(omega) < sec(omega)`

with an explicit `d(omega) > 0`. This avoids taking a supremum of merely pointwise strict inequalities.

### 2. Unrestricted small-angle asymptotics and limiting-defect rigidity

[small-angle.tex](small-angle.tex) proves

`m(omega) = 1 + omega^2/2 + o(omega^4)` as `omega -> 0+`.

The lower argument verifies directly that the corner-carved parallelogram `P_omega minus N_omega(P_omega)` is compact, path-connected, and feasible for `0 < omega <= pi/4`. The upper argument applies to arbitrary near-maximizers: a missing-triangle estimate forces all relevant support deficits to be `o(omega^2)`, so every such sofa must omit the same limiting corner.

More precisely, for normalized sofas `S_n` at `omega_n -> 0+` with area deficit from `m(omega_n)` equal to `o(omega_n^4)`, the spatially rescaled missing sets

`omega_n^(-2) (P_(omega_n) minus S_n)`

converge in symmetric-difference area to

`D_0 = { x >= 0, y >= 0, x+y+(x-y)^2 < 3/4 }`, of area `5/24`.

This is an asymptotic equality/rigidity theorem, not exact optimizer uniqueness or a Hausdorff-convergence claim.

### 3. Exact feasible family and a strict relaxation equality case

[relaxation.tex](relaxation.tex) proves that Baek's relaxed cap produces a feasible monotone sofa `S_*` for `0 < omega <= 1` radian, with **exact** area `1 + omega^2/2`. Thus

`m(omega) >= 1 + omega^2/2`

unconditionally in that interval. In the normalization `o = (sec(omega)-tan(omega), 1)`, its active supports are

`p_*(t) = omega-t + o dot u_t`,
`k_*(t) = t + o dot v_t`.

The explicit corner curve is

`gamma(t) = o + (omega-t-1)u_t + (t-1)v_t`,
`gamma'(t) = -t u_t + (omega-t)v_t`.

The proof verifies cap geometry, injectivity, fan containment, the absence of extra niche tails, connectedness, and the continuous motion. No candidate feasibility is inferred merely from solving the stationary equations.

For any other normalized cap, put `f = p-p_*`, `g = k-k_*`. The note derives the exact gap

`A_1(K_*) - A_1(K) = (1/2) integral [f'^2 + (g'+f)^2 - f^2]`,

and the lower bound

`(1/2)(1-omega^2/2) integral f'^2 + (1/2) integral (g'+f)^2`.

For `omega <= 1` this is strictly positive unless both support differences vanish. It proves uniqueness of the normalized **relaxation** maximizer, not just uniqueness of a cap specified by a chosen boundary measure.

Applying Baek's Theorem 5.5 then proves that `S_*` is the unique normalized optimum **among monotone sofas whose canonical corner curves are injective and lie in the fan**. The exact unrestricted upper bound is not supplied by this conditional application.

## Dependency audit

- Endpoint normalization and monotonization preserve the specified angle; see the companion's `02-setting.tex`, Facts `fact:angle` and `fact:monotone`.
- Fixed-angle existence and comparison are Baek's corrected Theorems 3.5.2--3.5.6. They should be separated from the companion's `fact:optimal`, which also packages the final Gerver theorem. The asymptotic proof avoids needing existence altogether.
- Penalized selection in `04-selection.tex` already treats a prescribed positive-area cap maximizer at arbitrary `omega in (0,pi/2]`. It is reusable, but it does not by itself identify the cap or prove the conditional majorization.
- Fixed-angle pinned-variation estimates and right-angle curvature/injectivity estimates must not be conflated. Audit their actual angle and area hypotheses.
- Extending a motion to pi/2 does not make the shape a pi/2 maximizer. A right-angle equality theorem cannot therefore be applied to an arbitrary fixed-angle maximizer as though it had Gerver's area.
- Unique endpoint normalization removes translations only. It neither rules out noncongruent maxima nor proves that reflection fixes a maximizing shape.
- `relaxation.tex` imports the standard cap endpoint geometry, with a source citation, and explains the support-area identity by smooth approximation. Its restricted-class theorem explicitly imports Baek's injectivity/fan majorization. Its direct feasibility theorem does not.

## Completion of the first pass

- [x] Isolate the angle convention and audit dependencies.
- [x] Write a paper proof of an explicit competitor, strict strip bound, and zero-angle uniqueness.
- [x] Prove feasibility and area asymptotics of the corner-carved parallelogram.
- [x] Prove the matching upper asymptotic for arbitrary near-maximizers.
- [x] Prove uniqueness of the limiting missing-corner region in measure.
- [x] Locate and attribute the existing fixed-angle relaxation and candidate.
- [x] Prove candidate feasibility and exact area for `0 < omega <= 1`.
- [x] Prove a strict relaxation gap and restricted-class optimality plus uniqueness.
- [x] Record an adversarial paper review and the limits of local symbolic/numerical checks.
- [ ] Remove the conditional majorization hypothesis for unrestricted maximizers in a proved angle interval.
- [ ] Complete equality recovery from a maximizing envelope to an arbitrary original sofa.
- [ ] Classify the larger-angle regimes without assuming a phase diagram.

## Next mathematical target

The most economical target is **not necessarily full injectivity as a standalone theorem**. It is the inequality

`A_omega(K) <= A_1(K)`

for global fixed-angle maximizing caps in a justified interval. Injectivity plus fan containment is one sufficient route; a direct signed-area/niche inequality would also suffice.

For the global optimum value, one needs this for some global maximizing monotone envelope, plus a valid existence/comparison theorem. For global uniqueness by the same argument, one needs it for every maximizing envelope, then a regular-closedness/equality recovery argument for the original sofa. The strict relaxation gap and the feasible candidate already provide the rest of the sandwich.

The small-angle estimates offer a quantitative starting point: `O(omega^4)`-near-full area forces relevant supports within `O(omega^(5/2))` of the parallelogram. This is a support-value estimate, not derivative control; it does not automatically make the inner-corner curve injective. The next variation argument must address that distinction.

No Lean placeholders should be introduced until these paper-level obligations are settled.
