# Fixed rotation angle: proof-exploration memo (PEM)

## Scope and status

This is a paper-first research workstream for a prescribed **net rotation angle** in the existing unit-width, right-angled hallway. It is not the problem of changing the hallway angle. A shape may admit several net rotation angles; membership at angle omega means that it admits a motion with that angle, not that omega is its minimum possible rotation.

Starting point: branch `paper/uniqueness-arxiv`, commit `1ade045936f32cf76572ee668ed8aa1627772bde`. Keep the current uniqueness manuscript and all Lean files unchanged. This directory is a separate research note. Here PEM means proof-exploration memo.

No CI, workflow dispatch, Lean compilation, or axiom audit is part of this workstream. Every research commit carries `[skip ci]`. New statements in this directory are paper mathematics, not machine-checked theorems.

The long-term goal is to determine the fixed-angle optimum and its equality cases. **Neither an explicit optimizer for every positive angle nor uniqueness for every positive angle is assumed.** The first deliverable is a collection of proved bounds, a small-angle analysis, and a precise reduction of the remaining optimizer-classification problem.

## Problem and notation

Let `L = ((-infinity,1] x [0,1]) union ([0,1] x (-infinity,1])`. Let `m(omega)` be the supremum of areas of nonempty compact connected sets admitting a motion in L with initial angle zero and final angle `-omega`.

For `0 < omega < pi/2`, normalize the two upper endpoint supports to one. Then every admissible sofa lies in

`P_omega = { (x,y) : 0 <= y <= 1, 0 <= x cos(omega) + y sin(omega) <= 1 }`.

Write `u_t = (cos t, sin t)`, `v_t = (-sin t, cos t)`, `F_omega = { y >= 0, p dot u_omega >= 0 }`, and `J_omega = [0,omega] union [pi/2,pi/2+omega]`.

The cap functional remains the repository's `A_omega(K) = |K| - |N_omega(K)|`, with the **fan**, not the parallelogram, in the definition of the niche. For an arbitrary cap, do not silently identify this difference with the area of a connected feasible sofa.

## Dependency audit

1. Endpoint normalization and monotonization preserve the specified angle: `docs/paper/sections/02-setting.tex`, Fact `fact:angle` and Fact `fact:monotone`.
2. Fixed-angle existence and comparison are the content of Baek's Theorems 3.5.2--3.5.6, with the corrections recorded by the companion manuscript. They do not require the final Gerver optimality theorem. Separate these inputs from `fact:optimal`, which packages them together with global optimality.
3. Penalized selection in `docs/paper/sections/04-selection.tex` already fixes arbitrary `omega in (0,pi/2]` and targets a prescribed positive-area cap maximizer. This is genuinely reusable; it is not a theorem identifying that maximizer.
4. The fixed-angle pinned-variation estimates and the right-angle curvature/injectivity argument must not be conflated. Inspect their angle and area hypotheses before transferring them.
5. A motion extended to pi/2 only puts its shape in the larger-angle feasible class. It does **not** make that shape a pi/2 maximizer. Consequently, right-angle equality rigidity does not identify an arbitrary fixed-angle maximizer.
6. The two endpoint supports remove translation freedom when `cos(omega) != 0`. They do not prove uniqueness, nor exclude noncongruent maximizers or different contact regimes.

## Initial proof targets

### A. A concrete feasible competitor

Consider the convex body

`C_omega = F_omega intersect { p dot u_t <= 1 : t in J_omega }`.

Its motion is rotation by `-t` about the inner corner. Its niche is empty. A radial integral should give

`|C_omega| = omega + tan(pi/4 - omega/2)`.

This is a competitor, not an asserted optimizer. At zero angle it is the unit square; at pi/2 it is the upper unit semicircle.

### B. Upper bound and a strictly positive deficit

Endpoint strips give `m(omega) <= sec(omega)`. Use the supporting hallway at `t = omega/2` to improve this strictly, without invoking Gerver or uniqueness: either an outer support is shortened, which removes a triangle near a vertex of P, or both supports remain large, which excludes a sector near the origin.

Record an explicit positive deficit rather than arguing that every individual sofa has a strict inequality and then incorrectly taking a supremum.

### C. Small-angle corner-carved parallelograms

For the full parallelogram P the support values are

`h_P(t) = sec(omega) cos(t)`,
`h_P(t+pi/2) = sec(omega) cos(omega-t)`.

Its niche has diameter of order `omega^2` near the origin. For small omega, prove directly that `T_omega = P_omega minus N_omega(P_omega)` is compact, connected, and admits the supporting-hallway motion. Do not infer this merely from P being a cap.

This family should improve the elementary small-angle estimate from target A. Under the scaling `p = omega^2 z`, `t = omega s`, the proposed limiting niche is

`D = union_{0<s<1} [0,(1-s^2)/2) x [0,s-s^2/2)`.

Its area is `integral_0^1 (s-s^2/2)s ds = 5/24`. Verify almost-everywhere convergence of the rescaled niches, including the moving fan and the endpoints, before using the area limit.

### D. An upper asymptotic, not only a competitor asymptotic

Near-optimal area forces the outer support values close to those of P. A small triangle contained in a missing support slice should bound a support deficit e by a constant times `sqrt((|P|-|S|) tan(omega))`.

If `|P|-|S| = O(omega^4)`, this is `e = O(omega^(5/2)) = o(omega^2)`. Then the same limiting niche D must be absent from every near-optimal sofa. Together with C, aim to prove

`m(omega) = 1 + omega^2/2 + o(omega^4)` as `omega -> 0+`.

This is a proposed proof target until the accompanying paper supplies both bounds. It does not assert that the corner-carved parallelogram itself is optimal.

### E. Selection and a conditional optimality/rigidity theorem

State an abstract sharp-majorant theorem with all hypotheses explicit: existence, admissibility of a candidate, applicability of an upper functional to every relevant maximizer, sharpness at the candidate, and equality rigidity. This is a reusable proof interface, not a construction of the missing fixed-angle functional.

## Work order

- [x] Isolate the problem and audit the obvious logical dependencies.
- [ ] Write a self-contained paper proof of the explicit competitor, strict upper bound, and zero-angle equality case.
- [ ] Prove feasibility and the area asymptotics of the corner-carved family.
- [ ] Prove a matching upper asymptotic for arbitrary near-maximizers.
- [ ] Record reusable selection statements and the remaining optimizer/uniqueness obligations.
- [ ] Perform an adversarial paper review, especially connectedness, suprema, endpoint conventions, and quantifiers.

## Remaining research after the first note

Determine the first nonzero term beyond the displayed small-angle expansion; derive and solve the appropriate fixed-angle contact equations; construct a sharp global majorant in each justified regime; and prove the equality case. Investigate symmetry rather than assuming it. Normalization removes translations but not reflection as a possible source of multiple maximizers.

The note will distinguish complete elementary proofs, imported results with exact sources, conditional theorems, and unproved research targets. No Lean placeholders should be added before those distinctions are settled.
