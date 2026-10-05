# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness proof is not closed.** The sharp adaptive-functional optimization is now proved on all normalized real H^1 profiles of horizontal width at least one, without curvature or contact assumptions. The missing step is a justified comparison with ordinary sofa area. A committed near-candidate counterexample shows why that comparison cannot be presumed from feasibility alone.

These are written, self-reviewed arguments, not independent refereeing or Lean verification. No novelty or best-known-bound claim is made.

Start with the **[global adaptive calibration, AF3](adaptive-functional-global-calibration.md)**, the **[exact enclosure counterexample, AF4](adaptive-functional-enclosure-counterexample.md)**, and **[Note 57: the current ledger](57-focused-structural-status.md)**. The structural route and its [two-condition sharp corollary WG4](31-closed-curvature-class-theorem.md) remain available. Earlier ledgers are historical snapshots.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All edits are Markdown in this directory. The existing uniqueness manuscript, Lean sources, dependencies, and workflows are unchanged.

## The analytic maximum is now unconditional on the wide-profile domain

Theorem AF3 assumes only that h is a real 2pi-periodic H^1 function with

$$
h(\pi/2)=1,\qquad h(3\pi/2)=0,\qquad h(0)+h(\pi)\geq1.
$$

It proves

$$
\boxed{\widetilde{\mathcal Q}(h)\leq
M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0,}
$$

with equality exactly for h=h_*+b cos(theta), the candidate profile up to horizontal translation. There is **no convexity, curvature domination, contact-order, or motion assumption** on this auxiliary profile. A genuine unit-span hull containing a body of area greater than one automatically has the required horizontal width.

The proof does not incorrectly assert that the functional is jointly concave in every variable. At fixed horizontal support values it is strictly concave by a Dirichlet spectral-gap identity. The unique half-profile optimizer is symmetric. Its momenta

$$
P=p+\min(p,0),\qquad Q=q+\max(q,0)
$$

satisfy an explicit globally Lipschitz piecewise linear Hamiltonian system. The free-width boundary condition is P(0)=1/2, Q(pi/2)=-1/2. Its orbit lengths leave only the half-unit disk and the candidate as stationary profiles. The disk has smaller value, and an explicit large-width solution rules out escape to infinity. This proves the attained global maximum and its exact equality case.

The cubic for Y emerges from the orbit-time equation. The candidate's exact functional value is the one evaluated in Note 14, not an inserted numerical target. Curvature jumps at contact switches are handled through continuous momenta rather than excluded by an unjustified C^2 assumption.

## The other inequality is genuinely missing

Proposition AF4 considers the already proved feasible high-curvature perturbations and their protected convexification repairs. If u is a nonzero reflected first-quarter repair increment supported in J, then

$$
\boxed{|S|-\widetilde{\mathcal Q}(h_{\operatorname{conv}S})
=\int_J(u'^2-u^2)>0.}
$$

The strict sign follows from the Dirichlet inequality because J is shorter than pi. These are actual compact connected feasible bodies, with the candidate's exact horizontal width and areas tending to M from below. The ordinary-area gain and the functional gain have been computed separately; their difference is the displayed term.

Thus AF3 does **not** close optimality by itself. Even the adaptive functional, not merely the older frozen-switch quadratic, can lie below the actual area near the candidate. The strict suboptimality of these examples comes from a feasible improving repair, not from omitting this positive correction.

One sufficient next statement is ordinary-area enclosure for an actual global maximizer in a common incoming unit-span normalization. For uniqueness it must cover every maximizer or retain an equality-recovery argument. An alternative surrogate profile need not be convex or feasible to use AF3, but its ordinary-area comparison still needs proof. Choosing a profile with value M without establishing that comparison is not a solution.

## The existing structural route now needs only two support conditions

It remains sufficient to establish, for relevant maximizing hulls in **one common incoming unit-span normalization**,

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on the four open coordinate quarters},
$$

and, for both h_K and its horizontal reflection,

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\qquad
p=f'-g+1\leq q=g'+f-1.
$$

The [width-gate supplement](64-width-gate-from-curvature-and-contact.md) proves from these hypotheses that

$$
w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.
$$

A centrally symmetric auxiliary body has the same widths as K and contains the comparison rectangle; it is **not assumed feasible**. For a competitive body, the two-strip estimate already puts its endpoint magnitudes above pi/4. The new width bound then forces full quarter turns. Corollary WG4 supplies the sharp area and exact body-uniqueness result from the two support conditions alone.

Those conditions remain sufficient for the **geometric** enclosure; they are no longer assumptions of the analytic maximum AF3. They have not been proved for every unrestricted maximizer. In particular, domination only at floating normals does not control a pinned partial-terminal normal lying inside an open quarter.

## General contact progress is retained

Theorem 130 in [Note 67](67-removing-the-fiber-clearance-hypothesis.md) excludes singular-continuous curvature at floating normals whose exposed point is strictly clear of both swept niches, without a positive-fiber-gap assumption. The proof combines:

- the two-corner BV graph measures of [Note 65](65-two-corner-pinch-measures.md), with exact jump and orientation terms;
- the zero-sensitivity repair of [Note 66](66-zero-sensitivity-singular-repair.md), where an explicit scaling pays for the small constraint error;
- stationary-corner reciprocity, forcing the opposite velocity traces to p=-1,q=1, together with BV level-set locality.

The earlier inactive-corner repairs, affine-ceiling comparison and roof continuity supply the remaining clear-contact cases. [Note 64](64-positive-corners-are-interior.md) removes the projection-endpoint source case: such a corner lies strictly outside the incoming strip and its small changes remove no strip points.

Corollary 131 localizes remaining singular-continuous curvature to **outer points that themselves coincide with canonical inner corners**. That set is not proved null. Hidden/coincident edge atoms and the sharp absolutely continuous density bound are also unresolved. Countability arguments for nonatomic measures do not dispose of atoms.

The finite optimality equation still has contact normal-cone terms. Vanishing selection penalties and bounded normal work do not make those terms vanish.

## Earlier framework and failed routes

The branch contains common-hull canonicalization, admissible unit-span normalization, correct-angle reductions, connected niche separation, a uniform bounding box, attainment, and quantitative selection of any prescribed maximizing hull. The non-sharp unrestricted bound and protected local results do not locate every maximizer near the candidate.

Recorded failures include the frozen-switch majorant, the adaptive enclosure tested in AF4, signed corner area counting outside the hull, raw-partition nonconcavity, freezing a max-min active angle, replacing visible edge length by full length, and silently dropping contact multipliers. High-area feasible hulls can violate curvature domination; the dominated class is closed, so arbitrary smoothing cannot impose it while approximating a fixed violating hull.

These negative findings remain in the history and the linked proofs. They are not counterexamples to candidate optimality; they invalidate specific attempted comparisons or reductions.

## Reading map

| Notes | Contents |
|---|---|
| [Adaptive calibration](adaptive-functional-global-calibration.md) | AF1–AF3: fixed-width strict concavity, Hamiltonian classification, and the global wide-profile maximum. |
| [Adaptive enclosure counterexample](adaptive-functional-enclosure-counterexample.md) | AF4: the exact positive ordinary-area defect on feasible near-candidate bodies. |
| [Width-gate supplement](64-width-gate-from-curvature-and-contact.md) | WG1–WG3; WG4 in Note 31 removes a separate full-turn assumption from the structural route. |
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Envelopes, sharp functional, restricted geometry, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, weak curvature class, selection, rounding, and finite-angle rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, coarse global bound, singular examples, and approximation obstructions. |
| [52](52-uniform-support-variation-control.md)–[63](63-roof-continuity-and-singular-residual.md) | Constrained finite variations, singular improvements, contact measures and roof continuity. |
| [64](64-positive-corners-are-interior.md)–[67](67-removing-the-fiber-clearance-hypothesis.md) | Projection margins, two-corner pinches, zero-sensitivity repair, and the clear-contact theorem. |
| [57](57-focused-structural-status.md) | Current ledger, dependencies, corrections and remaining geometry. |

The separate AF and WG labels avoid collisions with concurrently added numbered notes. The duplicate projection-corner file is now a pointer; all original work remains in Git history.

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the organization. Standard measure and BV inputs are cited where used. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because the unrestricted ordinary-area comparison and independent proof review remain unfinished.
