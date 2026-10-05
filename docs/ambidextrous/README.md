# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness proof is not closed.** This branch contains written, self-reviewed arguments, not independent refereeing or Lean verification. No novelty or best-known-bound claim is made.

Start with **[Note 57: the current structural ledger](57-focused-structural-status.md)**, through Note 67 and the width-gate supplement, and **[Corollary WG4: sharp comparison from two support conditions](31-closed-curvature-class-theorem.md)**. Earlier ledgers remain historical snapshots.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing uniqueness manuscript, Lean sources, dependencies, and workflows are unchanged.

## What is still required for unrestricted closure

It suffices to establish, for a relevant maximizing hull K in **one common unit-span normalization**,

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on every open coordinate quarter},
$$

and, for both h_K and its reflected support function,

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\qquad
p=f'-g+1\leq q=g'+f-1.
$$

The first condition includes exclusion/control of all singular and atomic parts and the sharp bound on the remaining density. Neither condition has been proved for every unrestricted maximizer. A proof for one attained maximizer would identify the optimal value; a proof for every maximizer, or an equality-preserving comparison, would give exact uniqueness.

The statements below reduce these obligations but do not replace them with a completed global proof.

## Full turns follow from those two conditions

The [width-gate supplement](64-width-gate-from-curvature-and-contact.md), Theorem WG2, proves

$$
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.}
$$

Its centrally symmetric auxiliary body C=(K+((0,1)-K))/2 has the same widths as K. Quarter-moment bounds and the inherited contact traces put a unit-height rectangle of width 2-sqrt(2) inside C. **C is not asserted to be a feasible sofa.** No symmetry of the actual body is assumed.

Every body of area greater than sqrt(2) already has correctly signed canonical endpoint magnitudes greater than pi/4. The displayed width is strictly greater than one from pi/4 up to, but not including, pi/2. Its outgoing unit-strip conditions therefore force both full quarter turns.

Corollary WG4 then applies the earlier sharp adaptive-functional theorem and proves

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad 4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate. Full turns are no longer a third independent assumption. Non-strict curvature is allowed; symmetry, fixed switches, face alignment, ordinary velocity monotonicity, and a finite analytic arc decomposition are not assumed.

This implication does not supply the two support conditions themselves. In particular, a partial terminal normal can be pinned yet lie inside an open quarter, so domination proved only at floating normals is not the complete required measure bound.

## New maximizer-specific progress: fiber clearance is unnecessary for clear singular-continuous contacts

[Theorem 130 in Note 67](67-removing-the-fiber-clearance-hypothesis.md) proves that a maximizing hull's singular-continuous curvature gives zero mass to floating normals whose exposed outer point is strictly clear of both closed swept niches. It no longer assumes a positive surviving-fiber gap near the affected source corner.

The proof combines three different mechanisms rather than treating every pinch as the same case.

**Transverse corner graphs.** [Note 65](65-two-corner-pinch-measures.md) derives the second-derivative measures of the two moving graphs, including exact jump terms and the orientation of the parameter map. Their gap is nonnegative by connected feasibility. Level-set locality then bounds the positively weighted source curvature on the pinch set. Note 67 extends the comparison to charts where the required coefficient signs hold only at actual contacts.

**Vanishing sensitivity.** [Note 66](66-zero-sensitivity-singular-repair.md) treats source singular mass where its other contact coefficient vanishes. For a circular support replacement on a radius-r interval with central mass m(r), the retained hull gain is at least c m(r)^2r, while the uniform hallway error is e_r=o(m(r)^2r). The old-niche comparison body is connected; scaling it by 1/(1+e_r) restores the exact motions at a smaller area cost. No infeasible variation is declared cost-free.

**Stationary blocking corners.** Two retained extreme-point tests show that an opposite corner coinciding with a stationary corner has velocity traces p=-1 and q=1 at an interior angle. BV level-set locality excludes source singular-continuous measure there. Countable blocker images handle terminal and jump parameters only for nonatomic source measures.

The earlier inactive-corner improvements, oblique affine-ceiling bound, and roof continuity supply the remaining cases. The new proof permits partial endpoint angles and arbitrary input curvature measures; it is not restricted to a neighborhood of the candidate.

### What remains of singular-continuous curvature

Corollary 131 now localizes any remaining singular-continuous curvature to **outer points that themselves coincide with canonical inner corners**. That residual set has not been proved null.

The previous independent source-corner pinch obstruction is removed at clear outer points. This is not a statement that every outer point is clear, nor a proof of the sharp density cap. Hidden/coincident edge atoms and pinned normals remain separate issues. Countability arguments used for singular-continuous curvature cannot discard atoms.

[Theorem 118 in Note 64](64-positive-corners-are-interior.md) also removes the projection-endpoint source-corner case: a nonnegative-height lower corner is strictly inside the horizontal projection; a corner at an endpoint lies strictly below the strip and its small changes remove no strip points.

## Earlier framework and failed routes remain relevant

The branch contains common-hull canonicalization, unit-span normalization, correct-angle reductions, connected niche separation, a uniform bounding box, attainment, and quantitative selection of any prescribed maximizing hull. The finite optimality equation retains its contact normal cone; vanishing selection penalties and bounded normal work do not imply that its constraint terms vanish.

The exact adaptive functional and its sum-of-squares equality kernel are recorded in Notes 13–16 and their extensions. The weak niche geometry connects it to actual area on the stated support class. Exact body recovery uses regular closedness of the identified candidate, not just zero area loss.

The fixed-switch quadratic is not an area majorant even for actual feasible bodies with areas tending to M. High-area feasible hulls can violate curvature domination through smooth oscillations, atoms, or singular-continuous measures. The dominated class is closed, so ordinary smoothing cannot impose the missing bound while staying arbitrarily close to a fixed violating hull.

Other recorded failures include signed corner area counting outside the hull, raw-partition nonconcavity, freezing an active max-min parameter, replacing visible edge length by full edge length, and silently deleting connectivity/contact multipliers. The non-sharp unrestricted bound of Note 46 and the protected local theorem of Note 48 do not localize every maximizer near the candidate.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Envelopes, initial reductions, sharp functional, restricted geometric theorem, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, weak curvature theorem, selection, rounding, and finite-angle error rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, non-sharp global bound, singular examples, and approximation obstructions. |
| [52](52-uniform-support-variation-control.md)–[58](58-singular-curvature-away-from-obstructions.md) | Constrained finite optimality and actual singular-curvature improvements under initial clearance assumptions. |
| [59](59-width-level-curvature.md)–[63](63-roof-continuity-and-singular-residual.md) | Width-level measures, outer-contact classification, oblique pinches, and roof continuity. |
| [64](64-positive-corners-are-interior.md) | Projection margins and the harmless endpoint source-corner case. |
| [Width-gate supplement](64-width-gate-from-curvature-and-contact.md) | WG1–WG3: full turns follow from curvature and contact; WG4 in Note 31 gives the strengthened sharp corollary. |
| [65](65-two-corner-pinch-measures.md) | Exact BV measures at two-corner pinches, including atoms. |
| [66](66-zero-sensitivity-singular-repair.md) | Lower-order uniform-error correction at vanishing contact coefficients. |
| [67](67-removing-the-fiber-clearance-hypothesis.md) | Stationary-corner reciprocity, the clear-contact singular theorem, and the remaining outer-corner residual. |
| [57](57-focused-structural-status.md) | Current dependency ledger, audit, and precise remaining obligations. |

Concurrent notes originally shared numerical labels. The width-gate supplement now uses WG1–WG4; the duplicate projection-corner file is a pointer preserving old links. The numbered results in Notes 64–67 use 118–131.

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the organization. Standard measure and BV inputs are cited where used. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because unrestricted closure and independent proof review remain unfinished.
