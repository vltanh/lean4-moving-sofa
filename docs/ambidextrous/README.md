# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not closed.** This branch contains written arguments with self-review, not independent refereeing or Lean verification. The full earlier proof chain has not been independently audited. No novelty or best-known-bound claim is made.

Start with **[Note 57: focused structural status](57-focused-structural-status.md)**, now updated through Note 63. The preceding inventory is [Note 51](51-current-proof-status.md). Older ledgers remain historical snapshots; the current ledger is being updated rather than adding another numbered status file after each pass.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing manuscript, Lean sources, dependencies, and workflows are unchanged.

## Latest results: classify the actual global contact obstructions

### Width-one diffuse contacts already have the required bound

[Theorem 109](59-width-level-curvature.md) proves, for any convex hull,

$$
\sigma_{K,\mathrm{na}}|_{\{w_K=1\}}\leq dt|_{\{w_K=1\}}.
$$

Here the nonatomic measure includes absolutely continuous and singular-continuous curvature, but not exposed-edge atoms. The unit square shows why the atoms cannot be included.

[Theorem 110](60-classifying-outer-contact-obstructions.md) proves that a regular outer boundary point touching a single inner wall must be in such a width-one direction. Thus the unresolved diffuse outer-contact obstruction is localized to actual hull/inner-corner coincidences, not arbitrary single-wall contact. The defining normals of a blocking corner are quantitatively separated from the touched outer normal.

### Inactive corners do not obstruct singular repair

[Note 61](61-inactive-corners-do-not-obstruct-repair.md) shows that, when a changed corner lies strictly below the lowest surviving point at its abscissa, the short circular support replacement retains the entire old body. A pinching fiber at another height is irrelevant. Under the prior outer-clearance conditions, the added area gives a genuine improvement without requiring a positive fiber gap.

### Oblique pinches admit a direct measure estimate

[Theorem 114](62-oblique-pinch-measure-bound.md) treats a lower corner meeting a local affine ceiling with slope strictly between its two inner-wall slopes. It derives a distributional clearance inequality and proves that both source curvature measures are absolutely continuous on the contact set. It allows families of changing active ceilings and does not assume smoothness or maximality.

A ceiling can be an opposite-motion single wall or a supporting line of the hull. The argument does not cover an arbitrary corner/corner pinch. Parallel inner-wall coincidence produces width **two**, rather than the width-one condition for an outer/inner coincidence, and is treated separately.

### The remaining singular support is now stated precisely

[Note 63](63-roof-continuity-and-singular-residual.md) proves continuous clipped roofs by controlling the small positive height of nearly axis-parallel constraints. This turns positive fiber length at a point into the neighborhood clearance needed by the earlier repair.

[Theorem 117](63-roof-continuity-and-singular-residual.md) then localizes remaining singular-continuous curvature of maximizing hulls to outer corner coincidences, source corners at projection endpoints, and actual collapsed source-corner fibers without an oblique touching affine ceiling. **Those residual classes have not been proved null.** This is not yet global absolute continuity, and it does not settle edge atoms or the sharp density cap.

## The prior maximizer-specific improvements

[Theorem 105](56-atomic-improvement-away-from-obstructions.md) excludes an exposed-edge atom when a strictly clear edge subsegment supplies retained added area and the affected corner band has the stated clearance. The short circular replacement has gain at least c epsilon and old-area loss O(epsilon squared).

[Theorem 107](58-singular-curvature-away-from-obstructions.md) gives the analogous comparison at nonatomic singular-density scales:

$$
|S_c|-|S|\geq c m(r)^2r-Cm(r)r^2>0,
\qquad m(r)/r\longrightarrow\infty.
$$

These are actual feasible improvements, not critical equations with unproved variations. Notes 59–63 remove several false or automatically controlled contact obstructions from their use. The circular replacement may create endpoint atoms and is not claimed to repair the entire hull at once.

## Finite variations retain their constraint terms

[Notes 52–55](55-slack-span-selection-and-normal-work.md) supply a uniform inner radius, mesh-independent support-displacement control, finite polyhedral contact charts with quadratic area, uniform interior-window area-derivative bounds, and an admissible inward saturation with quantified first-order cost.

The selected optimality equation is

$$
\nabla F=\kappa r-\sum_j\mu_j\nabla c_j+A^T\lambda,
\qquad\mu_j\geq0.
$$

The penalty tends to zero; the contact-constraint terms have not been shown to vanish. The fixed-line pinching example in Note 53 records why connectedness and hull retention alone cannot justify deleting them. The new geometric classifications do not turn bounded multipliers into zero multipliers.

## Strongest sharp theorem on a specified class

[Theorem 65](31-closed-curvature-class-theorem.md) assumes a compact connected body with unit-span common hull K, both canonical full quarter turns, curvature-measure domination

$$
\sigma_K=h_K+h_K''\leq d\theta
$$

on the open coordinate quarters, and, for both reflected halves,

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\qquad
f'-g+1\leq g'+f-1.
$$

Its written proof gives

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate. Non-strict curvature and degenerate contacts are allowed. Symmetry, fixed switches, aligned faces, ordinary velocity monotonicity, and finite analytic decompositions are not hypotheses.

The adaptive functional has an exact sharp maximum and a sum-of-squares equality kernel. The geometric profile and no-clipping arguments connect it to actual area on this class; regular closedness supplies exact-set recovery. **Its structural hypotheses are not established for every unrestricted maximizer.**

## Other results and negative findings

The general reductions supply common-hull canonicalization, unit-span normalization, correct signs, connected niche separation, a uniform bounding box, and attainment. Endpoint angles remain variable. Quantitative finite-angle completion and arbitrary-hull selection do not turn partial endpoints into full quarter turns.

The non-sharp unrestricted bound is in [Note 46](46-explicit-unrestricted-gap.md). The protected local comparison allowing singular inputs is in [Note 48](48-singular-protected-optimality.md). Neither localizes every maximizer to the candidate.

The record retains the fixed-switch-majorant counterexample near candidate area, high-area curvature violations, the closedness obstruction to forcing the curvature cap by approximation, signed-area errors, raw-partition nonconcavity, the width-only full-angle failure, the moving max-min derivative correction, and the visible-edge/normal-cone obstructions. The latest notes additionally distinguish width-one from width-two contacts and prove roof continuity rather than inferring it from compactness.

## Exact remaining obligation

An unrestricted structural or area-comparison theorem must still establish or replace full-quarter endpoints, domination of the **complete** open-quarter curvature measure, and the two contact-order inequalities. The residual singular configurations and the sharp absolutely continuous bound remain part of that task.

A structural result for one attained maximizer settles the value. A result for every maximizer, or an equality-preserving comparison, is needed for uniqueness. The branch is not a completed proof awaiting compilation.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Initial envelopes, canonical reductions, sharp functional, niche geometry, restricted uniqueness, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, endpoint constraints, weak curvature theorem, selection, rounding, and finite-angle error rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, unrestricted diagonal bound, singular examples, and approximation obstruction. |
| [52](52-uniform-support-variation-control.md)–[55](55-slack-span-selection-and-normal-work.md) | Finite variation estimates, exact normal cones, and an admissible clearing direction. |
| [56](56-atomic-improvement-away-from-obstructions.md), [58](58-singular-curvature-away-from-obstructions.md) | Maximizer exclusions for atoms and singular-continuous curvature under stated clearance conditions. |
| [59](59-width-level-curvature.md)–[60](60-classifying-outer-contact-obstructions.md) | Width-level measures and classification of diffuse outer contacts. |
| [61](61-inactive-corners-do-not-obstruct-repair.md)–[63](63-roof-continuity-and-singular-residual.md) | Inactive-corner repair, oblique-pinch measures, roof continuity, and residual singular support. |
| [57](57-focused-structural-status.md) | Current structural audit and exact unresolved obligations, updated through Note 63. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the organization. The measure-differentiation input in Note 58 is separately cited there. The new width-level and pinch-measure arguments have direct proofs in Notes 59 and 62. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because unrestricted closure and independent proof review remain unfinished.
