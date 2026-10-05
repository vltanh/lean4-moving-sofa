# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not closed.** This branch contains written arguments with self-review, not independent refereeing or Lean verification. No novelty or best-known-bound claim is made.

Start with **[Note 57: focused structural status](57-focused-structural-status.md)**, now updated through Notes 64–65, and **[Corollary 123: the sharp comparison from two support conditions](31-closed-curvature-class-theorem.md)**. Earlier ledgers remain historical snapshots.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing manuscript, Lean sources, dependencies, and workflows are unchanged.

## Latest advance: full turns follow from the other two support conditions

The earlier sufficient route listed three separate structural outputs. [Note 64](64-width-gate-from-curvature-and-contact.md) shows that full-quarter endpoints follow once the curvature and contact conditions are available for a competitive body.

For a unit-span convex hull K with those two conditions, Theorem 119 proves

$$
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.}
$$

The proof uses the centrally symmetric auxiliary body

$$
C=\tfrac12(K+((0,1)-K)),
$$

whose widths equal those of K. Quarter-moment inequalities and the inherited endpoint contact conditions show that C contains a unit-height rectangle of width 2-sqrt(2). **C is not assumed feasible**, and the original hull is not assumed symmetric or to contain that rectangle.

For a body with area greater than sqrt(2), the general canonical reduction already gives endpoint magnitudes greater than pi/4. The displayed width is greater than one for pi/4<=|t|<pi/2, so the outgoing unit strips force both endpoints to be pi/2.

This removes an independent premise of the sharp theorem. It does not establish the two remaining support conditions for arbitrary maximizers, and it does not turn the older width-continuity-only argument into a valid proof.

## Strongest sharp statement now in the branch

[Corollary 123](31-closed-curvature-class-theorem.md) applies to a compact connected ambidextrous body S with arbitrary original motions. In one common unit-span normalization let K=conv(S), and assume

$$
\sigma_K=h_K+h_K''\leq d\theta
$$

on the four open coordinate quarters. For both h_K and its horizontal reflection, write

$$
f(t)=h(t),\qquad g(t)=h(t+\pi/2),
$$

and assume

$$
f'-g+1\leq g'+f-1.
$$

Then the written proof gives

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate.

Full turns are a consequence, not a third hypothesis. The curvature bound may be non-strict and supplies the quarter Sobolev regularity. The theorem does not assume symmetry, fixed contact switches, aligned faces, ordinary velocity monotonicity, or a finite analytic decomposition.

The proof after the width gate uses the earlier exact adaptive functional, its sum-of-squares equality kernel, the weak niche-profile/no-clipping argument, and regular-closed exact-set recovery. The entire preceding chain has not been independently verified in this pass.

## One residual singular-contact case has also been eliminated

[Note 65](65-active-corners-stay-inside-the-projection.md) proves, without regularity or maximality, that a lower canonical corner of nonnegative height at an interior angle must lie strictly inside the horizontal projection of the hull. Its distances from the left and right endpoints are at least

$$
\tan(t/2),\qquad\tan((\pi/2-t)/2),
$$

respectively. A corner at or beyond a projection endpoint is strictly below the incoming strip, so its quadrant and sufficiently small local replacements remove no strip points. Reflection gives the upper-turn case.

Consequently projection-endpoint source corners cannot protect clear singular curvature from the existing improvement operations. The residual singular-continuous cases from Theorem 117 reduce to outer/inner corner coincidences and actual collapsed source-corner fibers without an oblique touching affine ceiling. **These remaining cases are not proved null.** Edge atoms and the sharp density bound also remain unresolved.

## Previous structural results and their limits

The general reductions provide common-hull canonicalization, unit-span normalization, correct turning signs, connected niche separation, a uniform bounding box, attainment, and quantitative selection of any prescribed maximizing hull.

[Notes 52–55](55-slack-span-selection-and-normal-work.md) give mesh-independent finite variation estimates and an exact normal-cone equation. Only the selection penalty is known to vanish; the contact multipliers have not been shown to vanish. Bounded normal work is not substituted for zero work.

[Notes 56](56-atomic-improvement-away-from-obstructions.md) and [58](58-singular-curvature-away-from-obstructions.md) give genuine improvements at clear atomic and singular-continuous contacts. [Notes 59–63](63-roof-continuity-and-singular-residual.md) establish the width-one diffuse-curvature bound, classify ordinary outer/inner contact, handle inactive source corners and oblique pinches, and prove roof continuity. Note 65 removes the unnecessary projection-endpoint residual case. None of these statements asserts the complete global curvature bound.

The non-sharp unrestricted upper bound is in [Note 46](46-explicit-unrestricted-gap.md). The protected local comparison with singular inputs is in [Note 48](48-singular-protected-optimality.md). Neither places every global maximizer near the candidate.

## Failed routes remain recorded

The fixed-switch quadratic is not an area majorant even for feasible bodies with areas tending to M. High-area feasible bodies can violate curvature domination through smooth oscillations, atoms, or singular-continuous measures. The dominated class is closed, so arbitrary smoothing cannot impose that condition while approximating a fixed violating hull.

Other recorded failures include signed corner area counting outside the hull, raw-partition nonconcavity, freezing the active parameter of a max-min roof, replacing visible edge length with full edge length, and deleting finite contact-normal terms just because the selection penalty vanishes.

The new width argument is different from a failed earlier shortcut: it proves a quantitative bound from curvature **and** contact assumptions, uses a symmetral only for widths, and does not suppose that all admissible strip orientations form a connected set.

## The exact remaining closure target

It is sufficient to prove, for a relevant maximizing hull in one common normalization:

1. curvature-measure domination on every open quarter, including the residual singular/atomic configurations and the sharp density bound;
2. both contact-order inequalities.

A result for one attained maximizer settles the value. A result for every maximizer, or an equality-preserving comparison, gives exact uniqueness. Full turns follow from these conditions by Note 64.

These remain substantial geometric obligations. In particular, bounds proved only at floating normals are not automatically domination on the entire open quarters: a partial terminal direction can itself lie in an open quarter and be pinned in a variational argument. The new implication does not remove that distinction.

The branch is not a completed unrestricted proof awaiting compilation.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Envelopes, initial reductions, sharp functional, niche geometry, restricted uniqueness, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, weak curvature theorem, selection, rounding, and finite-angle error rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, a non-sharp global bound, singular examples, and approximation obstructions. |
| [52](52-uniform-support-variation-control.md)–[58](58-singular-curvature-away-from-obstructions.md) | Finite optimality constraints and general maximizer improvements at clear singular contacts. |
| [59](59-width-level-curvature.md)–[63](63-roof-continuity-and-singular-residual.md) | Width-level measures, contact classification, oblique pinches, and roof continuity. |
| [64](64-width-gate-from-curvature-and-contact.md) | Full turns derived from the curvature and contact hypotheses. |
| [65](65-active-corners-stay-inside-the-projection.md) | Active-corner projection margins and removal of an unnecessary residual case. |
| [31](31-closed-curvature-class-theorem.md), [57](57-focused-structural-status.md) | Strongest sharp corollary and current dependency/obligation ledger. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the organization. Standard measure-theory inputs are cited where used. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because unrestricted closure and independent proof review remain unfinished.
