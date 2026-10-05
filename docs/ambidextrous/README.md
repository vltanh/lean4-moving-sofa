# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not proved in this branch.** The work contains a sharp geometric theorem on a specified curvature/contact class, a newer protected-arc theorem without an input curvature cap, general approximation and attainment results, and explicit counterexamples to failed proof routes.

These are written, self-reviewed proofs, not independent refereeing or Lean verification. No novelty or priority claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing manuscript, Lean files, dependencies, and workflows are unchanged.

**Start with [the current proof ledger, Note 43](43-current-proof-status.md).** Notes are chronological. Notes 7, 24, and 34 are earlier status snapshots, not the current task list.

## Current geometric results

### Global bound on the stated curvature/contact class

[Theorem 65](31-closed-curvature-class-theorem.md) applies to a compact connected S with common hull K, normalized to vertical span one, and with both canonical full quarter turns feasible. Assume the curvature measure h_K+h_K'' is dominated by dtheta on each open coordinate quarter. For both h_K and its reflected support function, set

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\quad
p=f'-g+1,\quad q=g'+f-1,
$$

and assume p<=q. Then

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate.

The curvature bound is non-strict and supplies the quarter Sobolev regularity. Symmetry, fixed switches, aligned faces, ordinary velocity monotonicity, and finitely many analytic pieces are not hypotheses. The missing unrestricted task is to derive or replace the remaining full-turn, curvature, and contact assumptions for arbitrary maximizers.

### A new local theorem without assuming the curvature cap

[Theorem 83](42-independent-arc-repairs.md) permits independent, nonsymmetric, C^1-small convex support perturbations in protected arc windows away from the candidate's axis normals and switching neighborhoods. Their curvature may exceed one and their second derivatives need not be small.

A convex-minorant construction repairs the excessive curvature while preserving the relevant wall envelope. The proof separately accounts for the moving corner graph and shows that every nonzero repair strictly increases actual feasible area. The repaired body satisfies Theorem 65. Consequently the original perturbed body has area at most M, with equality only for the candidate.

This is not an unrestricted Hausdorff-local theorem; the protected-window and C^1 conditions remain. It does resolve the area sign of the earlier high-frequency family: [Note 41](41-resolving-the-high-curvature-family.md) proves **|S_n|<M for all sufficiently large n**, while |S_n| tends to M. The old statements in Notes 28 and 34 that the sign was undetermined are superseded.

## General results that do not assume the candidate contact pattern

Notes 8–10, 15, and 25 prove a containment-preserving common-hull reduction for all competitive bodies, unit incoming span, correct turning signs, connected separated saturation, a uniform bounding box, and global attainment. The endpoint magnitudes remain variables in (0,pi/2].

[Note 38](38-quantitative-angle-completion.md) now gives a quantitative full-motion repair: if a radius-R connected body satisfies canonical constraints on an angular mesh of maximum gap Delta, then S/(1+R Delta) satisfies the complete motions between the same endpoints.

For the exact finite-angle upper values v_n with N=2^n,

$$
V\leq v_n\leq(1+e_n)^2V,
\qquad e_n=\sqrt{4+2\sqrt2}\,(\pi/2)/N.
$$

No v_n is numerically evaluated here. [Note 39](39-effective-maximizer-selection.md) uses this rate to select any prescribed maximizing hull with the explicit penalty N^-1/2. It gives hull error O(N^-1/2) and genuinely feasible polygonal approximants with area error O(N^-1).

Other unrestricted results include coupled endpoint-angle bounds, localization of strictly hidden boundary measure to edge atoms, and the motion-preserving rounding operation from Note 33. The rounding yields Per(S)<=4|S| for every global maximizer, but this is not a sharp equality certificate for the candidate.

## The sharp functional and curvature calculations

The adaptive functional adds the two signed corner integrals to hull area and subtracts the negative-p and positive-q squared contact terms. Its switches move with the support function. Notes 13–16 and 22–31 prove its sharp maximum M on the stated convex function domain and identify its equality kernel as horizontal translation.

[Notes 35–37](37-excluding-buried-endpoint-corners.md) derive the curvature cap from actual criticality in a regular full-turn model. The moving-angle contribution at a corner is retained. Any excessive-curvature interval would reach an endpoint and bury an active limiting corner inside another forbidden quadrant. This is not yet a theorem for arbitrary maximizing measures: its C^2 and stable-contact/admissible-variation hypotheses do not cover curvature jumps, atoms, or changing contact topology automatically.

[Notes 40–42](42-independent-arc-repairs.md) give the separate, actual feasible repair near protected candidate arcs. Preserving one wall envelope alone is insufficient; the corner-area cost is included explicitly. The two approaches should not be conflated.

## Negative findings retained

The fixed-switch quadratic has maximum M but is not an area majorant, even for feasible bodies whose areas tend to M; Note 19 gives an exact counterexample. High area alone does not imply the curvature cap; Note 28 remains a valid counterexample to that inference, with its strict area deficit now established in Note 41.

Other recorded failures include signed corner area counting outside the hull, nonconcavity of the raw partition relaxation, a width-only argument that does not prove full turns, and the difference between full and visible outer-edge length. Note 35 adds a max-min derivative counterexample: freezing the active angle loses the first-order motion of a crossing contact.

The [current ledger](43-current-proof-status.md) records which repairs are proved and which gaps remain. No failed route is silently reused as an unrestricted upper bound.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[7](07-proof-ledger.md) | Initial envelopes, overlap/partition identities, candidate separation, and historical first-pass program. |
| [8](08-common-hull-tightening.md)–[12](12-explicit-quadratic-kernel.md) | Canonical reduction, separation, wrong-angle exclusion, exact benchmarks, and initial quadratic tests. |
| [13](13-contact-quadratic.md)–[24](24-current-proof-ledger.md) | Sharp quadratic/adaptive analysis, exact niche geometry, restricted body uniqueness, and early audit. |
| [25](25-compactness-and-attainment.md)–[34](34-current-proof-status.md) | Attainment, endpoint coupling, curvature counterexamples, weak-bound theorem, selection, and rounding. |
| [35](35-active-wall-and-corner-tests.md)–[37](37-excluding-buried-endpoint-corners.md) | Correct moving-corner variation and a regular-critical curvature theorem. |
| [38](38-quantitative-angle-completion.md)–[39](39-effective-maximizer-selection.md) | Explicit finite-angle error and quantified selection of every maximizing hull. |
| [40](40-curvature-repair-by-convexification.md)–[42](42-independent-arc-repairs.md) | Convex-minorant repairs, strict suboptimality of the high-curvature family, and independent protected-arc comparison. |
| [43](43-current-proof-status.md) | Current statements, dependencies, negative findings, audit, and unrestricted obligations. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the proof organization. Their single-turn optimality hypotheses are not silently imported into this different problem. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Every research commit includes `[skip ci]`; workflow definitions are untouched. The PR remains open and draft because the unrestricted proof and independent review are unfinished.
