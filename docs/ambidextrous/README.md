# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not closed.** This branch contains written arguments with self-review, not independent refereeing or Lean verification. The earlier proof chain has not been independently audited. No novelty or best-known-bound claim is made.

Start with **[Note 57: focused structural status](57-focused-structural-status.md)**, updated through Note 58. The preceding inventory is [Note 51](51-current-proof-status.md). Older ledgers are retained as historical snapshots.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing manuscript, Lean sources, dependencies, and workflows are unchanged.

## Latest results: the unrestricted structural problem, not another candidate neighborhood

### Singular curvature at clear contacts cannot maximize area

[Theorem 105](56-atomic-improvement-away-from-obstructions.md) treats an exposed-edge atom at a floating normal of a general canonical body. It assumes a strictly clear subsegment of the edge and positive surviving-fiber clearance near the affected inner corner. It does not assume proximity to the candidate, full-quarter endpoints, smoothness, or a curvature cap.

Replacing the support on a short interval by the solution of f_c''+f_c=1 with the old endpoint values gives a convex outward replacement. Its relevant one-wall envelope is unchanged. The complete niche can change only in a shrinking corner band: its area cost is O(epsilon squared), while a retained triangle gains at least c epsilon. Thus the original body is not maximizing.

[Theorem 107](58-singular-curvature-away-from-obstructions.md) extends the mechanism to nonatomic singular-density points. For suitable radii r with central curvature mass m(r),

$$
|S_c|-|S|\geq c m(r)^2r-Cm(r)r^2>0,
\qquad m(r)/r\longrightarrow\infty.
$$

Measure differentiation supplies such scales at almost every singular-continuous curvature point. Strict outer-contact clearance and the stated fiber-clearance alternatives ensure the added hull survives and the new body stays connected.

**Scope:** these exclude singular curvature only in the unobstructed geometry. Masked/coincident contacts, pinching connections, pinned normals, and the sharp upper bound on the absolutely continuous curvature density remain unresolved. The circular replacement can create endpoint atoms; it is not claimed to repair the entire hull at once.

### Finite variations now have explicit constraint terms

[Notes 52–55](55-slack-span-selection-and-normal-work.md) establish the finite-dimensional ingredients directly:

- a uniform inner radius and the mesh-independent estimate d_H(K_s,K)<=RC|s|/r, eliminating artificial angle-gap amplification for hull-preserving variations;
- finite polyhedral contact charts with quadratic area and an exact normal-cone optimality equation;
- a mesh-independent bound on raw-envelope area derivatives away from axis normals;
- a slack-span selector and a genuinely admissible inward saturation, with controlled first-order cost and normal work.

The selected optimality equation is

$$
\nabla F=\kappa r-\sum_j\mu_j\nabla c_j+A^T\lambda,
\qquad\mu_j\geq0.
$$

The penalty coefficient tends to zero. The contact-constraint terms have not been shown to vanish. A committed fixed-line pinching example shows why connectedness and hull retention alone do not permit that inference. The raw full-envelope area estimate is not substituted for a largest-connected-component estimate.

## Strongest sharp theorem on a specified class

[Theorem 65](31-closed-curvature-class-theorem.md) concerns a compact connected body S with unit-span common hull K and both canonical full quarter turns feasible. Assume

$$
\sigma_K=h_K+h_K''\leq d\theta
$$

on each open coordinate quarter and, for both h_K and its reflected counterpart,

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\qquad
f'-g+1\leq g'+f-1.
$$

Then the written proof gives

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate. The non-strict curvature-measure bound supplies Sobolev regularity. Symmetry, fixed switches, aligned faces, ordinary velocity monotonicity, and finite analytic decompositions are not hypotheses.

The adaptive functional has an exact sharp maximum and a sum-of-squares equality kernel. Niche geometry and a no-clipping argument connect it to actual area on this class. Regular closedness of the identified candidate supplies exact-set recovery. **Its full-turn, curvature, and contact hypotheses have not been established for every unrestricted maximizer.**

## Other results and their limits

[Theorem 89](46-explicit-unrestricted-gap.md) gives the non-sharp unrestricted bound

$$
|S|<2\sqrt2-1-1/20000.
$$

It does not identify the optimum with M or locate every maximizer near the candidate.

[Theorem 92](48-singular-protected-optimality.md) bounds uniformly close convex supports equal to the candidate outside fixed protected angular windows, allowing singular curvature and independent quarter perturbations. Exact agreement near axes and switches is a substantive restriction; this is not unrestricted Hausdorff-local optimality.

The general reductions establish common-hull canonicalization, unit-span normalization, correct turning signs, connected niche separation, a uniform bounding box, and attainment. The endpoint angles remain variable. [Notes 38–39](39-effective-maximizer-selection.md) give quantitative finite-angle completion and selection of any prescribed maximizing hull. Filling the gaps in a mesh does not extend a partial endpoint to a quarter turn.

## Negative findings remain part of the record

The fixed-switch quadratic is not an area majorant even for feasible bodies with areas tending to M; [Note 19](19-near-candidate-counterexample.md) gives the counterexample. High-area feasible hulls can violate the curvature cap by smooth oscillations, edge atoms, or singular-continuous measures. [Note 50](50-curvature-domination-is-not-dense.md) proves the dominated class is closed, so general smoothing cannot impose that condition while approximating a fixed violating hull arbitrarily closely.

Other failures include signed corner area counting outside the hull, raw-partition nonconcavity, the width-only full-angle argument, freezing a moving max-min contact, and replacing visible edge length by full edge length. The new finite analysis records the nonvanishing constraint-normal obstruction rather than silently discarding it.

## Exact remaining obligation

An unrestricted structural or area-comparison theorem must establish or replace:

1. full-quarter endpoints;
2. domination of the entire open-quarter curvature measure, including obstructed singular contacts and the remaining density bound;
3. the two contact-order inequalities.

A result for one attained maximizer would settle the value. A result for every maximizer, or an equality-preserving comparison, is needed for uniqueness. Selection, compactness, and vanishing penalty errors do not supply this missing geometry by themselves. The branch is not a completed proof awaiting compilation.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Initial envelopes, canonical reductions, sharp functional, niche geometry, restricted uniqueness, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, endpoint constraints, weak curvature theorem, selection, rounding, and finite-angle error rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, unrestricted diagonal bound, singular examples, approximation obstruction, and preceding inventory. |
| [52](52-uniform-support-variation-control.md)–[55](55-slack-span-selection-and-normal-work.md) | Uniform finite variation estimates, exact normal cones, area measures, and an admissible clearing direction. |
| [56](56-atomic-improvement-away-from-obstructions.md) and [58](58-singular-curvature-away-from-obstructions.md) | General maximizer exclusions for atoms and singular-continuous curvature under explicit clearance conditions. |
| [57](57-focused-structural-status.md) | Current structural audit, including the remaining obstructions and corrections. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the organization. The standard measure-differentiation input for Note 58 is separately cited there. No single-turn optimality hypothesis is silently imported into this different problem. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because unrestricted closure and independent proof review remain unfinished.
