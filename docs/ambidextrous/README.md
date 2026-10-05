# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not closed.** This branch contains written mathematical arguments with self-review, not independent refereeing or Lean verification. No novelty or best-known-bound claim is made.

Start with **[Note 57: focused structural status](57-focused-structural-status.md)**. The preceding full inventory is [Note 51](51-current-proof-status.md). Notes are chronological; older status notes remain as historical snapshots rather than current instructions.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
All changes are Markdown in this directory. The existing manuscript, Lean files, dependencies, and workflows are unchanged.

## Latest focus: the actual structural bottleneck

The latest pass did not add another coarse numerical bound or merely enlarge the protected-candidate class. [Notes 52–55](55-slack-span-selection-and-normal-work.md) make the finite variation system explicit, and [Note 56](56-atomic-improvement-away-from-obstructions.md) obtains a new maximizer-specific atom exclusion.

### An improvement at a general body, not just near the candidate

Theorem 105 applies to an exposed-edge atom at a floating normal, with no input smoothness, curvature cap, full-turn assumption, or proximity to Romik. It requires a strictly clear subsegment of that edge and positive surviving-fiber clearance near the corresponding inner-corner abscissa.

A short replacement solving f_c''+f_c=1 with the old endpoint values raises the support while preserving convexity. Its relevant one-wall supremum is unchanged. The complete two-wall niche changes only in a band of width O(epsilon), by a height O(epsilon), while a clear portion of the old edge gains a triangle of area at least c epsilon. Thus the actual feasible connected competitor satisfies

$$
|S_\varepsilon|-|S|\geq c\varepsilon-C\varepsilon^2>0.
$$

Such an atom cannot occur at a global maximizer. **Masked/coincident edges and atoms tied to pinching connections remain outside the conclusion.** The operation generally creates new endpoint atoms; it is not falsely claimed to repair the entire curvature measure in one step.

### The finite Euler equations retain constraint normals

The supporting-polygon estimate in [Note 52](52-uniform-support-variation-control.md) is independent of angular mesh separation:

$$
d_H(K_s,K)\leq (RC/r)|s|.
$$

Competitive hulls have a uniform inner radius, so the selection penalty vanishes for bounded-speed, hull-preserving admissible variations without an extra mesh factor.

[Note 53](53-finite-variation-normal-cones.md) derives the exact finite normal-cone identity. On an incident feasible chart,

$$
\nabla F=\kappa r-\sum_j\mu_j\nabla c_j+E^T\lambda,
\qquad\mu_j\geq0,
$$

where r is a penalty subgradient and c_j>=0 are active constraints. The contact terms need not vanish when kappa does. A fixed-line pinching example records why merely declaring the limiting polygon balanced is invalid.

[Note 54](54-uniform-finite-area-derivatives.md) gives a mesh-independent area-derivative bound away from the axis normals and weak compactness of the resulting signed measures. [Note 55](55-slack-span-selection-and-normal-work.md) relaxes exact span at the selection stage, makes inward canonical saturation genuinely admissible, and bounds the normal work along that direction. It does not discard the first-order cost of the inward operation or infer that bounded multipliers vanish.

## Strongest sharp theorem on a specified class

[Theorem 65](31-closed-curvature-class-theorem.md) applies to a compact connected body with unit-span common hull K and both canonical full quarter turns feasible. Its hypotheses are

$$
\sigma_K=h_K+h_K''\leq d\theta
$$

on each open coordinate quarter, and, for both h_K and its reflected counterpart,

$$
f(t)=h(t),\quad g(t)=h(t+\pi/2),\qquad
f'-g+1\leq g'+f-1.
$$

Then the written proof gives

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate. The non-strict measure bound supplies the Sobolev regularity. Symmetry, fixed contact switches, aligned exposed faces, ordinary velocity monotonicity, and a finite analytic decomposition are not hypotheses.

The adaptive functional has a sharp maximum and a sum-of-squares equality kernel. Exact niche geometry and a no-clipping argument connect it to actual area on this class. Exact-set recovery uses regular closedness of the identified candidate. **The displayed structural hypotheses have not been derived for every unrestricted maximizer.**

## Other results and their scopes

[Theorem 89](46-explicit-unrestricted-gap.md) gives the non-sharp unrestricted bound

$$
|S|<2\sqrt2-1-1/20000.
$$

Together with attainment and candidate feasibility, this brackets the unknown optimum but does not identify it with M. It is a finite analytic position certificate, not a numerical optimization of the full problem.

[Theorem 92](48-singular-protected-optimality.md) proves area at most M for uniformly close convex supports equal to the candidate outside fixed protected angular windows. It allows singular curvature and independent changes to the four quarters. The exact agreement near axes and switching regions remains a substantive restriction; it is not unrestricted Hausdorff-local optimality.

The earlier general reductions establish a common convex hull, unit-span normalization, correctly signed canonical angular intervals, connected niche separation, a uniform bounding box, and attainment. The endpoint angles remain variables. [Notes 38–39](39-effective-maximizer-selection.md) supply quantitative finite-angle completion and selection of every prescribed maximizing hull. Scaling fills gaps between sampled angles; it does not extend a partial endpoint to a quarter turn.

## Negative findings are retained

The fixed-switch quadratic is not an area majorant even for feasible bodies with areas tending to M; [Note 19](19-near-candidate-counterexample.md) gives the exact counterexample. Near-optimal feasible bodies can violate the curvature cap, including by exposed-edge atoms or singular-continuous measures. [Note 50](50-curvature-domination-is-not-dense.md) proves that the dominated class is closed, so generic smoothing cannot impose the missing condition while approximating a fixed violating hull arbitrarily closely.

Other retained failures include signed corner area counting outside the hull, raw-partition nonconcavity, the width-only full-angle argument, freezing a moving max-min contact, and replacing visible edge length by full edge length. The latest finite analysis adds the explicit nonvanishing contact-normal obstruction; it does not reclassify any of these failures as a proof.

## Exact remaining unrestricted task

A valid structural or area-comparison theorem must establish or replace all three requirements:

- full-quarter endpoints;
- the entire open-quarter curvature-measure bound, including the obstructed cases not excluded by Theorem 105;
- the two contact-order inequalities.

A result for one attained maximizer would settle the value. A result for every maximizer, or an equality-preserving comparison, is needed for uniqueness. Selecting arbitrary maximizers and controlling penalty errors are not substitutes for the geometric statement itself.

The current finite route has explicit equations and controlled errors, but its feasibility/normal-cone terms remain. This is still a substantial missing argument, not a completed proof awaiting compilation.

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[24](24-current-proof-ledger.md) | Initial envelopes, canonical reductions, sharp functional, niche geometry, restricted uniqueness, and early counterexamples. |
| [25](25-compactness-and-attainment.md)–[39](39-effective-maximizer-selection.md) | Attainment, endpoint constraints, weak curvature theorem, selection, rounding, and finite-angle error rates. |
| [40](40-curvature-repair-by-convexification.md)–[51](51-current-proof-status.md) | Protected repairs, unrestricted diagonal bound, singular examples, approximation obstruction, and preceding inventory. |
| [52](52-uniform-support-variation-control.md)–[55](55-slack-span-selection-and-normal-work.md) | Uniform finite variation estimates, exact normal cones, area measures, and an admissible clearing direction. |
| [56](56-atomic-improvement-away-from-obstructions.md)–[57](57-focused-structural-status.md) | General maximizer atom improvement and current structural audit. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826) and the repository's [uniqueness manuscript](../paper/) motivate the proof organization. No single-turn optimality hypothesis is silently imported into this different problem. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed. Every research commit includes `[skip ci]`. The PR remains open and draft because unrestricted closure and independent proof review remain unfinished.
