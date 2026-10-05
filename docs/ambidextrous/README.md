# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness problem is not proved in this branch.** The work now contains an explicit sharp functional, its exact maximization and equality kernel, and a completed geometric optimality-and-uniqueness theorem on a stated support-function class. It also records explicit counterexamples to unsuccessful proof routes.

These are written, self-reviewed mathematical proofs, not independent refereeing or Lean verification. No novelty or priority claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
The existing uniqueness manuscript, Lean files, dependencies, and workflows are unchanged.

**Start with the [current proof ledger](24-current-proof-ledger.md) and [Theorem 52](23-sobolev-geometric-theorem.md).** Notes are chronological; the current ledger supersedes the initial task list in Note 7.

## Strongest geometric result proved

Let K be the convex hull of a compact connected sofa S, normalized to vertical span one. Suppose S follows both canonical full conventional quarter turns. On both h_K and its reflected support function, write

$$
f(t)=h(t),\qquad g(t)=h(t+\pi/2),\qquad
p=f'-g+1,\qquad q=g'+f-1.
$$

If the quarter functions are H^2 and satisfy

$$
0\leq f''+f<1,\qquad0\leq g''+g<1\quad\text{almost everywhere},
\qquad p\leq q,
$$

then [Theorem 52](23-sobolev-geometric-theorem.md) proves

$$
|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0,
$$

with equality exactly for bodies congruent to Romik's candidate.

The theorem does **not** assume symmetric competitors, fixed contact switches, aligned horizontal faces, ordinary monotonicity of both velocities, or finitely many analytic boundary pieces. The proof derives the required contact structure and face alignment from its remaining hypotheses.

## What is already reduced for arbitrary competitive bodies

For every body with area greater than sqrt(2), [Notes 8–10](10-wrong-angle-exclusion.md) and [Note 15](15-unit-span-normalization.md) prove a containment-preserving reduction to one common convex hull, unit incoming span, and canonical monotone motions with correct turning signs. The two endpoint magnitudes remain variables in (0,pi/2].

Connectedness forces the two niches to be disjoint inside this actual common hull. The entire canonical saturation is compact, connected, vertically convex, and has the same hull. Thus its area is exactly the hull area minus the two full niche areas. No symmetry assumption or maximizer-existence theorem is needed for these reductions.

What remains is to justify full-quarter endpoints and the support-curvature/contact hypotheses for arbitrary relevant maximizers or for a covering comparison class. The [visible-side balance obstruction](21-visible-side-balance-obstruction.md) explains why the single-turn variation theorem cannot simply be imported unchanged.

## The sharp functional and its rigidity

Let c_h=(f-1)mu+(g-1)nu and I(h)=one half of the integral of det(c_h,c_h'). The adaptive functional is

$$
\widetilde{\mathcal Q}(h)
=|K|+I(h)+I(h^\rho)
-\frac12\sum_{j\in\{h,h^\rho\}}
\left[\int\min(p_j,0)^2+\int\max(q_j,0)^2\right].
$$

[Notes 13–14](14-sharp-quadratic-calibration.md) derive an exact sum-of-squares Hessian, match the explicit candidate, prove stationarity against all normalized support variations, and evaluate the maximum as M. [Notes 16](16-adaptive-contact-functional.md) and [22](22-weaker-contact-hypotheses.md) allow the contact switches to move while preserving concavity on an explicit convex domain. Equality forces h-h_* to be a horizontal-translation support function a cos(theta).

[Notes 17–20](20-forced-face-alignment.md) turn this functional statement into a geometric one. They prove the niche roof rather than assume its contact pattern, identify the potential clipping error, and then eliminate that error using retention of extreme points in a feasible common hull. Exact body recovery uses a separate regular-closedness proof. [Note 23](23-sobolev-geometric-theorem.md) removes the finite-piece regularity restriction.

## Negative results are part of the record

The fixed-switch quadratic has the correct maximum M but is **not** a direct area majorant. [Note 19](19-near-candidate-counterexample.md) constructs actual feasible bodies S_epsilon whose areas approach M and satisfy

$$
|S_\varepsilon|>\mathcal Q_{\beta,\pi/2-\beta}(h_\varepsilon).
$$

The moving-switch adaptive functional gives their correct area instead. Thus neither a high-area threshold nor proximity to the candidate repairs the frozen-contact argument.

Other recorded failures include the wrong sign from double niche subtraction without separation, signed corner area counting regions outside the hull, nonconcavity of the raw partition relaxation, and a width-only argument that does not establish full-angle completion. The reflected Hammersley family is solved exactly and ruled out as a candidate for the sharp value. See the [negative-results table](24-current-proof-ledger.md).

## Reading map

| Notes | Contents |
|---|---|
| [1](01-two-motion-envelopes.md)–[3](03-partition-certificate.md) | General two-motion envelopes, overlap signs, and a universally valid partition majorant. |
| [4](04-romik-candidate.md)–[7](07-proof-ledger.md) | First-pass candidate separation, visible variations, conditional certificate, and historical ledger. |
| [8](08-common-hull-tightening.md)–[10](10-wrong-angle-exclusion.md) | Canonical common-hull reduction, connectedness-based separation, and wrong-angle exclusion. |
| [11](11-negative-tests-and-benchmarks.md)–[12](12-explicit-quadratic-kernel.md) | Exact benchmark family, counterexamples, and the first explicit quadratic kernel. |
| [13](13-contact-quadratic.md)–[14](14-sharp-quadratic-calibration.md) | Contact quadratic, positive factorization, exact candidate stationarity, value, and rigidity. |
| [15](15-unit-span-normalization.md)–[16](16-adaptive-contact-functional.md) | Unit-span normalization and the moving-contact replacement. |
| [17](17-exact-niche-profile.md)–[18](18-restricted-optimality-and-uniqueness.md) | Exact niche geometry and the first completed restricted area/uniqueness theorem. |
| [19](19-near-candidate-counterexample.md)–[20](20-forced-face-alignment.md) | Feasible near-candidate counterexamples and automatic face alignment. |
| [21](21-visible-side-balance-obstruction.md)–[23](23-sobolev-geometric-theorem.md) | Balance-transfer obstruction, weaker hypotheses, and the strongest geometric theorem. |
| [24](24-current-proof-ledger.md) | Current dependencies, audit, positive and negative findings, and exact remaining obligations. |

## Sources and attribution

- Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, [arXiv:1606.08111v3](https://arxiv.org/html/1606.08111v3). His explicit paths identify the candidate. Notes 14 and 18 provide a written functional evaluation and feasibility/area derivation for the corresponding normalized construction.
- Jineon Baek, *Optimality of Gerver's Sofa*, [arXiv:2411.19826](https://arxiv.org/abs/2411.19826). The sharp-majorant/equality-case organization is motivated by this work, not an application of its single-turn bound twice.
- The repository's [uniqueness manuscript](../paper/), particularly its arbitrary-maximizer and equality-case strategy. Its single-turn maximality hypotheses are not silently transferred to this different objective.

This is not a comprehensive literature review. Theorems, examples, and failures are committed for further scrutiny; the branch does not claim an independently verified new solution of the unrestricted problem.

## Execution constraints

Documentation only. No CI run was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Every research commit includes `[skip ci]`; workflow definitions are untouched. Keep the PR in draft while the unrestricted reduction and independent proof review remain unfinished.
