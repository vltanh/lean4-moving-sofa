# Ambidextrous sofa: pen-and-paper research

Status: **work in progress, not a proof of global optimality or uniqueness**. This directory contains written mathematical proofs, a candidate-level separation calculation, a conditional optimality/rigidity theorem, and an explicit ledger of missing hypotheses. None of these notes has been Lean-verified.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`.
The existing uniqueness manuscript and all Lean files are unchanged.

## The main result of this first pass

For a common convex outer set K and two removed niches U,V, the surviving envelope is E = K minus the union of U and V. Split the plane at the normalized midline and define

$$
P(K,U,V)=|K|-|U\cap\{y\leq1/2\}|-|V\cap\{y>1/2\}|.
$$

Then the following identity is exact:

$$
P-|E|=|(U\setminus V)\cap\{y>1/2\}|
      +|(V\setminus U)\cap\{y\leq1/2\}|\geq0.
$$

This is an upper bound **even for overlapping niches**. It does not require a universal separation theorem. Separately, [Note 4](04-romik-candidate.md) proves from Romik's explicit path formulas that his candidate's lower niche is strictly below the midline and its upper niche strictly above it. Hence this particular mask loss vanishes at the candidate, and remains zero under small independent path perturbations in the stated angular representation.

What is still missing is a tractable sharp global estimate for the clipped-niche functional (or a suitable further majorant), and rigidity of its equality case. The fact that this mask is tight at the candidate does not establish that global estimate.

## Reading order

| Note | Content |
|---|---|
| [1. Two-motion envelopes](01-two-motion-envelopes.md) | General motion witnesses, connected saturation, largest fixed-witness component, and regular-closed recovery. |
| [2. Niches and overlap](02-niches-and-overlap.md) | Exact common convex outer set, correct overlap sign, and a conditional geometric overlap budget. |
| [3. Partition certificate](03-partition-certificate.md) | Weighted and midline majorants, exact equality conditions, and robustness of candidate tightness. |
| [4. Romik candidate](04-romik-candidate.md) | Exact algebraic root bounds and a pen-and-paper proof of the strict maximum corner height below 1/2. |
| [5. Two-sided variation](05-two-sided-variation.md) | Common-pose normalization, masked gains/losses, exposed-boundary derivatives, and shared-arc one-sided terms. |
| [6. Optimality and rigidity](06-optimality-and-rigidity.md) | The five-defect identity, the precise conditional global theorem, and a quadratic comparison target. |
| [7. Proof ledger](07-proof-ledger.md) | Hypotheses, self-review, known failure modes, provenance, and the next proof obligations. |

## Scope and safeguards

The target is a compact connected planar body of positive area that can traverse a unit-width corner in either turning direction, with a common incoming body orientation. The two motions are independent. No reflection of the body is allowed during a motion; reflection exchanges the two feasibility problems instead.

General motions are used for the foundational envelope results. Monotone quarter-turn paths and Romik's contact pattern are used only where explicitly stated. No universal injectivity, separation, symmetry, or global-maximizer existence theorem is assumed. A single-turn maximizer replacement is not a valid substitute for two-turn maximality.

The overlap term has a **plus sign** in surviving area. Simply subtracting both full niche areas gives a lower bound, not the needed upper bound. The spatial partition is designed to avoid that double subtraction.

## Next substantive target

Develop a two-path first-order diagnostic at the candidate, then construct clipped-niche lower bounds sharp there. The resulting common-outer-set functional must be bounded globally on a covering normalized class and its equality directions identified. The precise required inputs are stated in [Theorem 17](06-optimality-and-rigidity.md); none is hidden inside an optimality assumption.

## Sources and attribution

- Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, [arXiv:1606.08111v3](https://arxiv.org/html/1606.08111v3), particularly Theorems 3–5. Candidate path formulas, feasibility, and area are attributed inputs. The scalar and height calculations in Note 4 are written derivations from them.
- Jineon Baek, *Optimality of Gerver's Sofa*, [arXiv:2411.19826](https://arxiv.org/abs/2411.19826). The sharp-majorant/equality-case organization is motivated by this work, not an application of its single-turn bound twice.
- The repository's [uniqueness manuscript](../paper/) motivates the arbitrary-maximizer/rigidity strategy. Its one-turn maximality hypotheses are not imported for the two-turn objective.

No novelty claim is made for these elementary lemmas or for the candidate separation calculation. This pass is not a comprehensive literature or priority audit. Written proofs, cited inputs, and open analytic steps are distinguished in the ledger.

## Execution constraints

Documentation only. No CI, Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Every research commit includes `[skip ci]`; no workflow definitions were changed. Keep the PR in draft while the sharp certificate and its rigidity remain unproved.
