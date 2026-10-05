# Ambidextrous sofa: pen-and-paper research

Status: work in progress. This directory does **not** prove that Romik's sofa is globally optimal or unique. It develops explicit lemmas and isolates the missing sharp inequality. Results called proved below have written mathematical proofs, not Lean verification.

The work starts from `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`. It is separate from the uniqueness manuscript: none of that manuscript's claims or Lean files are changed.

## Scope

The target is a connected planar body that can traverse a unit-width corner in either direction of turning, with a common incoming body orientation. The two motions are independent; no reflection of the body is permitted during a motion. Reflection exchanges the two problems, but is not an assumption of symmetry of the optimizer.

A general two-motion formulation comes first. Monotone quarter-turn paths, a symmetric pair of paths, injectivity, separation of niches, and existence of a global maximizer are **not** assumed without a stated restriction or proof.

## Reading order

1. [Two-motion envelopes and connected saturation](01-two-motion-envelopes.md).

Further notes will develop overlap-aware area bounds, a fixed spatial partition certificate, two-sided variations, exact candidate constants, and a dependency ledger. The principal target is a sharp inequality with an explicit nonnegative deficit, not merely equations for a stationary candidate.

## Sources and attribution

- Dan Romik, *Differential equations and exact solutions in the moving sofa problem*, arXiv:1606.08111v3, especially Sections 2 and 5–6: https://arxiv.org/html/1606.08111v3 . Romik constructs the candidate; its feasibility and area are external inputs until independently checked here.
- Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826: https://arxiv.org/abs/2411.19826 . The proposed use of a sharp majorant and its equality case is inspired by this work, not a transfer of its single-turn theorem.
- The current repository's [uniqueness manuscript](../paper/). Its arbitrary-maximizer/equality-case organization motivates the research direction, but no single-turn maximality statement is imported for the two-turn objective.

No novelty claim is made for elementary envelope, measure, or convex-analysis lemmas. Every unproved geometric bridge will remain explicit.

## Working rules

Documentation only. Do not run CI, Lean, Lake, dependency installation, or a manuscript build for this research pass. Keep small commits and include `[skip ci]` in every commit message. Do not change repository-wide workflow settings. Do not promote a conditional certificate, numerical observation, or stationary-point calculation to a global optimality claim.
