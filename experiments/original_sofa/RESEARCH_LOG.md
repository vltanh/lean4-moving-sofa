# Original right-angle sofa: computational research log

## Scope (2026-10-05)

Try numerical recovery of the original moving-sofa optimum and investigate whether the equality/concavity argument leads to a practical discovery algorithm. Keep successes, failed approaches, and limitations in commit history. This is an isolated numerical experiment, not a modification of the Lean proof or the paper.

Base: main at `16653ae81e0e4f52a362bafae2ad3440100ad065`.

No CI, Lean build, workflow dispatch, or workflow rerun is requested or used. All commits use `[skip ci]`; existing workflow definitions are unchanged. Only local numerical experiments and local tests will be run.

## 1. Source audit: the proposed discovery claim needs qualification

`MovingSofaOptimality/Optimality/Domain.lean` explicitly fixes the cut angle phi to Gerver's angle (with some geometric lemmas valid on a small interval). The paper's `docs/paper/sections/02-setting.tex`, subsection 'Baek's upper bound', on branch `paper/uniqueness-arxiv`, defines Q on triples (K,B,D), not on an arbitrary sampled support vector alone. Its admissibility conditions include convex bodies, inclusion, support inequalities, endpoint equalities, and the injectivity class.

Consequently a numerical program that inserts Gerver's cut angle is not a completely candidate-independent rediscovery. Likewise, the equality equations for h-h_G require the reference solution and do not supply the missing inhomogeneous optimization problem. Uniqueness for canonical triples does not by itself establish numerical conditioning or uniqueness of every relaxed/discretized triple optimizer.

Plan: audit Q's computational structure; build and validate an explicitly labelled geometric baseline; retain all failed relaxations or negative diagnostics; compare only after optimization with the known reference area. Finite angular sampling alone is not a certificate for continuous motion. A local solver is not a global optimality proof.
