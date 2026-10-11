# Third research round: publication-level theorem targets and outcomes

Starting checkpoint: `0a4000998d260c99c20a02eb13dead9b1810127c` (36 commits in PR #7).

The goal was a proved structural result, not simply larger floating-point candidates. Work was not restricted to the cap/uniqueness machinery. No CI, workflow dispatch, workflow rerun, or Lean build was used.

## Initial audit of the target

- The two aligned-endpoint motion classes had not been proved exhaustive. Statements about their suprema must not be labeled unrestricted sofa optimality.
- Excluding the forward class at 150 degrees was a pointwise statement, not by itself a theorem on the entire interval above 150 degrees.
- Opposite dominance at two parameter values does not establish a unique transition, nor even a crossing without an appropriate continuity argument.
- Existing numerical work already reports competing branches: Xingyi He, *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1. The approximate corridor-angle crossing 43.327 degrees corresponds to bend 136.673 degrees here. No novelty is claimed for that numerical phenomenon.
- At the start of this round, endpoint asymptotics for the unrestricted optimum were targets, not results. The existing midpoint upper bounds applied only to the aligned-endpoint classes.

## Completed derivation checkpoints

1. Derived a reverse-turn quadratic functional from the support-cap area and the signed corner integral. The first version was explicitly conditional on a monotone corner graph.
2. Solved its constant-coefficient Euler equation and proved strict concavity on the full continuous H^1 path space modulo horizontal translation. A separate Jacobi-field calculation handles asymmetric free endpoint abscissae.
3. Proved feasibility and exact area of the explicit convex candidate for every obtuse bend, using analytic geometry and exact-integer certificates for two scalar parameter inequalities.
4. Removed the monotone-corner hypothesis for epsilon<=pi/3 by proving monotonicity only inside the actual strip and bounding outside excursions by integration by parts.
5. Discovered that actual width cannot be assumed to be one and that the corrected quadratic upper bound alone does not force it. Combined the width-dependent quadratic with the midpoint bound, then certified the remaining scalar comparison.
6. Assembled an exact optimality and uniqueness theorem for the entire aligned reverse-turn class when 120 degrees<=beta<180 degrees. Competitors may be nonconvex, nonsmooth, asymmetric, narrow, and moved nonmonotonically.
7. Derived an asymptotically lossless alignment argument for arbitrary passages. An area-A sofa can be scaled into one of the aligned classes while retaining at least [A+sqrt(A^2-1)]/2 area. This is not an exact area-preserving reduction.
8. Combined the alignment bound and the reverse-class formula to obtain the unrestricted sharp asymptotic M(pi-epsilon)=C/epsilon+O(epsilon), where C=1.35653373245229... has an explicit trigonometric expression.
9. Certified a whole-interval forward-class exclusion for beta>=143 degrees, and outward-rounded scalar upper/lower bounds for the unrestricted problem.
10. Supplied the cap-area identity for nonsmooth convex hulls, recorded failed shortcuts, updated the reading guide, and passed all 31 new local tests.

The assembled statement and proof dependencies are in `REVERSE_MAIN_THEOREM.md`. Exact scalar evaluation and test results are in `results/theorem-checks.json`. Earlier conditional statements and negative experiments remain in the branch, with their limitations identified.

## What has and has not been established in this draft

The unrestricted asymptotic no longer assumes that the original sofa has a fully aligned rotation. The exact fixed-angle formula still pertains only to the aligned reverse class. Neither the forward class nor the unrestricted fixed-angle optimum is solved, and no unique global branch-crossing theorem is asserted.

These are new proof drafts supported by exact-integer computation, not independently reviewed or Lean-checked results. The certificate checkers contain no floating-point arithmetic, but their implementation and the ordinary mathematical derivations remain part of the trust boundary. The 31-test local run covers the new third-round modules, not a rerun of the entire older repository suite.

## Review and publication priorities

The strongest prospective paper structure is exact reverse-class optimality and uniqueness followed by sharp unrestricted near-reversal asymptotics. Before submission, independently review the support-cap identity, canonical-corner crossing and excursion estimates, variable-width correction, free-endpoint Hessian calculation, and alignment extension. Conduct a full literature/priority review rather than inferring novelty from an unsuccessful keyword search. A contemporaneous angled-corridor Gerver-family preprint surfaced during the search and is recorded in `ROUND3_NEGATIVE_RESULTS.md`.

## Sources and execution constraints

- He: https://arxiv.org/html/2608.11206v1
- Earlier bounds and certificate assumptions: `CLASS_BOUNDS.md`, `CLASS_EXCLUSIONS.md`, `INTERVAL_CERTIFICATES.md`.
- Further literature limitations and failed attempts: `ROUND3_NEGATIVE_RESULTS.md`.

A direct repository clone was unavailable in this runtime (DNS failure). All repository reads and writes used the GitHub connector; self-contained new code ran locally. This was not a CI failure and no CI was attempted. Existing Lean, paper, and workflow files were not changed.
