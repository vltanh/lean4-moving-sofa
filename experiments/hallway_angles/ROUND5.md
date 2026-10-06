# Fifth round: explicit global bounds and proof audit

Starting checkpoint: `ce09bb5910d86cd2f233ce52d2c3f3279a610836` (77 commits in PR #7).

The previous round asserts exact unrestricted near-reversal optimality with an unspecified cutoff. This round first audits its actual-set stability and flat-contact dependencies, then seeks explicit constants and a numerical interval. A flaw takes priority over extending a claim. No CI, workflow dispatch/rerun, or Lean build will be used. All changes stay inside this experiment.

## Targets

1. Replace existential uniform constants in the near-reversal argument by checkable bounds on a specified epsilon interval.
2. Try to bypass the full Hausdorff estimate in the final alignment step by using actual corner/support information and measurable contact patches.
3. Separate analytic derivations, whole-interval exact arithmetic, and supplementary numerical regression tests.
4. Record successful results and failed inequalities in separate incremental commits; do not silently turn a test into a proof.

## Initial audit

The current global proof invokes `REVERSE_SET_STABILITY.md` with normalized deficit d=e(V-area). Its delicate point is a two-sided containing-region estimate for possibly nonconvex sets, including endpoint-height points. The flat-contact width argument is valid conditional on that estimate. An explicit cutoff needs constants for the quadratic deficit, actual width, stationary path, and geometric contacts.

A direct clone again failed at DNS resolution; GitHub connector reads/writes work. This is not a CI attempt. Local source needed for checks will be retrieved or transcribed with Git blob checks. A current primary-source search found numerical competing branches in Xingyi He, arXiv:2608.11206, but no independently verified statement of the stronger theorem here. No novelty claim follows merely from that search.
