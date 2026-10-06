# Paper-level completion pass: effective entry and feasible critical coercivity

Base: `84af27349720234b0cf3ac1adb9a591159ced997` (PR #10).
Formalization remains frozen. This pass changes analytic notes and reproducible
Python/certificate material only. No Lean, Lake, CI, or manuscript compilation.

## Acceptance gates

1. Effective entry for the unrestricted 2.3 theorem needs a numerical deficit
   that puts EVERY eligible original sofa in ALL required local certificate
   neighborhoods. An angle-only exclusion, a Q-triple threshold, and a finite
   algorithm whose run has not finished are distinct weaker results.
2. A two-sided bound for the feasible critical coefficient needs a continuously
   feasible family for its lower bound. A Galerkin eigenvector or a relaxed
   Green-kernel optimizer is not such a family. The coefficient must specify
   midpoint alignment versus optimization over all horizontal translations,
   and fixed zero-slack faces versus the asymptotic critical cone.
3. Numerical acceptance must be replayable from committed source and receipts.
   Exact rational/dyadic decisions are separate from floating-point diagnostics.
   No earlier status message substitutes for a rerun or a verified artifact.

## Initial review

The current full-Q note proves a strict relaxed upper bound using two auxiliary
penalties, then a quantitative endpoint-slack estimate. It does not identify
an attainable feasible mode. The current entry note reports a coarse angle
cover only; the near-right-angle shape exclusion is still missing. The PR body
and research index have not yet been updated to include these last twelve
commits. This continuation will distinguish the latest defensible theorem
statements from the stronger research goals.

The planned work is to test the certificate backend and active-face geometry,
seek explicit feasible critical directions, and strengthen the outer search
with finite missing-area and support-distance certificates that apply to actual
subsets rather than only their envelopes. Any exhausted or interrupted search
will be reported with its precise domain and surviving frontier.
