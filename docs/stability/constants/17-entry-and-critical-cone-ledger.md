# Effective entry and the full-Q critical cone: continuation ledger

Base checkpoint: d31577916bfcdac0b854e67a922681a19a60b607 (PR #10).

The user requested the two outstanding research goals, not another decimal
improvement: a numerical entry certificate and the extra rigidity in the full
Q deficit. Formalization remains frozen. This continuation changes research
notes and Python experiments only and invokes neither Lean/Lake nor CI.

## Acceptance conditions

An effective entry result must either supply an actually verified positive
numerical separation gap outside the required neighborhood, or explicitly
state that it has not done so. A terminating search description alone is not
a computed epsilon0. A local cap-Q gap is not a global original-sofa area gap.

A critical-cone result must account for the first variation and both auxiliary
energies, with active wall constraints and convexity. Maximizing the cap-only
residual ratio over arbitrary functions does not answer this question.
Distinguish a rigorous relaxed upper estimate, a numerical discretization,
and an attained or limiting sharp constant for continuously feasible triples.

## Source inspection

WideGerverCertificate expresses minus the first variation as integrals of
nonnegative wall slacks against the two reference auxiliary curvature measures.
Their supports lie on [pi/2-theta,pi/2] and [pi/2,pi/2+theta]. Consequently zero
first variation should force the paired support perturbations to cancel on
those weighted arcs. This is more informative than a single scalar equation
when deriving a continuum relaxation.

The older source archives available in the conversation include a polygonal
Q optimizer and its quadratic forms. They may be used for exploratory critical
cones, but finite angle constraints and polygonal reference errors must not be
promoted to a continuous certificate.

Local access to raw GitHub via the runtime failed due to DNS resolution.
Repository reads and writes use the connected GitHub API. The mounted older
experiment archive is available locally for diagnostics; its provenance and
limitations will be recorded in any report that uses it.
