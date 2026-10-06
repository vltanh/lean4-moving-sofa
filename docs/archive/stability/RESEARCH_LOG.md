# Stability proof work log

## Scope and starting point

Start from the paper branch at `51c9be18d5b50d45561bfb93cb82d1aabca549bc`, preserving the incorporated maximizer-first optimality route. This separate branch is for stability, not further numerical cut discovery. The earlier draft is `experiments/original_sofa/CAP_STABILITY.md` on `research/original-sofa-discovery`.

Targets, in order:

1. Audit and prove the continuous support-function/cap stability estimate from the Q deficit, with explicit normalization and regularity hypotheses.
2. Determine what can be proved for nonconvex sofas, and separate a genuine global theorem from conditional or qualitative statements.
3. Supply a manuscript-ready proof and checks without claiming unperformed Lean verification.

All commits carry `[skip ci]`. No CI is to be dispatched or rerun. Existing formalization/audit claims are not to be enlarged by uncompiled code or unreviewed mathematics.

## Initial audit

The draft's four cap residuals have a translation kernel. Fixing the top support and the left endpoint removes it. The two auxiliary-body energies are nonnegative and can be discarded; strict concavity in all three bodies is unnecessary.

The draft proves an estimate only for K in Baek's injective class Ki. The exact-maximizer reduction does not imply that every near-maximizer belongs to Ki. Any assertion for arbitrary near-optimal sofas must address that gap rather than silently reuse the exact theorem.

The present runtime has no `lean` or `lake` executable. An attempted public git clone failed because container DNS cannot resolve github.com; repository reads and writes remain available through the GitHub connector. These are environment limitations, not mathematical evidence.
