# Stationarity, deficit, and rigidity for Gerver's sofa

**[Read the manuscript](paper.md).** This is a separate working-paper PR investigating a simpler organization of optimality and uniqueness, not a replacement of the existing Lean sources.

## The result being developed

For the unit right-angled hallway, the proposed framework gives

\[
|S|\le|G|,\qquad |S|=|G|\iff S\text{ is congruent to }G,
\]

using the concrete Gerver shape and the original closed connected moving sofa. The global proof is written relative to explicitly retained geometric results of Baek, Gerver and Romik. It proves the upper bound before using it to identify every equality case.

## What changes

The arm iteration is replaced by one maximum-deficit estimate, with an error-tolerant extension. Persistent finite support samples select the specified maximizer without a tuned vanishing penalty. A single affine-minus-squares deficit identity gives the final upper bound and its equality conditions. Four first-order equations recover the cap; actual containment and target regular-closedness recover the starting set.

## What does not disappear

Baek's feasible fixed-angle attainment theorem is retained. An arbitrary cap-minus-niche set need not be connected, so deleting that theorem from the outline would leave a gap. The convex domain of Q, its geometric area comparison, and its first-variation calculation also remain substantial inputs.

This is therefore a noncircular reorganization, not a claim of a completely balance-free or independently self-contained replacement for Baek's paper.

## Detailed proofs

| File | Contents |
| --- | --- |
| [01-arm-bootstrap.md](01-arm-bootstrap.md) | One-step bound; additive-error version; exact counterexample when the interval is too long |
| [02-selection-and-stationarity.md](02-selection-and-stationarity.md) | Persistent selection, single-sample floating variations, pinned defects, endpoint-safe curvature limits |
| [03-deficit-and-rigidity.md](03-deficit-and-rigidity.md) | Exact deficit identity, four-interval kernel, cap Hausdorff bound |
| [04-angle-and-set-recovery.md](04-angle-and-set-recovery.md) | Exact angular inequalities, motion of the same sofa, corrected envelope lemma and exact-set recovery |
| [DEPENDENCIES.md](DEPENDENCIES.md) | Retained inputs, the noncircular dependency graph, source counterparts and proposed Lean migration |
| [RESEARCH_LOG.md](RESEARCH_LOG.md) | Positive/negative results, corrections, references and commit history |

## Verification boundary

These are mathematical manuscripts, not independently reviewed proofs. The existing uniqueness formalization is uncompiled research material. This PR runs no Lean, Lake, CI, Comparator or independent checker, changes no Lean declaration or theorem statement, and introduces no proof-source generator or external reference package. It does not certify the full repository's proof methods, axiom closure, or toolchain compatibility.

The generic scalar and Hilbert-space arguments are fully written out. The new geometric stationarity extensions and the overall reorganization remain review targets. A fully balance-free feasible-attainment theorem and a stability theorem for arbitrary moving sofas are not proved or assumed here.
