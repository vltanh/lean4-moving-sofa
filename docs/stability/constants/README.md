# Global stability constants: research ledger

Base: `a8f7719fd43fa91b223d9f6c0eb53594e5a95716` on `paper/uniqueness-arxiv`.
PR #8 is merged. This branch is separate from PR #9's coercive-route refactor.
The faithful Baek proof, main uniqueness proof, bridge, and manuscript are not
to be silently rewritten during this investigation.

The target is an explicit coefficient for arbitrary sufficiently near-optimal
sofas, not merely the explicit cap coefficient. Distinguish:

1. an explicit coefficient C with an existential positive entry threshold;
2. an explicit pair (C, epsilon0), which also requires effective local entry;
3. a sharp coefficient, requiring matching lower bounds;
4. a bound for ALL deficits, a stronger global-in-area question.

## Initial source findings

`LocalSofaRecovery.lean` still uses the coefficient 80 and the crude recovery
factor `4*(160+1)/kappa`. The sharper cap API is additive, so it has not yet
improved these assembled constants.

The source also replaces the angle allowance `B*epsilon` by `B*sqrt(epsilon)`.
This puts the terminal-angle constant into the leading coefficient even though
its effect is lower order. Keeping an explicit linear remainder should avoid
that loss, at the cost of reducing the entry threshold.

The missing-area argument uses a square strictly inside an interior ball and
then reserves half the ball for erosion. Using the exact remaining disk radius
and its area should give a substantially sharper recovery formula.

## Validation policy

No Lean, Lake, CI, remote build, or TeX compilation will be invoked. New Lean
proof terms are uncompiled source, not kernel-checked results. Non-Lean
algebraic/numerical checks will be recorded with their limitations. Commits
include `[skip ci]`, including negative results and source corrections.

No numerical global coefficient is claimed at this initial checkpoint.
