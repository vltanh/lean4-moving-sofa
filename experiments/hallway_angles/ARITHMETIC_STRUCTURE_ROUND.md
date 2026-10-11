# Structural arithmetic round

Starting checkpoint: `2393d5a400e7062846365e1f07a2a1b2e91868b5` (138 commits in PR #7).

The immediate target is the analytic contact-model crossing, not an already identified unrestricted phase transition. This round will audit the existing arithmetic arguments and seek stronger structural conclusions from BOTH the contact equation and the crossing-area equation. Merely increasing a finite Farey denominator bound is not the main objective.

## Priorities

1. Reproduce the latest exact arithmetic certificate where possible, checking the claimed margins and its analytic prerequisites.
2. Try to replace the conditional exclusion of rational multiples of pi by a conditional exclusion of all algebraic directions. Distinguish algebraic radians, algebraic trigonometric coordinates, and finite exp/log expressions.
3. Investigate elementary-expression towers under Schanuel, rather than treating transcendence or a function-level inversion obstruction as a constant-level non-elementarity proof.
4. Record failed reductions and any corrections with the same prominence as positive results.

All new work stays within this experiment. No CI, workflow dispatch/rerun, or Lean build will be attempted. Local symbolic or numerical tests do not independently validate the underlying geometric theorem drafts.
