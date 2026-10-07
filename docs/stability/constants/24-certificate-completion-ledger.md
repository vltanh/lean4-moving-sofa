# Certificate completion and reproducibility ledger

Start: d0e15458ab79a119bde1b26318a0595c8edc1645, PR #10.
Formalization remains frozen. Only analytic notes, Python code and actual
computed receipts will be changed; no Lean, Lake, CI or manuscript build.

## Acceptance conditions

The intrinsic full-Q coefficient must distinguish the zero-slack face, the
asymptotic near-maximizer coefficient, and a finite-deficit estimate. A narrow
interval needs a continuously feasible lower family AND a uniform, executed
upper certificate. Floating-point diagnostic optima are not endpoints of a
proved interval.

Effective original-sofa entry needs an actually computed positive separation
outside the specified local neighborhoods, including near-right-angle motions.
Neither a Q-triple threshold nor a coarse angle exclusion is that separation.
A search with a surviving frontier must be reported as incomplete.

## Reproducibility issues found on inspection

The committed note 23 refers to `certify_feasible_trial_final.py`, but that file
and its defining rational Hermite data are absent from the current critical_cone
directory. Consequently its reported numerical lower family is not presently
replayable from this branch. A replacement must commit all data and recompute
the enclosure before presenting it as a reproducible numerical lower bound.

The all-pairs translation-quotient script is present, but no all-pairs receipt
is committed. This continuation will execute a complete cover or keep the
result explicitly inconclusive. The previously displayed approximately 0.93
upper value must not be treated as certified merely from a status message.

The existing coarse-entry notes also need replayable per-slab receipts, not
just aggregate counts. Earlier results are retained as historical claims while
these artifacts are checked and repaired.
