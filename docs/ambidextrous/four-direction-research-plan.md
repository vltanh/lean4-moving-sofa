# Four research directions: one bounded first attempt each

**User request:** commit the different directions and try all of them. Baseline: `80fb626e5672d9bb66a52c88d4b1b027b6c62e11`. Neither general optimality frontier is proved. This is an experiment plan, not a new completion claim. All changes stay under docs/ambidextrous; no CI, Lean/Lake compilation, dependency installation or manuscript build. Each calculation uses an external short timeout. Preserve both successful and failed tests.

## Common acceptance criterion

The goal is a proof of ordinary area at most the explicit reference value M for every relevant actual body. A supporting result counts as a useful advance only if it eliminates a possible maximizing configuration, supplies a universal correctly signed area bound, or gives a complete reduction with its domain stated. A restricted-family calculation is not global admission. Finite-angle feasibility is not continuous-motion feasibility; a finite-angle outer bound, however, is valid without that stronger premise.

## D1. Structure of an actual maximizer

**Question:** Can two-turn maximality force the curvature or injectivity hypotheses of the existing sharp regular-hull theorem?

**Existing work to reuse:** Notes 53 and 54 already give piecewise quadratic finite geometry, a normal-cone stationarity equation, and a mesh-independent bound on raw area derivatives. The old generic pinching example prevents dropping connectivity multipliers merely because the mesh is refined. Do not relabel these results as new balancing theorems.

**First attempt:** identify a rigorous second-order test on feasible chart directions. Determine whether first-order balance can occur at a strict saddle and how an exact certificate could reject it. Retain the critical cone, hull retention and all geometric constraints. Test the rejection on exact finite polygon data, not on an untrusted cap tuple.

**Proceed only if:** a feasible nonzero direction with positive first variation, or zero first and positive second variation, can be certified. **Remaining gate:** prove such directions exist for a noncandidate maximizing configuration or classify the critical-cone obstruction. No automatic continuum curvature conclusion.

## D2. A genuinely coupled dual inequality

**Question:** Can forbidden material be charged without double-counting overlap, so a sharp ordinary-area bound is proved before optimizing an auxiliary expression?

**First attempt:** formulate a finite, overlap-safe dual certificate for the union of both forbidden sweeps inside a bounding convex region. Test its optimal weights on an exact arrangement where the unweighted swept-area sum gives a false bound. Inspect whether the dual remains valid when placements vary in a parameter box.

**Proceed only if:** every point is charged at most once and the resulting area inequality is an upper bound for all stated data. **Remaining gate:** construct a globally sharp or branchwise sufficient certificate tight at the reference. Local weights at one hull are not universal weights.

## D3. Finite-angle global exclusion and certification

**Question:** Can a small finite-angle outer problem exclude whole regions of possible hallway placements, leaving a rigorously defined residual for a local proof?

**First attempt:** compute exact areas of intersections of rational L-hallways, and produce an upper enclosure over a nonzero box of their offsets. Check whether a naive concavity assumption is false even in an exact low-dimensional chamber. Compare with the existing finite-angle and occupancy results before announcing novelty.

**Proceed only if:** the result certifies a full parameter region rather than a sample. **Remaining gate:** complete coverage of the global parameter space with a genuinely sharp residual theorem. No large search or unsupported claim that increasing resolution removes the fractional barrier.

## D4. Joint area versus missing-angle deficit

**Question:** Can the partial-turn correction be reduced using actual terminal strip widths, rather than paying the worst-case unit-strip allowance for every body?

**First attempt:** derive the exact geometric deletion region for two strips of possibly unequal widths at the ends of a missing-angle interval. Retain the ordinary-area/signed-fiber distinction and determine when the region is empty. Test it against the circular unit-strip allowance and the finite strip-bridge criterion.

**Proceed only if:** the formula controls the whole missing interval and can be combined with the actual visited/full fiber identity. **Remaining gate:** pay the remaining positive allowance by a proved area deficit or complete the same body. Connectedness of an arbitrarily deleted full envelope remains a separate issue.

## Reporting and stop rules

Each attempt gets its own note, with: exact inputs, actual derivation or executed calculation, failure controls, and the remaining implication. The final review ranks the attempts by their ability to address the global theorem, not number of lemmas or commits. Do not embark on additional special-case refinements after a direction's first test merely because they are available.

This plan deliberately explores four alternatives, as requested, without asserting that any succeeds. Historical written results remain self-reviewed and have not been independently verified by these new experiments.
