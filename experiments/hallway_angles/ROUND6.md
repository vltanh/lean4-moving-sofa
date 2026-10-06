# Sixth round: stronger global interval and analytic branch comparison

Starting checkpoint: `9d08bce1b5c45cabea6c990e8965cfc238af699f` (91 commits in PR #7).

The targets are to lower the sufficient unrestricted-optimality cutoff and seek an analytic equation for the forward/reverse transition. The current statements are mathematical proof drafts, not independently reviewed or Lean-checked. Auditing their premises takes priority over extending them. No CI, workflow dispatch/rerun, or Lean build will be attempted.

## Questions and distinctions

1. Can the contact-core proof keep the exact rectangle-strip overlap, energy splitting, and parameter-dependent constants rather than the coarse uniform triangular-cap estimate?
2. Can an analytic forward family be derived near the numerical crossing? A stationary candidate is not automatically the optimum of its motion class.
3. Distinguish three angles: a sufficient global cutoff; an intersection of two explicit feasible families; and a unique transition of unrestricted global optima. An exact equation for the second is not a proof of the third.
4. Preserve failed inequalities, infeasible candidates, and inconclusive interval certificates. Numerical evaluation will not be labeled a global upper bound.

A current primary-source search confirms that Xingyi He, arXiv:2608.11206, reports an intersection of local numerical branches, not a global transition theorem. The generalized-Gerver abstract at Hexagon 2610.00011 concerns bends at most pi/2 and conjectural optimality. These source checks do not establish priority of any new result.

Direct git/raw downloads failed at DNS resolution in this runtime; the GitHub connector remains available. Local computations will use fetched or transcribed code with source checks where applicable. This is not a CI failure.
