# Fifth round: explicit global bounds and proof audit

Starting checkpoint: `ce09bb5910d86cd2f233ce52d2c3f3279a610836` (77 commits in PR #7).

The previous round asserted exact unrestricted near-reversal optimality with an unspecified cutoff. This round audited that argument's stability dependency and replaced it in the final proof by a direct contact-core estimate. No CI, workflow dispatch/rerun, or Lean build was used. All changes remain inside this experiment.

## Initial targets

1. Replace existential uniform constants by checkable bounds on a specified epsilon interval.
2. Bypass the full Hausdorff estimate using canonical corner/support information and measurable contact patches.
3. Separate analytic derivations, whole-interval exact arithmetic, and supplementary numerical regression tests.
4. Commit successful and failed steps without turning tests into geometric proofs.

## Completed checkpoints

1. Read the flat-contact and actual-set stability dependencies. The earlier width argument was conditional on a delicate uniform two-sided set estimate; no independent verification of that full estimate is claimed here.
2. Derived `CONTACT_RECTANGLE_LEMMA.md`. A coordinatewise path error yields an explicit rectangle in the majorant region. A small missing-area bound controls its directional width through two triangular caps.
3. Proved `EXPLICIT_PATH_CONSTANTS.md`. Keeping the two-coordinate trace matrix, rather than only its smallest eigenvalue, gives uniform errors `(5/2)sqrt(d)+(7/2)d` and `(17/10)sqrt(d)+5d` on e<=1/10.
4. Checked ten scalar bounds on the whole closed interval [0,1/10], including the removable endpoint at zero, using 256 exact-integer interval cells.
5. Assembled the explicit unrestricted theorem on 0<e<=1/19, including all bends 177<=beta<180 degrees. The final rational contradiction margin is 166189/7125000. The numerical sufficient left endpoint lies between 176.984432657 and 176.984432658 degrees.
6. Retained the failed cutoff 53/1000, the rejected single-cell cover, and an exact counterexample to omitting the triangle-regime condition. No failure is mislabeled as a counterexample to sofa optimality.
7. Derived explicit near-optimal motion rigidity on e<=1/100: mismatch at most 40e sqrt(D), width deficit at most 11D, and a clipped all-sofa area penalty. The tiny-mismatch case needs a separate argument when the triangular-cap regime fails.
8. Added one-command reproduction with baseline source-hash checks, exact value enclosures at 177/178/179 degrees, complete scalar proof hashes, and local tests.
9. Ran all 22 new local tests successfully with no skips. The compact record is `results/round5-checks.json`.

## Result and dependency audit

The strongest current entry point is `EXPLICIT_GLOBAL_CUTOFF.md`. Its proof no longer needs the full Hausdorff/inball estimate or universal limit-shape convergence. The cap-area identity, canonical crossing/excursions, strict quadratic maximization, explicit candidate realization, and alignment-by-scaling remain analytic dependencies. Exact scalar certificates do not independently validate them. The result remains an unrefereed, non-Lean mathematical proof draft.

The cutoff is sufficient, not a phase-transition value. No unrestricted fixed-angle conclusion at 150 or 170 degrees, no exact middle-angle forward branch, and no unique global crossing are added. The older separate results are retained, not silently re-audited by the 22 new tests.

## Sources, environment, and reproducibility

A direct clone failed at DNS resolution; connector reads/writes worked. The local copies of `parameter_certificate.py`, `width_certificate.py`, and `reverse_exact.py` matched their fetched Git blob hashes. The new main checker and its primary test module were also compared to their committed blob hashes. No CI or workflow was attempted.

The local record uses Python 3.13.5, NumPy 2.3.5, and Shapely 2.1.2 for supplementary tests. The scalar proof commands use only the Python standard library and exact integer/rational interval arithmetic. Run `python round5_check.py --output results/round5-checks.json` from this directory.

A current primary-source search reconfirmed numerical competing branches in Xingyi He, arXiv:2608.11206. A full priority review remains necessary; an unsuccessful keyword search is not evidence of novelty.
