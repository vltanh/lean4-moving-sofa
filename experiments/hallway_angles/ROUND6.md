# Sixth round: stronger global interval and analytic branch comparison

Starting checkpoint: `9d08bce1b5c45cabea6c990e8965cfc238af699f` (91 commits in PR #7).

The targets were to lower the sufficient unrestricted-optimality cutoff and seek an analytic equation for the forward/reverse transition. The current statements remain mathematical proof drafts, not independently reviewed or Lean-checked. No CI, workflow dispatch/rerun, or Lean build was attempted.

## Results

1. **Global cutoff lowered from pi-1/19 to pi-1/8.** The new sufficient bend threshold lies between 172.838027560 and 172.838027561 degrees. Thus every 173<=beta<180-degree hallway is covered by the draft unrestricted optimality and uniqueness theorem. This is not the actual onset of reverse optimality.
2. **Curved interior cores replace the single flat-contact rectangle.** Explicit path constants improve to `(12/5)sqrt(d)+(7/5)d` and `(41/25)sqrt(d)+2d`. The width estimate first gives actual width above 0.97, then bootstraps to `1-w<=4d`.
3. **Every mismatch direction is covered with exact arithmetic.** Common inscribed candidate rectangles are verified over the whole e interval, including its removable endpoint. The successful compact record uses 64 e cells, 255 rectangles, and 1024 direction cells. It uses 65 rectangles and has minimum normalized margin above 0.005. A separate 128-cell run also passed with margin above 0.006.
4. **An analytic three-phase forward contact model was derived.** Its early phase is a radius-half wall pair; its central constant-coefficient Euler equation has a hyperbolic solution. Matching eliminates all but one contact parameter T, with A=1/3 and an explicit scalar equation F(beta,T)=0.
5. **A closed signed-area formula replaces curve fitting.** The expression W(beta,T) agrees with independent signed-area quadrature, boundary matching, and polygon-area convergence checks. Those checks do not establish global or continuous feasibility.
6. **The contact-model crossing is uniquely certified.** The explicit system F(beta,T)=0 and W(beta,T)=V(pi-beta) has one solution on beta in [135,140] degrees and T in [13/20,3/4]. Its bend lies between 136.672184698 and 136.672184699 degrees. F_T positivity and the decreasing implicit area difference are checked over whole intervals using automatic interval differentiation and interval-Newton tubes.
7. **A continuous central concavity lemma was proved.** Arbitrary fixed-endpoint H^1 variations have a strictly negative quadratic form; symmetry is not imposed. This is a theorem about the central functional, not all forward sofas or phase-switch variations.
8. **All 29 new local tests passed with no skips.** The combined reproduction checks pinned source hashes and records exact scalar bounds, proof hashes, and values at newly covered global angles. Earlier repository tests were not rerun wholesale.

## The exact phase-transition question remains distinct

The new beta_model is not yet an established unrestricted beta_c. A complete proof still needs the contact-boundary topology and continuous feasibility, a sharp upper bound for every forward-class competitor, and an unrestricted comparison excluding other motion/contact families near the model crossing. The near-reversal global theorem does not reach that interval. An exact model equation is useful progress toward the question, not a replacement of its quantifiers.

## Failed approaches retained

- Flat-contact-only estimates and direct endpoint contact enclosures were too wasteful. The successful argument uses larger interior rectangles and an integrated curvature height estimate.
- Direct fixed-precision trigonometric Horner evaluation near 2.4 radians produced valid but excessively wide intervals. Exact argument reduction fixes the enclosure width without modifying the mathematical formula.
- Large off-root derivative boxes were inconclusive. A certified root tube, after proving uniqueness in T, establishes the relevant implicit derivative.
- Coarse direction and crossing covers reject rather than accept midpoint evidence. The core checker refuses extrapolation outside its verified e interval.
- Sampled nonconvex polygons can have a small positive collision discrepancy. The diagnostics preserve it and do not label those polygons continuous-motion certificates.
- An initial combined test run hit the runtime's 45-second limit, although both groups passed separately. A successful smaller whole-interval cover reduced the workload; the complete 29-test run then passed. No result is claimed from the interrupted run.

## Reproduction and trust

Read `INTERIOR_CORE_GLOBAL_CUTOFF.md`, `CURVED_CONTACT_CORES.md`, `FORWARD_CONTACT_MODEL.md`, and `FORWARD_CENTRAL_CONCAVITY.md`. The failure log is `ROUND6_NEGATIVE_RESULTS.md`.

Run `python round6_check.py --output results/round6-checks.json` for the recorded combined checks, or run the two exact certificate commands separately as documented in the README. `requirements-round6.txt` adds the optional high-precision numerical regression package; the scalar proof commands use only the Python standard library.

The locally used baseline files matched their Git blob hashes. The committed main core checker, contact-model evaluator, and crossing checker were fetched again and their blob hashes matched the tested local files. The final compact record contains all relevant source hashes.

The analytic cap identity, canonical crossing/excursions, corrected width majorant, quadratic theorem, explicit reverse candidate realization, and alignment lemma remain dependencies of the stronger global result. Exact scalar certificates do not independently referee them. No Lean or CI verification is claimed.

A current primary-source check reconfirms that Xingyi He, arXiv:2608.11206v1, reports competing local numerical branches and a crossing near corridor-ray angle 43.327 degrees. No novelty claim is made for that phenomenon. The analytic contact equations and new global proof need a full mathematical and priority review.
