# Third-round negative results and corrected routes

These records are retained alongside the theorem drafts. Earlier failed arguments are not silently promoted to proofs when a later argument repairs them.

## 1. A signed corner integral is not automatically a swept-region area

The first reverse functional was justified only for a height-monotone corner graph spanning the entry strip. Canonical corners of arbitrary support caps can leave that strip. Simply integrating x dy over the whole path and calling it an excluded area was unjustified.

Resolution for e<=pi/3: the actual-strip height is monotone after clamping, and outside contributions admit an integration-by-parts upper bound. This is proved in `REVERSE_GENERAL_MAJORANT.md`. The same unrestricted majorant is NOT claimed for pi/3<e<pi/2, even though the explicit candidate remains geometrically feasible there.

## 2. Width one cannot be assumed for arbitrary competitors

If a sofa's actual height is w<1, its canonical corner endpoint heights are +/- (1-w/2), not +/-w/2. The uncorrected Q is not even horizontal-translation invariant: its change is -2(1-w) times the translation. Dropping this discrepancy would invalidate the area bound.

Resolution: add (1-w)(x0+xe)+(1-w)^2 cot e, derived from the outside excursions. The resulting width-dependent bound F_e(w) is translation invariant.

## 3. The corrected quadratic bound alone is still insufficient

For e=pi/6, the corrected quadratic relaxation gives F_e(0) approximately 2.799135, greater than F_e(1)=V(e), approximately 2.641025. This is a loose upper bound at width zero, not a feasible counterexample.

Resolution: combine it with the independent width-sensitive midpoint bound area<=w csc(e/2). The scalar comparisons in the main theorem exclude every w<1. Reproduce the failure of the single-bound approach with `width_majorant(pi/6,0)` and `width_majorant(pi/6,1)` from `reverse_exact.py`.

## 4. A symmetric numerical stationary point is not global optimality

Negative Hessians in finite-dimensional polynomial bases do not prove continuous concavity, and testing only symmetric variations misses the free asymmetric endpoint mode.

Resolution: the quadratic theorem proves strict negativity for H^1_0 variations using Poincare's inequality and separately evaluates the endpoint Jacobi field. The asymmetric mode is strictly negative, and the local tests compare its closed-form coefficient with independent quadrature. Symmetry of a maximizer is now a conclusion.

## 5. Coarse parameter intervals can be inconclusive

The exact-integer geometry checker with 8 cells rejects an inconclusive interval. It must not interpret this as either positivity or a mathematical counterexample. With 32 cells it passes; 64 cells give comfortably positive common lower bounds. The rejection is a regression test.

An initial pi regression test used a decimal upper bracket narrower than the outward 96-bit dyadic enclosure. The test expectation was widened to include the correctly rounded enclosure; the checker arithmetic and theorem certificates did not change.

## 6. Alignment does not preserve area exactly

No theorem here says every unrestricted sofa can enter one of the two aligned classes unchanged. The exit-strip argument may require uniform scaling by cos(delta/2). It preserves at least [A+sqrt(A^2-1)]/2 of an original area A>1, not all of A.

Consequently the unrestricted result is an explicit sandwich and the sharp asymptotic M(pi-e)=C/e+O(e). It does not identify the unrestricted optimum with V(e) at a fixed e>0.

## 7. The numerical branch crossing is still not a phase-transition theorem

The forward class is not solved. The exact reverse formula and a forward-class exclusion on beta>=143 degrees do not establish a unique crossing near 136.673 degrees. Previously recorded forward constructions can be compared pointwise with the exact reverse bound, but a unique global transition needs additional work.

## 8. Novelty and verification limits

Xingyi He's *A Gas-Driven Algorithm for Variants of the Moving Sofa Problem*, arXiv:2608.11206v1, already reports two competing numerical branches and their crossing. The pressure interpretation and the phenomenon itself are not new claims here.

A current search also surfaced Henrik Schou Guttesen's *A generalized Gerver sofa for angled corridors*, Hexagon 2610.00011. Its indexed abstract concerns bend angles 0<phi<=pi/2 and a conjecturally optimal generalized Gerver family. Only the abstract and author exposition were checked in this round, not the full paper. This must be included in a full priority review rather than assuming that an unsuccessful keyword search proves novelty.

The new analytic results and small exact-integer checkers have been reviewed in this research session only. They are not independently refereed, Lean checked, or CI validated. The original Lean libraries and paper are unchanged. A direct clone was unavailable because of runtime DNS failure; all repository reads/writes used the GitHub connector, and new numerical checks ran locally.

Sources: https://arxiv.org/html/2608.11206v1 ; https://hexagonmath.org/ ; https://theunbraid.com/ .
