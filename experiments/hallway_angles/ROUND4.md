# Fourth round: audit, stronger ranges, and exact global near-reversal optimality

Starting checkpoint: `69d0b5f15b4497c4ef4bcac265acb80706083b4f` (55 commits in PR #7).

The task was to strengthen the mathematical results, not only increase numerical search resolution. All new statements remain mathematical proof drafts, not independently reviewed or Lean-checked. No CI, workflow action, or Lean build was attempted. New work stays within this experiment.

## Initial priorities

1. Audit the cap-area, canonical-corner, width, and alignment steps for hidden geometric assumptions.
2. Try to extend the reverse-class theorem from bends at least 120 degrees toward the entire obtuse range.
3. Seek stronger unrestricted statements: quantitative alignment, stability, a limiting shape, or exact optimality on a nontrivial interval.
4. Separate optimal-class crossings from crossings of local numerical candidates.
5. Keep analytic arguments, exact-arithmetic certificates, and floating-point experiments separate; retain unsuccessful routes.

## Initial source and runtime checks

The primary-source search reconfirmed that Xingyi He's arXiv:2608.11206 reports competing numerical local branches, not a proved global transition. Hexagon 2610.00011 describes Guttesen's conjectural generalized Gerver family for bends at most 90 degrees. A later search for obtuse-hallway exact results did not replace a complete literature/priority review. No priority claim follows from these searches.

A direct clone failed because the runtime could not resolve github.com. GitHub connector reads/writes worked. Local dependencies were copied from fetched source; their Git blob hashes were checked against GitHub before the final test run. No CI was tried as a substitute for local execution.

## Completed research checkpoints

1. A sharper canonical-corner derivative estimate extended the geometric majorant to beta>=pi-arccos(sqrt(2)-1), approximately 114.4698 degrees. The same estimate has a genuine limit beyond that range; its failure is recorded rather than called a geometric counterexample.
2. A universal width threshold 983/1000 made a weaker reverse upper bound available at every obtuse bend. Endpoint-stable exact-integer formulas certified the width comparisons on the entire obtuse parameter interval.
3. An explicit all-angle circular-notch construction supplied a closed-form forward lower bound. Its right-angle special case is Hammersley's construction; no novelty claim is made for the family.
4. Exact-integer derivative and root checks gave ordered whole-class dominance below 133.644346373 degrees and above 142.098382576 degrees, with precisely defined comparison roots rather than an invented beta_c.
5. Compactness and strict-clearance perturbation proved attainment and local Lipschitz continuity of all three value functions. Thus at least one crossing of the optimal aligned-class values really exists; all crossings lie between the comparison roots. Uniqueness and a global phase-transition classification remain unproved.
6. Uniformly rescaled quadratic coercivity yielded path stability. A containing region with controlled missing area and an inball sandwich upgraded it to Hausdorff stability of actual, possibly nonconvex sofa sets. Endpoint-height spurs and degenerating fixed-angle constants required separate treatment.
7. Explicit boundary limits identified a universal convex shape, with O(e^2) convergence of the exact reverse optimizers after horizontal rescaling.
8. A scalar attempt to cancel alignment loss using width optimality failed: F_e'(1)-2V(e) has the wrong sign. The failure and a regression test are retained.
9. A different flat-contact argument succeeded in the draft. Near-optimality makes the rescaled shape error O(abs(nu)) after alignment, while the candidate's flat contact segments force a directional-width penalty of order abs(nu)/e. For all sufficiently small e, this forces nu=0. Hence the explicit candidate is the exact UNRESTRICTED optimum and is unique on a nonempty interval immediately below pi.
10. The same absorption argument improves unrestricted quantitative rigidity to O(sqrt(D)) relative to the finite-angle optimizer, and O(sqrt(D)+e^2) relative to the limit shape. It also identifies the next global area coefficient C1=0.09477330574913... in M(pi-e)=C/e+C1 e+O(e^3).
11. An analytic dependency audit showed that the sufficiently-small-e global theorem does not need any interval checker: all required signs follow from strict analytic endpoint limits. The checkers are used for the broader explicit class range and tight scalar brackets, not for the existence of the near-reversal interval.
12. All 37 new local tests passed with the fetched-source dependencies. The full older repository test suite was not rerun. Exact certificate outputs, rejected coarse covers, dependency hashes, and numerical profile errors are recorded in `results/round4-checks.json`.

## Current main result and limits

Read `EXACT_NEAR_REVERSAL.md`, then `ANALYTIC_NEAR_REVERSAL_FOUNDATION.md`, `FLAT_CONTACT_ALIGNMENT.md`, and `REVERSE_SET_STABILITY.md` Section 1.

The draft proves there exists e_1>0 such that M(pi-e)=V(e) and the optimizer is unique for all 0<e<e_1. It does NOT give a numerical value of e_1. None of the explicit class-comparison thresholds is substituted for that unknown global cutoff. The middle-angle forward family, exact beta_c, and uniqueness of the class crossing remain unresolved.

Independent review should focus on the geometric majorant and the uniform actual-set stability argument, which are not validated merely by passing the scalar or polygon tests. The final exact-alignment step depends on those analytic inputs. The original Lean libraries, existing paper, and workflows are unchanged.
