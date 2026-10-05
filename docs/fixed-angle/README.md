# Fixed net rotation angle: paper proofs and research record

This directory studies the prescribed **net rotation angle** in the usual unit-width, right-angled hallway. It does not change the hallway corner angle. The original uniqueness manuscript, Lean sources, and workflows are unchanged.

## Current result

For arbitrary nonempty compact connected sofas and admissible motions, including backtracking, the paper proofs establish

**`m(omega) = 1 + omega^2/2` for `0 <= omega <= 1` radian, with a unique normalized optimizer.**

At zero angle the optimizer is the unit square. At positive angles through one radian it is the sofa obtained from Baek's relaxed cap `K_(omega,1)` by deleting its actual niche. After fixing the two upper endpoint supports to one, the optimizer is unique as a set; without a fixed initial coordinate orientation, it is unique up to congruence.

The full angle problem is **not** declared closed: the optimal shape and uniqueness for `1 < omega < pi/2` are still unclassified in these notes. What is proved there is stronger than failure of one proof technique: `m(omega) < 1 + omega^2/2`, and the actual relaxed-cap sofa admits a strict feasible improvement for every angle in that interval.

These are paper-proof drafts with explicit imported inputs, not independently refereed or Lean-verified results.

## Start here

- [optimality-uniqueness.tex](optimality-uniqueness.tex): main unrestricted theorem on `[0,1]`, cap attainment, and equality recovery of arbitrary original sofas.
- [PEM.md](PEM.md): current proof-exploration memo, dependency audit, positive and negative results, and the remaining larger-angle problem.
- [beyond-one-radian.tex](beyond-one-radian.tex): all-angle strict relaxation gap and proof that the sharp value regime ends exactly at one radian.
- [redundant-angle-improvement.tex](redundant-angle-improvement.tex): an exact feasible perturbation proving that the relaxed-cap sofa itself is suboptimal above one radian.
- [REVIEW.md](REVIEW.md): mathematical audit and limits of the validation.

## Proof components

| File | Content and role |
| --- | --- |
| [fixed-angle-curvature.tex](fixed-angle-curvature.tex) | Transfers the companion's fixed-angle selection and floating variations to curvature bounds for **every** positive maximizing cap. Explicitly rules out the two outer endpoint atoms. |
| [arm-bootstrap.tex](arm-bootstrap.tex) | Three elementary bootstrap steps give strict arm inequalities on intervals of length at most one. |
| [all-angle-bootstrap.tex](all-angle-bootstrap.tex) | An exact rational certificate extends the arm inequalities to every physical angle below `pi/2`. |
| [monotone-majorization.tex](monotone-majorization.tex) | Horizontal monotonicity of the corner implies `A_omega <= A_1` without assuming fan containment. Equality recovers fan containment. |
| [relaxation.tex](relaxation.tex) | Concrete candidate geometry, feasibility and exact area through one radian, and the original strict quadratic gap. Its restricted-class theorem is a component, now strengthened by the continuation. |
| [relaxed-candidate-feasibility.tex](relaxed-candidate-feasibility.tex) | Direct feasibility of the cap-minus-niche family for every `0 < omega < pi/2`, without confusing feasibility with optimality. |
| [negative-results.tex](negative-results.tex) | An explicit feasible convex quadrilateral disproves universal `A_omega <= A_1`; endpoint atoms explain why maximizing-cap structure matters. |
| [stability.tex](stability.tex) | Qualitative Hausdorff convergence of arbitrary near-maximizers to the unique optimizer, at each fixed `0 < omega <= 1`. |
| [checks/arm_certificate.py](checks/arm_certificate.py) | Optional standard-library exact check of the printed rational certificate, independently using integer and Fraction arithmetic. Not CI. |

The non-circular proof chain is:

`cap attainment -> penalized selection -> floating defects -> fixed-angle curvature -> arm bootstrap -> monotone-corner area majorization -> strict relaxation gap -> regular-closedness recovery`.

The imported geometric inputs are the companion's fixed-angle cap/monotonization identities and its selection/first-variation results. The final Gerver optimality theorem and right-angle equality theorem are not inputs to the new small-angle result.

## What is established, by scope

| Scope | Paper result |
| --- | --- |
| `0 <= omega <= 1` | Exact unrestricted optimum `1 + omega^2/2` and uniqueness of the normalized sofa. |
| Fixed `0 < omega <= 1` | Every normalized near-maximizing sequence converges to that sofa in Hausdorff distance. No explicit rate is asserted. |
| Every `0 < omega < pi/2` | Every positive global maximizing cap satisfies the corner monotonicity and `A_omega <= A_1`. |
| Every `0 < omega < pi/2` | Baek's `A_1` has a unique normalized maximizing cap, by a strict quadratic gap and a one-ended Poincare inequality. |
| `1 < omega < pi/2` | The unrestricted optimum is strictly below the relaxed value `1 + omega^2/2`. |
| `1 < omega < pi/2` | The actual relaxed-cap sofa is feasible but strictly suboptimal; a smooth support bump leaves its niche unchanged and increases area. |
| General feasible caps | Universal `A_omega <= A_1` is false, even for a convex monotone sofa. |

## Earlier independent notes

[paper.tex](paper.tex) contains the zero-angle proof, elementary competitors, a quantitative strict endpoint-strip bound, and the abstract sharp-majorant interface. [small-angle.tex](small-angle.tex) gives an independent unrestricted asymptotic argument and the limiting missing-corner region

`D_0 = {x,y >= 0 : x+y+(x-y)^2 < 3/4}`, with area `5/24`.

The asymptotic value is superseded by the exact theorem on `[0,1]`; its geometric rescaling result remains separate. These earlier standalone notes describe their own original scope. Read this README and the PEM for the current project status.

## Remaining larger-angle task

The relaxed candidate cannot simply be continued past one radian. A whole early interval of its hallway constraints becomes redundant, allowing a strictly area-improving perturbation. The next exact optimization must account for the exposed niche walls and the positive correction `|N|-I(x_K)`. No convexity of that correction, new optimizer formula, or larger-angle uniqueness theorem is asserted here.

## Attribution and validation

Baek's *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, already contains the functional `A_1`, the candidate cap, and its relaxed maximum value. They are explicitly credited. The new notes supply the fixed-angle all-maximizer route, direct signed-area comparison, strict equality calculations, equality recovery, and the stated negative results.

Starting reference: `paper/uniqueness-arxiv`, commit `1ade045936f32cf76572ee668ed8aa1627772bde`. No CI, workflow dispatch, Lean compilation, axiom audit, or TeX compilation was run. Every research commit uses `[skip ci]`. Local symbolic and exact-arithmetic checks are described in the review; sampled geometry is not treated as a proof certificate.
