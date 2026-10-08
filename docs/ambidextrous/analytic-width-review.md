# Review of the analytic width-at-most-two replacement

## Result and dependency chain

[Theorem AW-W](analytic-width-theorem.md) proves |S|<41/25 for the width-at-most-two class. Since 41/25<411/250<M, it is stronger than the prior computer-assisted exclusion and gives the same width-greater-than-two conclusion for every global maximizer.

The complete analytic chain is:

```text
an actual body of area > 8/5 and horizontal width <= 2
  -> all four complementary-angle positions are actually visited
  -> canonical supports have nonnegative endpoint deficits
  -> disjoint lower/upper loss regions in the 2-by-1 rectangle
  -> either one single-hallway loss is already > 9/50,
     or AL1 puts all complete loss triangles inside their assigned regions
  -> mixed area bounds the union of the two inner triangles
  -> a convex four-variable surrogate reduces to two variables
  -> its explicit stationary minimum is globally valid and > 9/50
  -> each independent turn removes > 9/50 in disjoint counted regions
  -> ordinary area < 2 - 18/50 = 41/25.
```

The only classical theorem beyond elementary convexity and integration is planar Brunn--Minkowski, used through the mixed-area inequality derived in LP2. The proof does not use the adaptive functional, any curvature bound, any theorem about proximity to Romik, or the computer-assisted certificate.

## Checks of the potentially dangerous steps

**The motions are independent.** LP1 applies separately to the two sets of support offsets. Symmetry is used only to average parameters of the convex surrogate Psi. It is not an operation on feasible bodies.

**No double subtraction.** Half-height clipping confines the two counted losses to disjoint vertical halves, with their roles reversed in the middle band. This remains valid if the actual four-position envelope is disconnected or has empty fibers.

**No unproved full-angle extension.** The larger selected angle has cosine sqrt(2/5)>5/8. A body above 8/5 must visit it by the existing two-strip argument. The proof does not sample beyond its reduced endpoint.

**No assumed triangle containment.** Whole-triangle mixed area is used only after AL1. That lemma begins with a globally valid lower bound that subtracts overestimates of the omitted tent tails and keeps the half-height cutoff. It proves the required containment from a hypothetical small-loss condition.

**All parameter regimes are covered.** The low sublevel of L is localized using convexity on D, four minimized boundary quadratics, and concavity in each far tail. A stationary point of a polynomial is not declared a global optimum outside its domain. The later stationary point is global because its containing surrogate F is convex on the whole plane.

**The clipping knot was checked explicitly.** At e=1/2 the localization lower bound agrees with its quadratic along the boundary, but not throughout an open neighborhood on the clipped side. Its value and tangent derivative are enough. An early overstatement of neighborhood agreement was corrected in a separate commit.

**Mixed-area constants.** The reference triangles have area (r+q)/2 and mixed area r. Their normalized ratio is exactly 6/5. For their intersection C, monotonicity and Minkowski give |C|<=(5/11)(A_1+A_2), yielding the required 6/11 union coefficient. Degenerate intersections or triangles are handled separately.

**Scalar constants.** The four boundary estimates in AL1 list rational expressions and positive rational differences from 9/50. The two-variable stationary point has v/u=6/5, strictly between the two line-ordering boundaries 1 and 3/2. Its remaining tent height parameter is 55*kappa/109>0. The candidate-area comparison uses only the increasing cubic and arctan(z)>z-z^3/3 at z=149/500.

**Scope of the conclusion.** The proof excludes narrow bodies. It does not prove the unrestricted sharp value, a global curvature theorem, or an exact optimum for the new four-position relaxation. In particular, the stationary value of the convex loss surrogate is not being advertised as the exact ordinary-area optimum over all placements.

## Discovery versus proof

The old certificate motivated retaining finitely many hallway positions but changing the analytic decomposition. Local floating-point exploratory evaluations were used to compare partitions and complementary angle choices. Scratch rational arithmetic also checked the displayed scalar fractions. Those activities helped discover the argument; no output of them is a hypothesis, leaf certificate, or verification step in AW-W.

The final directions, partition, inequalities, derivatives, and rational comparisons are all supplied explicitly. A reader can check the result using only the three mathematical notes, without Python, a solver, the old binary tree, or a generated case list. This is removal of computer assistance from the **proof**, not a claim that computers played no role in its discovery.

The simplest two-diagonal relaxation was rejected for an exact geometric reason, recorded in [AW-D1](analytic-width-diagonal-obstruction.md): it admits area 4sqrt(2)-4. The accepted proof uses two distinct complementary directions for each turn.

## Preservation and execution

The existing `computer-assisted/` code, theory, binary hashes, and recorded runs are retained. Their theorem is superseded as the needed width exclusion, not retracted by this analytic improvement. The historical reproduction instructions remain useful for comparison.

This continuation changes only Markdown under `docs/ambidextrous/`. It does not run or modify the old certificate generator or verifier. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. Every commit includes `[skip ci]`.

This is a written proof with self-review. No independent mathematical refereeing, kernel verification, or novelty/priority claim is asserted. The unrestricted proof remains open for the separate reasons stated in the research index.
