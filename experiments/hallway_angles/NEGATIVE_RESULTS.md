# Negative results and failed shortcuts

Failures are retained as part of the research record rather than discarded after successful runs.

## N1. The direct motion-area objective is not concave

This is an exact counterexample, already in the right-angle hallway. Use forward rotation `theta(u)=(pi/2)*u`, the strip `0<=y<=1`, and three corner-path knots at `u=0,1/2,1`. Both endpoint corners are `(0,0)`. Let `A` have middle corner `(0,0)` and `B` have middle corner `(0,3)`.

The continuous intersection for `A` is the unit upper semicircle, of area `pi/2`. For `B`, the endpoint hallways restrict all points to `[-1,1] x [0,1]`. At the middle angle the inner-wall condition is `|x|+y>=3`, which is impossible there. Thus `B` has area zero.

For the midpoint corner path `(A+B)/2`, the middle inner-wall condition is `|x|+y>=3/2`. Its intersection with that same rectangle comprises two triangles of total area `1/4`. Further hallway constraints can only decrease area. Therefore

$$A((A+B)/2)\le1/4<\pi/4=(A(A)+A(B))/2.$$

This also works for the largest-connected-component objective (each triangle has area `1/8`). It disproves concavity over the convex coordinate box used by the solver; one endpoint has empty intersection, so it is not a claim about some hypothetical smaller convex domain consisting only of nonempty sofas.

A floating-point check with 129 poses gives total areas `1.5708160403515905`, `0.1897113230666635`, and `0` for `A`, the midpoint, and `B`, respectively. The midpoint's largest component is `0.09485566153333175`. The exact argument, not those decimals, is the counterexample.

**Consequence:** the direct path search is nonconvex. The oblique Mamikon square identity cannot simply be substituted for an area-majorization theorem or the construction of the enlarged convex domain.

## N2. A solver can converge successfully to an infeasible sampled sofa

The first 9-knot, 33-pose, right-angle search returned optimizer status `success=True`, with sampled area `2.2316541712516575`. Holding its corner path fixed and increasing the pose count to 257 reduced the area to `2.214886142563717`; 1025 poses reduced it to `2.213028228128224`.

The corresponding margin-shrunken construction at 1025 poses has floating-point area `2.187465851663766`. The margin deliberately sacrifices area to handle all intervening orientations. None of these decimals is an interval-certified bound.

The path and parameters are retained in `results/coarse-grid-counterexample.json`. This is not an improvement on Gerver. A successful optimizer exit means its stopping criterion was met for the finite numerical objective, not that the sofa is feasible, locally optimal in the continuous problem, or globally optimal.

An even simpler exact warning is the stationary inner-corner motion checked only at `0` and `pi/2`: the accepted rectangle has area `2`, but `(1,1)` violates an outer wall at `pi/4`. The continuous intersection has area `pi/2`.

## N3. An affine hallway change does not preserve rigid motion

For the shear `A=[[1,1],[0,1]]`, the conjugate of a quarter-turn is `[[1,-2],[1,-1]]`, not an orthogonal matrix. Shearing the original sofa and its entire trajectory does not solve the oblique-hallway problem. This failure occurs before questions of optimality or uniqueness arise.

## N4. Full-circle rigidity is not a proof on partial contact arcs

The operator `D_beta` in THEORY.md has only translation modes in its full-circle kernel. On a proper contact interval, a smooth perturbation supported outside both that interval and its `beta`-shift can satisfy the local tangent equation without being a translation. Actual arc coverage, endpoint conditions, and gluing remain necessary.

## N5. A sharp arbitrary-angle Q was not obtained

The experiment derives an oblique corner formula and a square-gap operator, but not a sharp area majorant for all relevant sofas. Baek's original core/tail split is chosen using Gerver-specific parameters. It would be misleading to describe this PR as a convex program solving the arbitrary-angle moving-sofa problem, or as a global optimality/uniqueness theorem.

## N6. Float geometry is not a numerical certificate

The continuous-motion margin has an exact-real proof, but the implementation uses ordinary NumPy and GEOS calculations. A small floating-point guard and denser collision audit are useful checks, not a directed-rounding argument. The saved results therefore distinguish sampled area, inner-construction area, and analytic baseline areas. No computed global upper bound is claimed.
