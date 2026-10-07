# Analytic continuation: recovery geometry, alignment, and effective entry

Start: f95fe45c4194ecc95d46ad5427bf58db2dcae157 (PR #10).
The user has frozen formalization. This continuation changes analytic notes and
Python experiments only: no Lean source, Lean/Lake invocation, CI, or manuscript
build. Intermediate failures and scope limitations will be retained in commits.

## Questions

1. Replace the vertical Lipschitz-roof ball construction behind coefficient
   30.5 by Euclidean local boundary geometry. A steep smooth graph is not a
   narrow Euclidean cone; its tangent can be rotated. Actual corner opening
   angles, not the largest slope in fixed coordinates, should govern recovery.
2. Try a Euclidean-normal version of the adaptive-angle hallway witness. The
   old forward factor 10.2 measures vertical displacement and may also be a
   coordinate loss.
3. Study the cap estimate modulo translation, separating the abstract residual
   space from feasible cap/triple perturbations. Do not infer feasibility from
   an arbitrary residual extremizer.
4. Reassess the numerical entry threshold. Local quantitative data alone do
   not prove a global separation gap. Any computed local radius remains
   conditional until that gap is controlled.

## Initial hypothesis, not yet a result

If all corners of the actual Gerver boundary have interior angle at least pi/2,
then its fixed piecewise regular boundary may allow every interior-ball ratio
strictly below sqrt(2)-1 at sufficiently small scales. Combined with the current
split budget this would reduce the reverse coefficient below 7. This requires
checking EVERY junction and proving a uniform small-scale statement, rather
than sampling normals or treating a vertical slope bound as a corner angle.

The forward direction and effective entry must still be handled separately.
The reference algebra and cap coercivity from previous notes remain inputs;
the whole enlarged theorem is not re-verified by this continuation.
