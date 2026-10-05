# Initial numerical failures (2026-10-05)

The first local prototype implemented the `upperQ` formula using three polygonal support vectors, exact polygon arc areas, and cellwise Gauss-Legendre integration of the inner-corner curve. No Gerver boundary, symmetry constraint, or reference area was supplied to the optimizer. The cut parameter was fixed at 0.04, not optimized.

## Failure 1: SLSQP stopped at a feasible LP vertex

Parameters: 4 uniform intervals per quadrant (plus the two cut normals), phi=0.04, 3 wall samples per cell, 8-point quadrature, seed=0.

Observed output:

```
variables = 61; reduced_variables = 55
success = false
message = Inequality constraints incompatible
iterations = 1
Q = 1.6182251899252433
cap_area = 1.858486636889554
equality_max_abs = 4.440892098500626e-16
inequality_min = -4.951594689828198e-14
Hessian max eigenvalue = 7.679854604370008e-15
Hessian min eigenvalue = -38.56315715995901
Hessian near-zero count (abs < 1e-8) = 36
```

This is not evidence of a small optimum: the solver never moved. Equality elimination leaves some inequalities numerically constant, and many others have very different scales. The next revision will remove constant rows after checking their consistency and normalize the remaining rows.

The near-zero Hessian eigenvalues also disprove the expectation that fixing horizontal translation makes the full triple objective strictly concave. Large parts of the auxiliary bodies B,D do not occur in Q. Cap rigidity at the optimum does not mean uniqueness of every triple variable.

## Failure 2: polygon validation crashed

On the next grid the geometric validator encountered a GEOS `TopologyException: found non-noded intersection`, involving repeated cap vertices with y-coordinates about -6.7e-12, 0, and -3.3e-16. The command exited before writing its combined JSON output. This failure must not be silently converted to a successful result.

The next validator will build a convex hull of the computed cap vertices, report its area discrepancy and original linear feasibility residuals, and refuse to validate substantially infeasible solver output. Taking this hull is numerical cleanup, not a proof of continuous motion. All dense-angle areas remain sampled geometric diagnostics.

## Positive observation, not yet a result

The equality-reduced Hessian was negative semidefinite to floating-point accuracy on the first grid. That supports the implementation direction, but does not by itself validate all formulas or admissibility conditions.
