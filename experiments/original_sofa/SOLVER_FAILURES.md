# Cut-feedback solver failures

The initial feedback runs are retained unchanged. A `success: false` result is
not used to infer the next cut, even when its objective looks plausible.

| Intervals | Initial cut | Cut at failure | Solver status | Minimum raw inequality residual |
| --- | --- | --- | --- | --- |
| 32 | 0.06 | 0.03946816009482712 | Positive directional derivative for linesearch | -7.4702105e-5 |
| 64 | 0.02 | 0.02 | Inequality constraints incompatible | -3.2423331e-4 |
| 64 | 0.06 | 0.038346722277668555 | Inequality constraints incompatible | -1.9778979e-3 |

All three runs satisfy the eliminated equalities to floating-point precision,
but none is a usable feasible solution. The first finest-grid failure started
from an LP-feasible point; the other two started from interpolated preceding
solutions that were not feasible after changing the cut. Therefore infeasible
warm starts are not a complete explanation of every failure.

## Separate certificate failure

The common-fan scan also tries an independent first-order-gap LP at each
computed solution. Some of these linear problems report unboundedness. This is
not evidence that the quadratic problem itself is unbounded: the linearization
at an approximate optimizer can be unbounded on an unbounded feasible domain,
even for a bounded concave quadratic maximization problem. Tiny errors in flat
or weakly controlled directions can also matter. The exact cause in each
instance has not been isolated.

Where finite first-order gaps are returned, they are roughly 1e-7 to 1e-6 in
the broad common-fan scans, larger than the approximately 5e-8 difference
between the optimized values at cuts 0.039 and 0.040. The experiment therefore
does not resolve a precise minimizing cut with an error certificate.

## Next recovery experiment

Project the failed/interpolated support vector to a feasible point by an
independent L1-distance linear program in the equality-reduced coordinates,
then restart the unchanged quadratic optimizer. Any repaired result will be
reported separately from the failures above, including the projection size,
new residuals, and solver status. No tolerance or infeasible result will be
silently relabelled as a success. No CI or Lean build is involved.
