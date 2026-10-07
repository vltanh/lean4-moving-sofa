# Review boundary for the tangency-floor and half-width arguments

**The unrestricted optimal value remains unproved.** This records the new analytic deductions TF/HF and the short checks actually performed, not another proposed universal enclosure. The baseline is `03280a04151b0cf1a15c24b705f9aad4e12b28a0`; the new proof files are [TF](one-turn-tangency-floor-bound.md) and [HF](one-turn-half-width-top-face.md).

## 1. Dependency chain and scope

PA/WP/WR supply an arbitrary attained signed weighted maximizer, its selected finite polygons, bounded open-quarter curvature and half-height end edges. AR7 supplies the stronger same-sign inequalities. PT3 proves its top face is positive; TS1--TS2 then give niche height at most one half and endpoint arms at most 9/4. These are inputs, not re-proved historical infrastructure.

TF's controlled-oscillator comparison uses only those inequalities. It proves that the two single-wall tangencies are above the floor. Their baseline intercepts are therefore monotone, confining the full niche horizontally to the top-face interval. This is **not** an assertion of unit curvature or global exposure of those tangencies.

The symmetric two-turn construction now has zero clipping and area exactly 2 Psi(U). Applying AW-W to that genuinely feasible body proves W>2. Initial and final strict-quadrant tests show that the niche projection is exactly the open top-face interval.

HF proves convergence of the finite niche projection lengths using a specific uniform derivative estimate coming from WR's grid curvature bound. It does not infer projection-length convergence from niche-area convergence. Finite projection identities and EB.10 then give top length T=W/2.

After removing the half-height vertical segment and then the horizontal top segment, the cap has the exact Minkowski representation U=V+([0,T] times [0,1/2]), with convex V of width T and height one half, and a point top. The finite niche Green identity plus EB gives 2 Psi(U)=Per(V)-T. No sharp perimeter bound for these stationary cores is supplied.

## 2. Points checked in the argument

- TF1 uses a variable coefficient a(t) in [0,1], not a constant coefficient or the saturated ODE. Positivity of the two homogeneous response kernels is justified only for elapsed times at most pi/2, exactly the interval used.
- The q>=1 contradiction is applied only on the initial positive-q component. AR7 bounds all later positive-q components by 1/8. Without this distinction the initial-condition comparison would not apply.
- The reference comparison has a strictly positive rational margin. The narrow margin is kept exactly, not inferred from rounded trigonometric values.
- At an interior zero of a tangency height, the positive top face excludes q=-1 (or its reflected counterpart). This is needed for strict positivity, not merely nonnegativity.
- HF's uniform derivative convergence is derived from the non-axis grid curvature estimates. General Hausdorff convergence of convex bodies does not give this conclusion.
- In the baseline estimates for finite caps, their height H_n may be below one. The inequalities retain the favorable signs of H_n-1 rather than setting H_n=1.
- HF passes a finite **area** identity to the limit. It does not identify the actual perimeter measure of the limiting niche with the limiting exposed-wall measure: alternating polygonal walls can lose length in the limit.
- The zero-clipping conclusion applies to the symmetric construction from a weighted maximizer. It does not eliminate the positive G term for arbitrary two-turn cap pairs.

The correction [exposure-saturation-gap.md](exposure-saturation-gap.md) is part of the proof record. Actual exposure equals outer curvature in EB; it need not attain a larger local upper bound. The previous suggested contradiction from hidden exposure alone is not used.

## 3. Exact check actually executed

The standard-library checker [check_tangency_floor.py](computer-assisted/check_tangency_floor.py) was executed with an external five-second wall-clock cap. Its internal checks took less than one millisecond in the recorded run. It passed 18 named rational checks, including 54 rational instances of the stationary area identity, and two negative controls. The source matches fetched Git blob `c526fa787c63dc234f8a66e3dfc7c249d2b5fedc`.

[The recorded result](computer-assisted/tangency-floor-checks.json) gives the exact rational margin, source SHA-256, local version and measured time. Reproduce with:

```sh
timeout 5s python docs/ambidextrous/computer-assisted/check_tangency_floor.py
```

The timeout is external. The program does not certify the continuum comparison lemma, the geometric projections, or the entire historical dependency chain. Those claims have the written proofs described above and still need independent review.

## 4. Unsuccessful short exploratory tests

These did not establish new theorems and were not used as premises of TF or HF.

A midpoint linear-control relaxation was tested on a grid of 80 time cells with prescribed sign-transition indices. Eight models allowing one excessive endpoint arm were reported infeasible by the numerical solver. Sixteen models allowing two excessive arms and retaining the half-width face moment were also reported infeasible. Removing that face moment from the latter family gave one feasible sampled model, with indices [12,18,62,68], initial q about 1.19085 and final p about -1.14190. The other fifteen were reported infeasible.

All three runs used external ten-second caps. Their recorded solver-loop times were approximately 0.042, 0.084 and 0.067 seconds. They did not cover arbitrary transition times, certify rounding or continuum errors, validate cap realizations, or provide checked infeasibility duals. Therefore neither their infeasibility flags nor the feasible sample proves or refutes EA2. Their limited lesson is that the newly proved face moment should be retained in any future endpoint comparison.

A separate fixed-grid test of a crude rectangle-niche bound was too weak: its proposed weighted upper expressions remained above M/2 throughout the tested widths. It also had no certified quadrature error. It was abandoned rather than refined into a long computation.

The small control sources and outputs are preserved in the session's bounded-check bundle, separately from the exact TF checker. No multistart, interval covering or large search was launched. The current working policy caps new diagnostic invocations at 30 seconds and requires an explicit failure record if a timeout occurs; these checks finished below their stricter five/ten-second caps.

## 5. Still required for optimality

For the weighted one-turn value, EA2 for one attained maximizer is still sufficient and still unproved. Equivalently, one could prove the sharp bound Per(V)-T<=M for the stationary cores characterized by HF, but HF does not say every convex half-height core is stationary. A universal perimeter bound on arbitrary cores would be a different, unjustified relaxation.

For unrestricted ambidextrous area, a valid upper comparison must still cover bodies not obtained by the symmetric weighted-maximizer construction. General clipping, exceptional face placement, winding and actual angle coverage retain their earlier qualifications. Neither the new face ratio nor the stationary perimeter identity is a global optimum theorem.

All new arguments are written and self-reviewed. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Only docs/ambidextrous changed; uniqueness remains deferred.
