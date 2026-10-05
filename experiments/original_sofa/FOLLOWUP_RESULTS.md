# Follow-up: cut/contact discovery and quantitative cap stability

This follows the original PR #6 experiment at a72e4ca. The work is confined to
`experiments/original_sofa/`. No CI or Lean build was run. The successive
commits preserve the initial failures and later recovery attempts separately.

## Main outcome: an analytic cap estimate

[CAP_STABILITY.md](CAP_STABILITY.md) gives a written deduction from the
continuous Q identities: for a normalized right-angle cap K in Baek's
injective class Ki,

    inf_s d_H(K, K_G + (s,0)) <= (12/5) sqrt(|G| - A(K)),
    A(K) = area(K) - area(N(K)).

This is an analytic argument, not an inference from eigenvalue plots. It has
not been Lean-checked or independently reviewed. It does not yet establish
stability for arbitrary near-optimal moving sofas or for the nonconvex shape
K minus its niche.

The key simplification is to discard the two nonnegative auxiliary-body
squares, rather than attempting to regularize all the flat B,D directions.
The Q deficit controls the four cap-square residuals. Integrating their
first-order equations, after removing horizontal translation, controls the
uniform support error. The proof gives an explicit constant around 2.326;
12/5 is a convenient conservative constant justified by rational bounds.

The independent cap-energy code finds uniform-norm constants 1.98397,
1.99716, 2.00046, 2.00130 and 2.00153 on meshes 4, 8, 16, 32 and 64. These
remain bounded while the smallest raw coordinate eigenvalue decreases.
The numerical calculation maximizes over each entire angular cell, not just
fan normals. It is a cross-check, not a proof of the best continuum constant.

## Correcting and testing the cut search

The earlier suggestion to maximize over the cut was incorrect. For cuts
where the continuous geometric reduction applies,

    M <= U(phi) = sup_{xi in T_phi} Q_phi(xi).

The sharp-cut search is therefore **min_phi U(phi)**. This does not establish
that the minimizing cut is unique, or that the discretized values are bounds.

`cut_search.py` uses the same polygon normal fan for every cut in a scan,
including the union of all tested cut normals. This removes the changing
approximation-space artifact from the earlier single-cut scan.

| Mesh | Q at cut 0.039 | Q at cut 0.040 | Smallest tested value |
| --- | --- | --- | --- |
| 16 | 2.218347806409 | 2.218347761812 | 0.040 |
| 32 | 2.219228816415 | 2.219228868396 | 0.039 |

The broader tested cuts were 0.02, 0.03, 0.035, 0.045, 0.05 and 0.06.
All 16 scan solves terminated successfully with small primal residuals.
However, the differences between 0.039 and 0.040 are only about 5e-8, while
finite first-order-gap LP diagnostics are around 1e-7 to 1e-6. Some of those
LPs report unboundedness, which is not evidence that the quadratic problem
is unbounded. Thus the scan does not resolve the exact minimizing cut with
an error certificate. Cuts outside [0.039,0.04] remain exploratory: the
source's geometric reduction is not asserted there.

## Geometric exposure detects a cut not supplied to the solver

`contacts.py` tests whether an inner-corner point is removed by another
hallway's forbidden wedge. Within each polygon-normal cell, it minimizes the
maximum of two sinusoidal wall slacks using endpoints, stationary points and
wall-switch candidates. The implementation is floating point, not interval
arithmetic. A coarse root scan locates the observed exposure events; it does
not prove that no additional events could occur for an arbitrary input.

For the two previously optimized caps, both with input cut 0.04:

| Mesh | First exposed corner angle | Last exposed corner angle |
| --- | --- | --- |
| 32 | 0.039441007526 | 1.531355036092 |
| 64 | 0.039196257260 | 1.531600238926 |

Changing the angular neighborhood excluded around the corner's own contact
among 0.1, 0.2 and 0.3 changes the roots by less than 1.1e-14. Gerver's
post-solve reference cut is 0.039177364790; the finest inferred first exposure
is about 1.89e-5 away. No Gerver path, theta, or phase ansatz is loaded by the
contact detector or optimizer.

The wall-slack detector also locates diagnostic transition intervals. On mesh
64, with tolerance factor 2, the left interval is
[0.67495155, 0.69504450] and the right one is [0.87576768, 0.89584478]. They
contain the post-solve reference angles 0.68130151 and 0.88949482, respectively.
These threshold-based intervals are **not certified enclosures**.

The first-departure detector failed on small mesh artifacts; see
[CONTACT_FAILURES.md](CONTACT_FAILURES.md). Replacing it with a longest-active-
plateau detector produced the useful intervals above, but quadratic and cubic
one-sided fits still give biased cutoffs outside those intervals. They are
explicitly marked `identified: false`, even when least squares succeeds.
The program has not recovered an exact contact pattern or generated its ODEs.

## Feedback finds mesh-dependent cuts, with mixed solver reliability

`cut_feedback.py` feeds the inferred exposed-core endpoints back into the
symmetric cut parameter. This is a geometric fixed-point heuristic, not a
proved implementation of the min-max problem. Shape reflection symmetry is
still not imposed. The normal fan changes when the cut changes.

On mesh 16, starts at 0.02 and 0.06 move toward approximately 0.0396958.
On mesh 32, the successful iterations move toward approximately 0.0394609.
These are mesh-biased values, not accurate recovery of Gerver's constant.
A `converged` status refers only to the finite feedback stopping rule.

Three initial finer-grid failures were committed before trying any repairs;
see [SOLVER_FAILURES.md](SOLVER_FAILURES.md). `solver_recovery.py` separately
projects to finite feasibility by an L1-distance LP and restarts SLSQP.
All three original failed cases then had successful repaired solves, but one
subsequent mesh-64 restart still failed. That later output is retained as a
failure even though its primal residual is small; its first-order gap is
about 5.9e-4.

The successful mesh-64 sequence from the 0.06 start was

    0.06 -> 0.0383467223 -> [initial failure]
         -> [repaired solve] 0.0392478529 -> 0.0392209648.

The last successful solve has a first-order-gap diagnostic about 2.0e-5, so
this is not a high-precision minimization result or a convergence certificate.
There is still no robust, exact-cut discovery algorithm.

## Tests, data and reproduction

**31 local unittest tests passed**: the 11 baseline tests and 20 new tests.
New checks cover continuous-angle extrema, independent square decomposition,
translation removal, the uniform cap norm, integrating-factor identities on
an independent smooth function, an exact rational constant check, common-fan
consistency, and explicit feasibility repair. Import checks verify that the
new discovery/stability modules do not load a Gerver reference. Tests do not
replace the mathematical proof or certify floating-point optimization.

[results/followup_summary.json](results/followup_summary.json) contains compact
row tables for all 16 scan solves, all 18 initial feedback solves, all six
recovery/follow-on solves, five stability meshes, and the contact diagnostics.
Failed rows are included. Null first-order gaps mean the gap LP did not return
a finite successful result, not zero error. Coordinates and raw logs are in
the supplementary experiment archive supplied with this session.

Run from the repository root after installing the existing requirements:

```sh
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python -m unittest discover -s experiments/original_sofa -v
python experiments/original_sofa/stability.py --output /tmp/stability.json
python experiments/original_sofa/cut_search.py --output /tmp/common_fan_scan.json
python experiments/original_sofa/cut_feedback.py --output /tmp/cut_feedback.json
python experiments/original_sofa/cut_feedback.py --intervals 64 --steps 3 \
  --output /tmp/cut_feedback64.json
python experiments/original_sofa/solver_recovery.py \
  /tmp/cut_feedback.json /tmp/cut_feedback64.json --steps 2 \
  --output /tmp/solver_recovery.json
# Use saved baseline solutions or regenerate them with q_experiment.py.
python experiments/original_sofa/contacts.py /tmp/sofa32.json /tmp/sofa64.json \
  --output /tmp/contacts.json
```

Failure locations can change with numerical libraries and stopping behavior;
these commands reproduce the experiments, not guaranteed bitwise traces.
The archived failed first detector is retained separately from the corrected
`contacts.py`; rejected fits and failed solver outputs are not overwritten.

## Assessment

The strongest advance is the explicit analytic stability estimate within Ki.
The discovery work gives a useful geometric cut detector and removes a major
outer-optimization mistake, but does not yet recover exact constants or an
analytic ansatz. Extending the cap estimate to arbitrary near-optimal sofas,
proving a certified discretization, and deriving ODEs from a validated contact
pattern remain open tasks of this project, not completed results.
