# Original sofa: numerical recovery using Baek's Q

**Status:** numerical experiments plus a written analytic cap-stability deduction. The numerical outputs are not certified bounds or a candidate-independent derivation of the objective. The analytic deduction has not been Lean-checked or independently reviewed. Changes are confined to this directory. No CI or Lean build was run; every research commit carries `[skip ci]`.

## Follow-up: cut/contact discovery and cap stability

Start with [FOLLOWUP_RESULTS.md](FOLLOWUP_RESULTS.md) for the current results and reproduction commands. [CAP_STABILITY.md](CAP_STABILITY.md) derives

```
inf_s d_H(K, K_G + (s,0)) <= (12/5) sqrt(|G| - A(K))
```

for normalized caps in Baek's injective class Ki. This is not yet a stability theorem for arbitrary near-optimal moving sofas. The proof uses the four cap-square residuals and does not require controlling flat auxiliary-body directions.

The follow-up corrects the outer cut search to min_phi sup Q_phi, runs common-fan scans, detects a geometric exposure cut 0.0391963 from the finest baseline cap whose input cut was 0.04, and records mesh-biased cut-feedback iterations. Exact cut/contact constants and an automatic ODE derivation have not been recovered. [CONTACT_FAILURES.md](CONTACT_FAILURES.md) and [SOLVER_FAILURES.md](SOLVER_FAILURES.md) preserve rejected fits and failed solves; later repairs are reported separately, including a remaining failed restart. Compact data for all successful and failed runs are in [results/followup_summary.json](results/followup_summary.json).

**The current local test suite has 31 passing tests**, including 20 new contact, coercivity, identity, common-fan and feasibility-repair tests. All material below describes the original fixed-cut baseline, before this follow-up.

## Baseline result

A direct three-body quadratic program recovers caps approaching Gerver's cap, without supplying its boundary, support values, reference area, or reflection symmetry to the solver. The cut parameter is fixed at 0.04. Gerver's analytic path is loaded **after** optimization, only by the comparison script.

| Intervals per quadrant | Discrete Q | Maximum sampled error in Gerver cap support |
| --- | --- | --- |
| 4 | 2.190843865010 | 2.9870e-2 |
| 8 | 2.214767826129 | 3.3980e-3 |
| 16 | 2.218310365199 | 1.0176e-3 |
| 32 | 2.219201211357 | 2.8534e-4 |
| 64 | 2.219448047610 | 1.0055e-4 |

The support comparison uses 4,097 directions and is not a proven Hausdorff error bound. Four independent LP starts on grid 16 agreed in Q to within 3e-10. No symmetry constraint was imposed; the grid-64 cap differs from its reflection by about 4.23e-7 in polygonal Hausdorff distance.

The six Mamikon squares were assembled independently of Q. Their sum cancels Q's quadratic part on the equality-constrained subspace to maximum matrix residual 4.89e-12 on grid 64 (64-point audit quadrature). This is a more discriminating implementation check than testing the Hessian eigenvalues alone.

See [BASELINE_RESULTS.md](BASELINE_RESULTS.md) for positive and negative observations, [INITIAL_FAILURES.md](INITIAL_FAILURES.md) for the failed first attempt, and [RESEARCH_LOG.md](RESEARCH_LOG.md) for scope and source caveats. Compact numerical data are in [results](results/).

## Reproduce locally

Run from the repository root, using Python 3.13 for the recorded environment. Dependencies are pinned to the locally tested versions; no packages are added to the Lean project.

```sh
python -m venv .venv-sofa
. .venv-sofa/bin/activate
python -m pip install -r experiments/original_sofa/requirements.txt
export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1

# Fast local tests; these are not GitHub Actions or a Lean build.
python -m unittest discover -s experiments/original_sofa -v

# Baseline refinement; output includes the full optimized triple variables.
python experiments/original_sofa/q_experiment.py \
  --intervals 4 8 16 32 64 --phi 0.04 \
  --validation-samples 4096 --output /tmp/sofa-mesh.json

# Independent starts.
python experiments/original_sofa/q_experiment.py \
  --intervals 16 --seeds 0 1 2 3 --validation-samples 4096 \
  --output /tmp/sofa-starts.json

# Use a single finest-grid record for the more expensive diagnostics.
python experiments/original_sofa/q_experiment.py \
  --intervals 64 --validation-samples 4096 --output /tmp/sofa64.json
python experiments/original_sofa/diagnostics.py /tmp/sofa64.json \
  --dense-samples 4096 16384 65536 --output /tmp/sofa64-audit.json
python experiments/original_sofa/motion_validation.py /tmp/sofa64.json \
  --subdivisions 4096 16384 65536 --output /tmp/sofa64-motion.json
```

The 64-grid solve used 661 variables and 157 SLSQP iterations, taking about 50 seconds in the recorded environment. This is a dense prototype, not a scalable implementation or a performance comparison with other algorithms. Solver details and small residuals may vary with numerical libraries. A `success` flag is never a mathematical certificate. Each completed run is written before starting the next one.

For the original cut sensitivity experiment, repeat the solver with `--intervals 16 --phi VALUE` for the values in `results/cut_sensitivity.csv`. Some tested cuts lie outside the interval used in the source's geometric reduction; those are explicitly exploratory. The follow-up common-fan scan is a different experiment and controls the changing approximation space.

## What is implemented

The source is [upperQ](../../MovingSofaOptimality/Optimality/UpperBound.lean), with background in [the optimality chapter](../../docs/proof/09-optimality.md). The equality identity is in [Rigidity.lean](../../MovingSofaUniqueness/Rigidity.lean).

The variables are support numbers of K,B,D on a common angular fan. Its uniform quarter-circle mesh is augmented by phi and pi/2-phi and replicated under quarter turns. K's lower half is determined by its two bottom corners. For every body, adjacent supporting-line intersections are linear in the variables; nonnegative edge lengths express polygon convexity. The program imposes B,D subset K, sampled inner-wall support constraints, four endpoint equalities, unit cap height, and the gauge h_K(0)=h_K(pi). One-sided polygonal arm inequalities f,g >= 1 are imposed at both ends of each cell. No reflection equation is imposed.

Q is assembled from the source formula

```
area(K) + J(left tail of D) + J(Y_D, x_K^L)
        - J(inner corner on [phi, pi/2-phi])
        + J(x_K^R, X_B) + J(right tail of B).
```

Polygon areas and tail arc areas are quadratic in the support numbers. The inner-corner term is integrated cellwise by Gauss-Legendre quadrature; its value is also checked under quadrature refinement. Linear equalities are eliminated, constant inequalities are checked and removed, and remaining inequalities are normalized. A random-objective LP supplies the initial feasible point; the LP alone uses a [-10,10] search box in reduced coordinates. The final SLSQP optimization does not use that box. The program saves original-coordinate feasibility residuals and the equality-reduced Hessian spectrum.

## Limitations established by the baseline experiments

**This is not yet a certified discretization of the continuous optimization problem.** Polygonal support restrictions shrink the search space, while finitely sampled wall inequalities relax some constraints. Those effects do not have the same sign. In particular the computed maximum of Q is not automatically a continuum upper bound, and an arbitrary (K,B,D) triple does not inherit the canonical-triple area bound. Polygonal arms are only a nonsmooth analogue of the source's regularity/injectivity hypotheses. The source's cap-area condition is checked at the reported solutions, not enforced throughout the feasible region.

**Finite motion sampling overestimates area.** For the fixed grid-64 cap, using 4,096, 16,384, and 65,536 motion subdivisions gives areas 2.21960023, 2.21949243, and 2.21946549. The first apparently beats Gerver only because it misses forbidden points. None is a certified lower bound. The exact within-cell sinusoidal check separately detects wall-constraint violation 8.37e-6, despite tiny residuals at imposed nodes.

**The full triple is not strictly concave after removing translation.** There are many auxiliary-body null directions. The uniqueness theorem for extremal caps does not imply uniqueness or good conditioning for every variable in this discretized triple. Quadrature near tangent endpoints can also be delicate: a 12-point square audit failed on coarse meshes; 64-point quadrature resolved that diagnostic discrepancy. The follow-up cap-only argument avoids the auxiliary-body null directions instead of penalizing them.

**The exact cut angle was not recovered.** The original coarse-grid scan had its smallest tested Q at phi=0.02, not at Gerver's angle. Treating the discretized value as a rigorous upper bound and minimizing it over cuts would be unjustified. The follow-up common-fan scan and geometric contact analysis improve this situation without certifying exact recovery. Baek's objective architecture remains an input.

## A conservative continuous-angle construction

Let K lie in the unit-height strip and in a disk of radius R about the origin. For a fixed p in K, the two inner-wall slacks are

```
f_p(t) = p.u(t) - h_K(t) + 1,
g_p(t) = p.v(t) - h_K(t+pi/2) + 1.
```

Both are 2R-Lipschitz: the unit-vector term is R-Lipschitz and so is the support function. With angular mesh spacing d, every angle is within d/2 of a sampled one. Remove, at every mesh point including both endpoints, the enlarged forbidden region where both slacks are below R*d. At any remaining point at least one slack is >= R*d at the nearest sample, hence is >= 0 at the actual angle. Outer-wall containment follows from K's support function. This proves the continuous hallway inequalities for the exact-arithmetic construction. Connectedness still has to be checked for the constructed set; the reported polygon has one positive-area component.

`motion_validation.py` implements this construction using the actual cap hull, clipped to the unit strip, and adds a small floating-point margin. It does **not** verify roundoff by interval arithmetic, so it explicitly reports `arithmetic_certified: false`.

| Motion subdivisions | Margin | Constructed area (floating point) |
| --- | --- | --- |
| 4,096 | 6.18865e-4 | 2.216853024905 |
| 16,384 | 1.54716e-4 | 2.218805640686 |
| 65,536 | 3.86791e-5 | 2.219293786995 |

This is a way to avoid treating a sampled apparent improvement as a solution. It is not an interval-certified lower bound or a new proof of optimality.

## Baseline local checks

The original 11 local tests passed: parameter validation, support interpolation, independent shoelace area, analytic gradient, main quadrature refinement, Mamikon decomposition, affine concavity and null directions, multi-start feasibility, nested sampling, conservative off-grid motion checks, and rejection of infeasible validation input. The current suite contains 31 tests; see the follow-up report above.

A one-sided, error-controlled discretization and an extension of cap stability to arbitrary near-optimal sofas remain substantive next steps. There is still no demonstrated discretization convergence theorem, exact recovery of Gerver's constants, or measured advantage over established sofa-search methods.
