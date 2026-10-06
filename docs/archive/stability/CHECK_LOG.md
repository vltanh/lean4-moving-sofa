# Local validation log

These are implementation checks, not Lean verification or interval certificates. No CI or Lean build is run.

## First local run

Seventeen tests exercised the exact four-piece Green evaluation norm, independent numerical integration of its coefficients, reconstruction from an independently differentiated smooth function, junctions, the translation null direction, the sharp witness, rational constant bounds, and elementary geometric lemmas for the recovery step.

Sixteen passed. One failed in the endpoint stress check:

    D(pi-1e-6) = 1.000000000261576e-6
    asserted upper bound = 1e-6

The excess is approximately 2.62e-16. This is a floating-point comparison failure: forming pi-e and evaluating sine near pi does not retain the exact real inequality D(pi-e)<=e with zero absolute tolerance. The analytic inequality follows directly from sin(2e)<=2e. The diagnostic needs an absolute roundoff tolerance; the theorem and its constant do not change.

All independent quadrature/closed-form identities, reconstruction checks, and sharp-witness norm calculations passed in this first run. This failure was committed before the corrected script, rather than silently discarded.

## Corrected local run

All 17 tests pass with an absolute 4e-15 tolerance in the endpoint comparison. Python 3.13.5 and SciPy 1.17.0 were used. The command is

    python docs/stability/check_stability.py

The maximum discrepancy between independent kernel quadrature and the exact evaluation-norm formulas in the recorded audit is 1.3322676295501878e-15. The maximum independent reconstruction error is 7.077671781985373e-16. These floating-point checks support implementation consistency; they do not certify real arithmetic, prove all parameter values, or replace review of the analytic argument.

The local source SHA-256 is

    4b07d133e505ed8b9906cdc31b88bcdd6e8f9fa7a6b16d1b91d5f32d7f05e9e4

Its Git blob SHA is

    384e7b5feb746d7f354de255b758943356fe1d2d

The latter was compared to the blob returned by the GitHub connector after committing the file. Thus the committed script is the one tested locally. `checks-summary.json` records the audit values and the explicit false flags for Lean checking, arithmetic certification and CI dispatch.

## Negative mathematical controls

- Omitting horizontal translation is invalid: Delta(t)=cos(t) has zero residual energy but nonzero uniform norm. The cap theorem pins the left endpoint before applying coercivity.
- Continuity of area for nonconvex Hausdorff limits is invalid, even for connected sets: square-grid skeletons have area zero and converge to the filled unit square. The global argument uses only upper semicontinuity.
- Exact maximality does not supply an injectivity hypothesis for arbitrary near-maximizers. The global qualitative result and the quantitative Ki result are stated separately.
- Numerical tests of an interior-ball construction on a sample Lipschitz graph are not evidence that Gerver has that property. The proof establishes it directly by decomposing Gerver into two convex wings and a positive-height Lipschitz epigraph strip.
- No convergence of arbitrary original motion paths is assumed. The qualitative proof constructs a canonical motion for the limit from its support function.

## Verification boundary

The runtime has no Lean or Lake toolchain, and no Lean compilation was attempted. No CI was dispatched or rerun, and every research commit carries `[skip ci]`. `paper-section.tex` was not compiled and is not included in `docs/paper/main.tex`. Existing claims that the manuscript's theorems are kernel-checked have not been extended to these new written proofs.
