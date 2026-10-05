# Local validation log

These are implementation checks, not Lean verification or interval certificates. No CI or Lean build is run.

## First local run

Seventeen tests exercised the exact four-piece Green evaluation norm, independent numerical integration of its coefficients, reconstruction from an independently differentiated smooth function, junctions, the translation null direction, the sharp witness, rational constant bounds, and elementary geometric lemmas for the recovery step.

Sixteen passed. One failed in the endpoint stress check:

    D(pi-1e-6) = 1.000000000261576e-6
    asserted upper bound = 1e-6

The excess is approximately 2.62e-16. This is a floating-point comparison failure: forming pi-e and evaluating sine near pi does not retain the exact real inequality D(pi-e)<=e with zero absolute tolerance. The analytic inequality follows directly from sin(2e)<=2e. The diagnostic needs an absolute roundoff tolerance; the theorem and its constant do not change.

All independent quadrature/closed-form identities, reconstruction checks, and sharp-witness norm calculations passed in this first run. The failure is preserved rather than silently discarded. A corrected run and the checked script will be committed separately.

## Negative mathematical controls

- Omitting horizontal translation is invalid: Delta(t)=cos(t) has zero residual energy but nonzero uniform norm. The cap theorem pins the left endpoint before applying coercivity.
- Continuity of area for nonconvex Hausdorff limits is invalid, even for connected sets: square-grid skeletons have area zero and converge to the filled unit square. The global argument uses only upper semicontinuity.
- Exact maximality does not supply an injectivity hypothesis for arbitrary near-maximizers. The global qualitative result and the quantitative Ki result are stated separately.
