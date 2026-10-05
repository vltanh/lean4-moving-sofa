# Baseline observations (2026-10-05)

These are floating-point observations, not claims about a proven continuum optimum. Runs used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, a single BLAS thread, phi=0.04, 8-point cellwise quadrature, and three wall subdivisions per cell. The environment version is checked again in the final report. No CI was run.

## Positive: direct Q optimization recovers Gerver-like support functions

No Gerver path, Gerver support values, reference area, or reflection constraint enters `QProblem.solve`. Initial points come from LPs with random linear objectives. The objective does retain Baek's three-body formulation and cut-angle architecture.

| Uniform intervals per quadrant | Variables | Optimized discrete Q | Solver iterations | Maximum reduced Hessian eigenvalue |
| --- | --- | --- | --- | --- |
| 4 | 61 | 2.190843865010 | 21 | 7.68e-15 |
| 8 | 101 | 2.214767826129 | 28 | 9.20e-15 |
| 16 | 181 | 2.218310365199 | 73 | 1.49e-14 |
| 32 | 341 | 2.219201211357 | 137 | 2.96e-14 |
| 64 | 661 | 2.219448047610 | 157 | 5.45e-14 |

All five normalized-constraint solves returned success. Equality residuals were at most 4.45e-16 and inequality violations at most 5.69e-14 for seed 0. The reduced Hessian is negative semidefinite to numerical precision; this supports concavity of the implemented finite quadratic program, not a proof about its continuum limit.

An independent post-solve comparison loads `scripts/figures/gerver.py` and computes the analytic reference cap support as `1 + path(t).u(t)` and `1 + path(t).v(t)`, translated to the same horizontal gauge. Maximum errors over 4,097 normal angles were:

| Grid | Maximum sampled support error | RMS support error |
| --- | --- | --- |
| 4 | 0.0298702767 | 0.0129254077 |
| 8 | 0.00339800676 | 0.00141664005 |
| 16 | 0.00101758680 | 0.000407764967 |
| 64 | 0.000100548979 | 0.0000331432115 |

The 64-grid cap's Hausdorff distance from its own horizontal reflection was approximately 4.23e-7, despite no reflection constraint. This is numerical evidence of recovered symmetry, not a symmetry proof.

## Positive: independent starts agree

On grid 16, seeds 0,1,2,3 gave Q values respectively:

```
2.2183103651986977
2.2183103649093656
2.2183103652055460
2.2183103652064310
```

The spread is below 3.0e-10. Auxiliary-body variables need not agree: the Hessian has large flat subspaces (108 eigenvalues with absolute value below 1e-8 on this grid).

## Negative: sampled areas can look falsely better than Gerver

For the *same* grid-64 optimizer, subtracting a union of sampled niche wedges gives:

| Motion subdivisions | Sampled sofa area |
| --- | --- |
| 4,096 | 2.219600225523 |
| 16,384 | 2.219492433425 |
| 65,536 | 2.219465485030 |

The first number exceeds Gerver's known area (~2.21953) only because finitely many hallway positions under-sample the forbidden niche. It is NOT a counterexample. Even the last number is not a certified area for a sofa with continuous motion. A 20-second command timeout also interrupted the first grid-64 attempt; the completed grid-32 data survived, and grid 64 was subsequently rerun to completion (about 50 seconds of solver time in this environment).

Finite wall inequalities have a separate defect. The exact trigonometric maximum within every polygonal cell reveals maximum between-node wall violation 8.3666e-6 on grid 64. Also, polygonal support restrictions and the finite wall relaxation act in opposite directions: the optimized discrete Q is not automatically a lower or upper bound on the continuous maximum. Arbitrary B,D triples do not inherit the canonical-triple area inequality.

## Negative: low-order square-audit quadrature was insufficient

The independent Mamikon-square audit initially used 12-point quadrature. At grid 4 it gave a spurious decomposition residual 4.8868e-5, because the tangent-displacement integrands vary rapidly near a cut endpoint. Increasing the audit to 64-point quadrature reduced the maximum affine-restricted matrix residual to:

```
grid 4:  2.4336e-13
grid 8:  4.6185e-14
grid 16: 3.5527e-13
```

The main Q assembly integrates a different, smooth cellwise trigonometric expression; its quadrature must be tested separately. The audit implementation and regression tests are added in subsequent commits.

## Cut sensitivity: not a reliable discovery of the exact angle

At grid 16, cut parameters 0.02, 0.03, 0.039, 0.04, 0.05, 0.08, 0.12, 0.2 gave optimized Q values:

```
0.020 : 2.218306124332
0.030 : 2.218311018846
0.039 : 2.218309705144
0.040 : 2.218310365199
0.050 : 2.218327764179
0.080 : 2.218513645187
0.120 : 2.219493989704
0.200 : 2.225387555373
```

The coarse-grid minimum is not at Gerver's cut angle. It would be wrong to use this experiment as a discovery of that constant. Values outside the range justified in the source's geometric reduction are exploratory only. What works so far is numerical shape recovery under the existing Q architecture, not a candidate-independent construction of Q itself.
