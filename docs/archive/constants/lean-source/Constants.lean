module

public import MovingSofaStability.DeficitBudget
public import MovingSofaStability.DiskRecovery
public import MovingSofaStability.GlobalConstantAlgebra
public import MovingSofaStability.OrthogonalErosion
public import MovingSofaStability.RefinedConstantAlgebra
public import MovingSofaStability.BudgetedRecovery
public import MovingSofaStability.PhaseAwareConstants
public import MovingSofaStability.NumericalRecovery
public import MovingSofaStability.DirectRoofBand
public import MovingSofaStability.CoefficientLowerBound

/-!
# Explicit global coefficients: supporting source and analytic proof

The analytic notes in docs/stability/constants derive coefficients

* Hausdorff distance: 61 / 2;
* symmetric-difference area: 100;
* terminal-angle deficit: 31 / 10;

for all sufficiently near-optimal original sofas, with an existential positive
entry threshold. They do not claim optimal coefficients or a bound for all
possible area deficits.

This root collects the new exact bookkeeping, orthogonal erosion, scalar
reference inequalities, direct roof-band localization, conditional actual-set
recovery, and the puncture-based lower bound on any universal coefficient.
It does NOT contain an unconditional new numeric UnrestrictedStability theorem.
The reference phase/angle adaptation, explicit interior-ball geometry, exact
band/parallel-layer integration, improved terminal trapezoid, and final geometric
specialization still require formal implementation and verification.

No Lean, Lake, CI, remote build, or TeX compilation was run. All additions are
uncompiled proof source. Numerical diagnostics do not verify these proof terms.
See docs/stability/constants/09-audit-and-limitations.md.
-/
