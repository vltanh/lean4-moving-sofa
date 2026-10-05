module

public import MovingSofaStability.QuadraticDeficit
public import MovingSofaStability.MamikonEnergy
public import MovingSofaStability.BaekDeficit
public import MovingSofaStability.EuclideanGeometry
public import MovingSofaStability.Statement
public import MovingSofaStability.IntegralEstimates
public import MovingSofaStability.WideDomain
public import MovingSofaStability.TerminalBookkeeping
public import MovingSofaStability.Residuals
public import MovingSofaStability.CBVAlgebra
public import MovingSofaStability.ArcAtoms
public import MovingSofaStability.NonsmoothBookkeeping
public import MovingSofaStability.NonsmoothAffinity
public import MovingSofaStability.WideConcavity
public import MovingSofaStability.MixedArea
public import MovingSofaStability.ReferenceCoreVariation
public import MovingSofaStability.WideFirstVariation
public import MovingSofaStability.WideGerverCertificate
public import MovingSofaStability.WideResidualEnergy
public import MovingSofaStability.ODEReconstruction
public import MovingSofaStability.GreenNorm

/-!
# Quantitative stability: current formalization frontier

This import root contains uncompiled proof source. No Lean or Lake invocation,
CI run, or kernel verification has been performed for these additions.

The strongest concrete objective result is
`MovingSofaStability.wide_deficit_eq_slack_add_integrals`, on the enlarged
nonsmooth triple domain, with
`MovingSofaStability.wide_capResidualEnergy_le_deficit` as a corollary.

`MovingSofaStability.UnrestrictedStability` in Statement.lean is an explicit
target proposition, NOT a proved theorem. The full analytic-to-geometric
assembly remains unfinished. See docs/stability/FORMALIZATION.md for a
per-dependency account; do not extend the manuscript's verification claims
on the basis of this import root.
-/
