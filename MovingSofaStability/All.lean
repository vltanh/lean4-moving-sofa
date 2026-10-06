module

public import MovingSofaStability.AngularFaceStability
public import MovingSofaStability.ArcAtoms
public import MovingSofaStability.BaekDeficit
public import MovingSofaStability.CBVAlgebra
public import MovingSofaStability.CanonicalContacts
public import MovingSofaStability.CanonicalTriple
public import MovingSofaStability.CapCoercivity
public import MovingSofaStability.CapDistance
public import MovingSofaStability.CapShape
public import MovingSofaStability.CapWidthGeometry
public import MovingSofaStability.CompactSetLimits
public import MovingSofaStability.ConvexParallelArea
public import MovingSofaStability.CoreAreaBound
public import MovingSofaStability.CoreGraph
public import MovingSofaStability.CoreIntegral
public import MovingSofaStability.CoreMonotonicity
public import MovingSofaStability.CoreRegionGeometry
public import MovingSofaStability.CornerAnalysis
public import MovingSofaStability.CurveRoof
public import MovingSofaStability.CutSeparation
public import MovingSofaStability.EnvelopeSlack
public import MovingSofaStability.EnvelopeSlope
public import MovingSofaStability.EpigraphBalls
public import MovingSofaStability.EuclideanGeometry
public import MovingSofaStability.ExposedFaceStability
public import MovingSofaStability.FloorCoverage
public import MovingSofaStability.FourArcCoercivity
public import MovingSofaStability.GerverMargins
public import MovingSofaStability.GerverRoof
public import MovingSofaStability.GlobalStability
public import MovingSofaStability.GreenNorm
public import MovingSofaStability.IntegralEstimates
public import MovingSofaStability.InteriorBalls
public import MovingSofaStability.LocalArmMargins
public import MovingSofaStability.LocalSofaRecovery
public import MovingSofaStability.LocalUpperBound
public import MovingSofaStability.MamikonEnergy
public import MovingSofaStability.MissingAreaRecovery
public import MovingSofaStability.MixedArea
public import MovingSofaStability.NicheContainment
public import MovingSofaStability.NicheFeet
public import MovingSofaStability.NonsmoothAffinity
public import MovingSofaStability.NonsmoothBookkeeping
public import MovingSofaStability.ODEReconstruction
public import MovingSofaStability.OmittedWedgeArea
public import MovingSofaStability.PartialHallways
public import MovingSofaStability.QuadraticDeficit
public import MovingSofaStability.QualitativeEntry
public import MovingSofaStability.ReferenceCoreVariation
public import MovingSofaStability.ResidualIntegrability
public import MovingSofaStability.ResidualMass
public import MovingSofaStability.ResidualPropagation
public import MovingSofaStability.Residuals
public import MovingSofaStability.RoofGeometry
public import MovingSofaStability.RoofMargins
public import MovingSofaStability.SeparatedWedges
public import MovingSofaStability.SofaBounds
public import MovingSofaStability.SofaCap
public import MovingSofaStability.SofaCoordinates
public import MovingSofaStability.SofaLimitMotion
public import MovingSofaStability.Statement
public import MovingSofaStability.SupportDistance
public import MovingSofaStability.SymmetricDifference
public import MovingSofaStability.TerminalBookkeeping
public import MovingSofaStability.TerminalComparison
public import MovingSofaStability.TerminalFloor
public import MovingSofaStability.UniformGeometryBounds
public import MovingSofaStability.WideConcavity
public import MovingSofaStability.WideDomain
public import MovingSofaStability.WideFirstVariation
public import MovingSofaStability.WideGerverCertificate
public import MovingSofaStability.WideResidualEnergy

/-!
# Stability: complete current source assembly

The headline proof-source declarations are now in GlobalStability.lean:

* `MovingSofaStability.unrestricted_stability`
* `MovingSofaStability.terminal_angle_stability`
* `MovingSofaStability.reduced_sofa_stability`

The first two inhabit the target propositions defined in Statement.lean;
they are no longer only target definitions. Their assumptions are Gerver's
parameter solution and source-box hypotheses, not an unproved stability or
special-envelope interface.

IMPORTANT: none of this development has been compiled or kernel-checked.
This root records source coverage, not verification. Elaboration and tactic
errors may remain. No Lean, Lake, CI, remote build, or TeX compilation was run.
The global constants are existential; the source cap estimate uses the
non-sharp coefficient 80, not the analytic sharp coefficient 2 sec(phi).

The separate exponent-sharpness argument remains in the analytic notes; it
is not asserted here as a Lean theorem. See docs/stability/FORMALIZATION.md
for the proof route, validation limits, and source-review corrections.
-/
