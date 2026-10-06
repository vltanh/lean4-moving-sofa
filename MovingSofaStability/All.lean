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
public import MovingSofaStability.EuclideanDisks
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
public import MovingSofaStability.PunctureMetric
public import MovingSofaStability.PunctureTopology
public import MovingSofaStability.PuncturedSofa
public import MovingSofaStability.QuadraticDeficit
public import MovingSofaStability.QualitativeEntry
public import MovingSofaStability.ReferenceCoreVariation
public import MovingSofaStability.ResidualIntegrability
public import MovingSofaStability.ResidualMass
public import MovingSofaStability.ResidualPropagation
public import MovingSofaStability.Residuals
public import MovingSofaStability.RigidInterior
public import MovingSofaStability.RoofGeometry
public import MovingSofaStability.RoofMargins
public import MovingSofaStability.SeparatedWedges
public import MovingSofaStability.SharpCapDistance
public import MovingSofaStability.SharpEvaluation
public import MovingSofaStability.SharpExponent
public import MovingSofaStability.SharpIntegralControl
public import MovingSofaStability.SharpKernelNorms
public import MovingSofaStability.SharpReconstruction
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
public import MovingSofaStability.TrigKernelIntegrals
public import MovingSofaStability.UniformGeometryBounds
public import MovingSofaStability.WideConcavity
public import MovingSofaStability.WideDomain
public import MovingSofaStability.WideFirstVariation
public import MovingSofaStability.WideGerverCertificate
public import MovingSofaStability.WideResidualEnergy

/-!
# The stability of Gerver's sofa

This module imports every module of the library.

`GlobalStability.lean` proves the unrestricted stability theorem and the
terminal-angle estimate. There are constants C, C', C'', ε₀ > 0 such that a
moving sofa whose area is ε < ε₀ less than Gerver's is, after a translation,
within C√ε of Gerver's sofa in the Euclidean Hausdorff distance, the area of its
symmetric difference with Gerver's sofa is at most C'√ε, and every rotation angle
ω ∈ [arcsec 2.2, π/2] with which it moves satisfies π/2 - ω ≤ C''ε. The
constants are existential.

`SharpCapDistance.lean` proves the cap estimates with coefficient 2 / cos φ,
less than 2.002 in Romik's box. The declarations with coefficient 80 remain.

`SharpExponent.lean` proves, with the punctured Gerver sofas of
`PuncturedSofa.lean`, that no Hausdorff exponent greater than one half holds,
whatever the constant and the rigid alignment. It claims no sharpness for the
symmetric-difference area or for the cap constants.

See `docs/stability/README.md`.
-/
