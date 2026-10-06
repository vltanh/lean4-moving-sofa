module

public meta import Lean

-- Repository proof bodies must be visible through every intermediate result.
-- This file is source for a future explicit audit; it has NOT been executed.
import all MovingSofaOptimality.Angle.HorizontalSide
import all MovingSofaOptimality.Angle.RightAngle
import all MovingSofaOptimality.Balanced.BalancedMaximumSofa
import all MovingSofaOptimality.Balanced.CapGeometry
import all MovingSofaOptimality.Balanced.MaximumPolygonCap
import all MovingSofaOptimality.Balanced.MaxPolygonCapExists
import all MovingSofaOptimality.Balanced.NefPolygon
import all MovingSofaOptimality.Balanced.PolygonCap
import all MovingSofaOptimality.Balanced.Polyline
import all MovingSofaOptimality.Basic.ConvexBody
import all MovingSofaOptimality.Basic.Interval
import all MovingSofaOptimality.Basic.LebesgueStieltjes
import all MovingSofaOptimality.Basic.Plane
import all MovingSofaOptimality.Basic.SurfaceArea
import all MovingSofaOptimality.Convex.ConvexCurve
import all MovingSofaOptimality.Convex.ConvexDomain
import all MovingSofaOptimality.Convex.CurveArea
import all MovingSofaOptimality.Convex.Mamikon
import all MovingSofaOptimality.External.AreaFormula.Param
import all MovingSofaOptimality.External.AreaFormula
import all MovingSofaOptimality.External.Romik.Calc
import all MovingSofaOptimality.External.Romik.Fix
import all MovingSofaOptimality.External.Romik.Num
import all MovingSofaOptimality.External.Romik
import all MovingSofaOptimality.Gerver.AreaBounds
import all MovingSofaOptimality.Gerver.Bounds
import all MovingSofaOptimality.Gerver.Defs
import all MovingSofaOptimality.Gerver.Envelope
import all MovingSofaOptimality.Gerver.EnvelopeArea
import all MovingSofaOptimality.Gerver.Frame
import all MovingSofaOptimality.Gerver.Niche
import all MovingSofaOptimality.Gerver.NicheBounds
import all MovingSofaOptimality.Gerver.Properties
import all MovingSofaOptimality.Gerver.Structure
import all MovingSofaOptimality.Gerver.StructureCap
import all MovingSofaOptimality.Injectivity.ArmLengths
import all MovingSofaOptimality.Injectivity.BoundingArms
import all MovingSofaOptimality.Injectivity.DiscreteIneq
import all MovingSofaOptimality.Injectivity.LimitIneq
import all MovingSofaOptimality.Intro.RotationAngleBound
import all MovingSofaOptimality.Main
import all MovingSofaOptimality.Monotone.CapContainsNiche
import all MovingSofaOptimality.Monotone.CapDefs
import all MovingSofaOptimality.Monotone.CapNiche
import all MovingSofaOptimality.Monotone.MonotoneSofa
import all MovingSofaOptimality.Monotone.SupportingHallway
import all MovingSofaOptimality.Optimality.Concavity
import all MovingSofaOptimality.Optimality.Domain
import all MovingSofaOptimality.Optimality.UpperBound
import all MovingSofaOptimality.Optimality.Variation
import all MovingSofaOptimality.Sofa.Defs
import all MovingSofaUniqueness.AngleExtension
import all MovingSofaUniqueness.Curvature
import all MovingSofaUniqueness.RegularClosed
import all MovingSofaUniqueness.Rigid
import all MovingSofaUniqueness.Selection
import all MovingSofaUniqueness.Variation
-- Old routes are imported only for negative controls and statement coexistence.
import all MovingSofaUniqueness.Rigidity
import all MovingSofaUniqueness.Main
import all MovingSofaUniqueness.Maximizers
import all MovingSofaUniqueness.Optimality
import all MovingSofaUniqueness.Alternative
-- Only the lower quantitative layer, not the global-stability/local-entry layer.
import all MovingSofaStability.MamikonFoundation
import all MovingSofaStability.QuadraticDeficit
import all MovingSofaStability.MamikonEnergy
import all MovingSofaStability.BaekDeficit
import all MovingSofaStability.WideDomain
import all MovingSofaStability.CBVAlgebra
import all MovingSofaStability.ArcAtoms
import all MovingSofaStability.NonsmoothBookkeeping
import all MovingSofaStability.NonsmoothAffinity
import all MovingSofaStability.WideConcavity
import all MovingSofaStability.MixedArea
import all MovingSofaStability.ReferenceCoreVariation
import all MovingSofaStability.WideFirstVariation
import all MovingSofaStability.WideGerverCertificate
import all MovingSofaStability.WideResidualEnergy
import all MovingSofaStability.IntegralEstimates
import all MovingSofaStability.Residuals
import all MovingSofaStability.ODEReconstruction
import all MovingSofaStability.ResidualIntegrability
import all MovingSofaStability.ResidualMass
import all MovingSofaStability.ResidualPropagation
import all MovingSofaStability.FourArcCoercivity
import all MovingSofaStability.CapCoercivity
import all MovingSofaStability.EuclideanGeometry
import all MovingSofaStability.SupportDistance
import all MovingSofaStability.CapDistance
import all MovingSofaStability.GreenNorm
import all MovingSofaStability.SharpIntegralControl
import all MovingSofaStability.TrigKernelIntegrals
import all MovingSofaStability.SharpReconstruction
import all MovingSofaStability.SharpKernelNorms
import all MovingSofaStability.SharpEvaluation
import all MovingSofaStability.SharpCapDistance
import all MovingSofaExtremal.Geometry
import all MovingSofaExtremal.HorizontalTranslation
import all MovingSofaExtremal.CoerciveRigidity
import all MovingSofaExtremal.Optimality
import all MovingSofaExtremal.Uniqueness
import all MovingSofaBridge.GerverConstants
import all MovingSofaBridge.RomikParams
import all MovingSofaBridge.Motion
import all MovingSofaBridge.GerverSofa
import all ChallengeDefs
import all Solution
import all SolutionCoercive

/-!
# Audit contract for the independent coercive route

Checks standard axioms, transitive proof dependencies, required positive
quantitative dependencies, negative controls, and the types of all twelve
Challenge statements against the canonical solution. It never treats a renamed
wrapper as independent merely because its direct body has no forbidden name.

No execution or successful audit is claimed. Do not run this file until the
user permits Lean compilation and the new libraries have been checked.
-/

open Lean Elab Command

namespace CoerciveRouteAudit

meta def isRepositoryModule (m : Name) : Bool :=
  [`MovingSofaOptimality, `MovingSofaUniqueness, `MovingSofaStability,
    `MovingSofaExtremal, `MovingSofaBridge].any (·.isPrefixOf m) ||
    m == `ChallengeDefs || m == `Solution || m == `SolutionCoercive

meta def auditedModule (m : Name) : Bool :=
  (`MovingSofaExtremal).isPrefixOf m || (`MovingSofaStability).isPrefixOf m ||
    m == `SolutionCoercive

meta def forbiddenModules : List Name :=
  [`MovingSofaUniqueness.Main, `MovingSofaUniqueness.Rigidity,
   `MovingSofaUniqueness.Maximizers, `MovingSofaUniqueness.Optimality,
   `MovingSofaUniqueness.Alternative, `MovingSofaStability.Statement,
   `MovingSofaStability.QualitativeEntry, `MovingSofaStability.GlobalStability,
   `Solution]

meta def baekForbidden : List Name :=
  [``MovingSofaOptimality.theorem1_1_1, ``MovingSofaOptimality.gm_area_le,
   ``MovingSofaOptimality.theorem1_5_2, ``MovingSofaOptimality.theorem4_1_2,
   ``MovingSofaOptimality.theorem4_1_4, ``MovingSofaOptimality.theorem4_2_5,
   ``MovingSofaOptimality.theorem6_1_1, ``MovingSofaOptimality.theorem6_3_3,
   ``MovingSofaOptimality.theorem6_4_3, ``MovingSofaOptimality.corollary6_4_4,
   ``MovingSofaOptimality.theorem6_5_6, ``MovingSofaOptimality.theorem8_1_1_balanced]

meta def constantsIn (env : Environment) (select : Name → Bool) : NameSet := Id.run do
  let mut out : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if select m then
      for c in d.constNames do out := out.insert c
  return out

meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Traverse all repository intermediate bodies, including private and generated declarations. -/
meta def dependencies (env : Environment) (library : NameSet) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack := (usedConstants env root).toList
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if c == root || visited.contains c then continue
      visited := visited.insert c
      if library.contains c then
        for d in usedConstants env c do
          if !visited.contains d then stack := d :: stack
  return visited

meta def requiredEdges : List (Name × Name) :=
  [(``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaExtremal.isKi_of_maximizes),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaExtremal.right_angle_maximizer_certificate),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.sharp_wide_cap_distance_bound),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.wide_deficit_eq_slack_add_integrals),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.EuclideanClose.eq_of_zero),
   (``MovingSofaExtremal.gerver_sofa_optimal, ``MovingSofaStability.wideUpperQ_le_gerver),
   (``MovingSofaExtremal.image_eq_gerver_of_volume_eq,
      ``MovingSofaExtremal.right_angle_maximizer_eq_gerver),
   (``CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa,
      ``MovingSofaExtremal.image_eq_gerver_of_volume_eq),
   (``CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa,
      ``MovingSofaBridge.gerversSofa_eq)]

meta def negativeEdges : List (Name × Name) :=
  [(``MovingSofaOptimality.theorem1_1_1, ``MovingSofaOptimality.gm_area_le),
   (``MovingSofaOptimality.gm_area_le, ``MovingSofaOptimality.theorem1_5_2),
   (``MovingSofaOptimality.gm_area_le, ``MovingSofaOptimality.theorem8_1_1_balanced),
   (``MovingSofaUniqueness.area_le_gerver, ``MovingSofaOptimality.theorem1_1_1),
   (``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
      ``MovingSofaUniqueness.capKernel_of_triple_midpoint),
   (``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
      ``MovingSofaUniqueness.CapKernel.eq_horizontal_translation)]

/-- Distinct names, identical statement types: both solutions may coexist. -/
meta def statementPairs : List (Name × Name) :=
  [(``Baek.gerver_params_exists, ``CoerciveSolution.gerver_params_exists),
   (``Baek.gerver_params_unique, ``CoerciveSolution.gerver_params_unique),
   (``Baek.gerver_sofa_area, ``CoerciveSolution.gerver_sofa_area),
   (``Baek.gerver_sofa_optimal, ``CoerciveSolution.gerver_sofa_optimal),
   (``Baek.gerver_sofa_unique, ``CoerciveSolution.gerver_sofa_unique),
   (``Bridge.isMovingSofa_iff, ``CoerciveSolution.bridge_isMovingSofa_iff),
   (``Bridge.sofaConstant_eq, ``CoerciveSolution.bridge_sofaConstant_eq),
   (``Bridge.gerversSofa_eq, ``CoerciveSolution.bridge_gerversSofa_eq),
   (``FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique,
      ``CoerciveSolution.gerver_constants_existsUnique),
   (``FormalConjectures.MovingSofa.isMovingSofa_gerversSofa,
      ``CoerciveSolution.formal_isMovingSofa_gerversSofa),
   (``FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa,
      ``CoerciveSolution.formal_sofaConstant_eq_volume_gerversSofa),
   (``FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa,
      ``CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa)]

elab "#audit_coercive_route" : command => do
  let env ← getEnv
  let library := constantsIn env isRepositoryModule
  let audited := constantsIn env auditedModule
  let old := constantsIn env forbiddenModules.contains
  let forbidden := baekForbidden.foldl (fun s n => s.insert n) old
  let standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  if audited.size == 0 then throwError "no coercive declarations visible"
  for (root, target) in negativeEdges do
    unless (dependencies env library root).contains target do
      throwError m!"negative control failed: {root} does not expose {target}"
  for (root, target) in requiredEdges do
    unless audited.contains root do
      throwError m!"coercive entry point is not owned by an audited module: {root}"
    unless (dependencies env library root).contains target do
      throwError m!"required quantitative/bridge dependency absent: {root} -> {target}"
  for n in audited do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then
      throwError m!"non-standard axioms in coercive declaration {n}: {axs}"
    let ds := dependencies env library n
    for f in forbidden do
      if ds.contains f then
        throwError m!"coercive declaration {n} reaches forbidden dependency {f}"
  for (canonical, coercive) in statementPairs do
    let oldInfo ← liftCoreM <| getConstInfo canonical
    let newInfo ← liftCoreM <| getConstInfo coercive
    unless oldInfo.levelParams == newInfo.levelParams do
      throwError m!"different universe parameters for statement pair {canonical}, {coercive}"
    let same ← liftTermElabM do Meta.isDefEq oldInfo.type newInfo.type
    unless same do
      throwError m!"Challenge statement type changed: {canonical} versus {coercive}"
  logInfo m!"Checked {audited.size} coercive/core declarations; standard axioms only, no forbidden old route, required quantitative dependencies present, negative controls passed, all {statementPairs.length} Challenge statement types agree."

end CoerciveRouteAudit

#check MovingSofaOptimality.theorem1_1_1
#check MovingSofaUniqueness.image_eq_gerver_of_volume_eq
#check MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal_and_unique
#check MovingSofaExtremal.gerver_sofa_optimal_and_unique
#check FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa
#check CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa

#audit_coercive_route
