module

public meta import Lean.Elab.Command

-- Proof bodies must be visible under Lean's module system, including in intermediate results.
-- This is a separate script: scripts/Audit.lean and Baek's route extraction remain unchanged.
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
-- The original entry point is imported for negative controls and coexistence checks only.
-- None of the three alternative modules imports it.
import all MovingSofaUniqueness.Main
import all MovingSofaUniqueness.RegularClosed
import all MovingSofaUniqueness.Rigid
import all MovingSofaUniqueness.Rigidity
import all MovingSofaUniqueness.Selection
import all MovingSofaUniqueness.Variation
import all MovingSofaUniqueness.Maximizers
import all MovingSofaUniqueness.Optimality
import all MovingSofaUniqueness.Alternative

/-!
# Separate audit of the parallel maximizer-first route

Prepared for a later authorized verification pass; not compiled or run in this work.
After building the required library modules, run:

    lake env lean scripts/AuditMaximizerRoute.lean

This script does not import or execute `scripts.Audit`, write the paper's route table, alter
workflows, or change the Challenge/Solution proof route. It checks every declaration owned by
the three new modules, not only the headline theorems.

Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
Dependency audit: traverse types and proof bodies through all repository helpers and numbered
results. Reject Baek's final global bound (`theorem1_1_1`, `gm_area_le`) and *every declaration*
owned by the original `MovingSofaUniqueness.Main`. This excludes indirect reuse of its
bound-dependent wrappers and final uniqueness theorem, not just literal calls to those names.

The original proofs are deliberately present in this audit environment. Negative controls
must detect their known dependencies, demonstrating that the traversal can see proof bodies.
Their dependence on the old bound is expected and is not a failure of the original route.
Importing both routes for this test does not make one a proof dependency of the other.
-/

open Lean Elab Command

namespace MaximizerRouteAudit

meta def alternativeModules : List Name :=
  [`MovingSofaUniqueness.Maximizers, `MovingSofaUniqueness.Optimality,
   `MovingSofaUniqueness.Alternative]

meta def entryPoints : List Name :=
  [``MovingSofaUniqueness.MaximizerRoute.exists_maximizing_cap,
   ``MovingSofaUniqueness.MaximizerRoute.isKi_of_maximizes,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_value,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.maximizing_monotone_has_right_angle,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizes_iff_translate_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_sofaArea_eq_gerver_iff,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_optimality_and_rigidity,
   ``MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal,
   ``MovingSofaUniqueness.MaximizerRoute.cap_area_le_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq,
   ``MovingSofaUniqueness.MaximizerRoute.volume_eq_gerver_iff,
   ``MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal_and_unique,
   ``MovingSofaUniqueness.MaximizerRoute.isMaximal_iff_image_eq_gerver]

/-- Ownership rather than namespace matching includes private/generated declarations. -/
meta def constantsIn (env : Environment) (select : Name → Bool) : NameSet := Id.run do
  let mut out : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if select m then
      for c in d.constNames do
        out := out.insert c
  return out

meta def isRepositoryModule (m : Name) : Bool :=
  (`MovingSofaOptimality).isPrefixOf m || (`MovingSofaUniqueness).isPrefixOf m ||
    (`MovingSofaBridge).isPrefixOf m || m == `ChallengeDefs || m == `Solution

meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Unlike Baek's numbered-result route audit, this never stops at an allowed intermediate
result. The root itself is excluded, allowing a forbidden theorem to be a negative control. -/
meta def forbiddenUses (env : Environment) (library forbidden : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if c == root || visited.contains c then continue
      visited := visited.insert c
      if forbidden.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

elab "#audit_maximizer_route" : command => do
  let env ← getEnv
  let library := constantsIn env isRepositoryModule
  let originals := constantsIn env (fun m => m == `MovingSofaUniqueness.Main)
  let alternatives := constantsIn env alternativeModules.contains
  let forbidden := (originals.insert ``MovingSofaOptimality.theorem1_1_1).insert
    ``MovingSofaOptimality.gm_area_le
  let standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for m in alternativeModules do
    let owned := constantsIn env (fun n => n == m)
    if owned.size == 0 then
      throwError m!"no declarations visible for alternative module {m}"
  for n in entryPoints do
    unless alternatives.contains n do
      throwError m!"alternative entry point not visible in its module: {n}"
  unless originals.contains ``MovingSofaUniqueness.area_le_gerver do
    throwError "original uniqueness entry point not visible for the negative control"
  let oldBound := forbiddenUses env library forbidden ``MovingSofaOptimality.theorem1_1_1
  unless oldBound.contains ``MovingSofaOptimality.gm_area_le do
    throwError "negative control failed: Baek's original optimality proof body is not visible"
  let oldWrapper := forbiddenUses env library forbidden ``MovingSofaUniqueness.area_le_gerver
  unless oldWrapper.contains ``MovingSofaOptimality.theorem1_1_1 do
    throwError "negative control failed: original uniqueness bound no longer exposes Baek's theorem"
  let oldUniqueness := forbiddenUses env library forbidden
    ``MovingSofaUniqueness.image_eq_gerver_of_volume_eq
  unless oldUniqueness.contains ``MovingSofaUniqueness.maximizer_contained_in_gerver do
    throwError "negative control failed: original uniqueness proof body is not visible"
  for n in alternatives do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then
      throwError m!"non-standard axioms in alternative declaration {n}: {axs}"
    let uses := forbiddenUses env library forbidden n
    unless uses.isEmpty do
      throwError m!"alternative declaration {n} reaches forbidden original dependencies: {uses}"
  logInfo m!"Checked {alternatives.size} alternative declarations: standard axioms only; no dependency on Baek's final bound or the original uniqueness entry point. Negative controls passed."

end MaximizerRouteAudit

-- Both theorem families must coexist without renaming or replacing the original declarations.
#check MovingSofaOptimality.theorem1_1_1
#check MovingSofaUniqueness.image_eq_gerver_of_volume_eq
#check MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal
#check MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal_and_unique

#audit_maximizer_route
