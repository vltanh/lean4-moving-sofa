module

public meta import Lean.Elab.Command

-- Proof bodies must be visible under Lean's module system, including in intermediate results.
-- This is a separate script: scripts/Audit.lean and Baek's route extraction remain unchanged.
import all MovingSofaOptimality.Angle.HorizontalSide
import all MovingSofaOptimality.Angle.RightAngle
import all MovingSofaOptimality.Balanced.BalancedMaximumSofa
import all MovingSofaOptimality.Balanced.CapGeometry
import all MovingSofaOptimality.Balanced.MaxPolygonCapExists
import all MovingSofaOptimality.Balanced.MaximumPolygonCap
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
import all MovingSofaOptimality.External.AreaFormula
import all MovingSofaOptimality.External.AreaFormula.Param
import all MovingSofaOptimality.External.Romik
import all MovingSofaOptimality.External.Romik.Calc
import all MovingSofaOptimality.External.Romik.Fix
import all MovingSofaOptimality.External.Romik.Num
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
import all MovingSofaUniqueness.Mamikon
import all MovingSofaUniqueness.Maximizing
import all MovingSofaUniqueness.RegularClosed
import all MovingSofaUniqueness.Rigid
import all MovingSofaUniqueness.Rigidity
import all MovingSofaUniqueness.Selection
import all MovingSofaUniqueness.Variation
import all MovingSofaUniqueness.MaximizerRoute
-- The first proof is imported for negative controls only; the second proof does not import it.
import all MovingSofaUniqueness.Main

/-!
# Audit of the second proof of optimality

Run with `lake env lean scripts/AuditMaximizerRoute.lean` after `lake build`; CI runs it after
`scripts/Audit.lean`.

The modules `MovingSofaUniqueness.Maximizing` (the maximizing caps and the assembly shared with the
coercive route) and `MovingSofaUniqueness.MaximizerRoute` prove Baek's optimality theorem a second
time, from the maximizing caps (`rem:second` of the manuscript `docs/paper`), and assemble the
uniqueness theorem from that proof. This script checks every declaration of the two modules,
private and auxiliary ones included, and fails if one of them

- depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, or
- reaches, through the proofs of the library's declarations, Baek's final theorem
  (`theorem1_1_1`, `gm_area_le`), the results by which Baek derives the right-angle motion and the
  injectivity condition of Baek's cap from its balance (Theorems 1.5.2, 4.1.2, 4.1.4, 4.2.5, 6.1.1,
  6.3.3, 6.4.3, 6.5.6, Corollary 6.4.4 and Theorem 8.1.1 (2)), or any declaration of
  `MovingSofaUniqueness.Main`, the module of the first proof, which uses Baek's theorem.

Unlike the route traversal of `scripts/Audit.lean`, the traversal does not stop at numbered results.
Both proofs are imported, with `import all` so that the proofs are visible; negative controls check
that the traversal finds the known uses of the forbidden results in the first proof.
-/
open Lean Elab Command

namespace MaximizerRouteAudit

meta def alternativeModules : List Name :=
  [`MovingSofaUniqueness.Maximizing, `MovingSofaUniqueness.MaximizerRoute]

meta def entryPoints : List Name :=
  [``MovingSofaUniqueness.exists_maximizing_cap,
   ``MovingSofaUniqueness.isKi_of_maximizes,
   ``MovingSofaUniqueness.maximizing_monotone_has_right_angle,
   ``MovingSofaUniqueness.Maximizing.gerver_sofa_optimal,
   ``MovingSofaUniqueness.Maximizing.image_eq_gerver_of_volume_eq,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_value,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizes_iff_translate_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.right_angle_sofaArea_eq_gerver_iff,
   ``MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal,
   ``MovingSofaUniqueness.MaximizerRoute.cap_area_le_gerver,
   ``MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq,
   ``MovingSofaUniqueness.MaximizerRoute.volume_eq_gerver_iff,
   ``MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal_and_unique,
   ``MovingSofaUniqueness.MaximizerRoute.isMaximal_iff_image_eq_gerver]

/-- Baek's final theorem, and the results by which Baek derives the right-angle motion (step (3a))
and the injectivity condition (step (3b)) of Baek's cap from its balance. -/
meta def baekForbidden : List Name :=
  [``MovingSofaOptimality.theorem1_1_1, ``MovingSofaOptimality.gm_area_le,
   ``MovingSofaOptimality.theorem1_5_2, ``MovingSofaOptimality.theorem4_1_2,
   ``MovingSofaOptimality.theorem4_1_4, ``MovingSofaOptimality.theorem4_2_5,
   ``MovingSofaOptimality.theorem6_1_1, ``MovingSofaOptimality.theorem6_3_3,
   ``MovingSofaOptimality.theorem6_4_3, ``MovingSofaOptimality.corollary6_4_4,
   ``MovingSofaOptimality.theorem6_5_6, ``MovingSofaOptimality.theorem8_1_1_balanced]

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
    (`MovingSofaBridge).isPrefixOf m || m == `baek.Solution

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
  let forbidden := baekForbidden.foldl (fun s n => s.insert n) originals
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
  let oldSteps := forbiddenUses env library forbidden ``MovingSofaOptimality.gm_area_le
  unless oldSteps.contains ``MovingSofaOptimality.theorem1_5_2 &&
      oldSteps.contains ``MovingSofaOptimality.theorem8_1_1_balanced do
    throwError "negative control failed: Baek's steps (3a) and (3b) are not visible in Baek's proof"
  let oldAngle := forbiddenUses env library forbidden ``MovingSofaOptimality.theorem1_5_2
  unless oldAngle.contains ``MovingSofaOptimality.theorem4_2_5 do
    throwError "negative control failed: the proof of Baek's Theorem 1.5.2 is not visible"
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
  logInfo m!"Checked {alternatives.size} declarations of the second proof: standard axioms only; no dependency on Baek's final theorem, on Baek's steps (3a) and (3b) from the balance, or on MovingSofaUniqueness.Main. Negative controls passed."

end MaximizerRouteAudit

-- Both theorem families must coexist without renaming or replacing the original declarations.
#check MovingSofaOptimality.theorem1_1_1
#check MovingSofaUniqueness.image_eq_gerver_of_volume_eq
#check MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal
#check MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal_and_unique

#audit_maximizer_route
