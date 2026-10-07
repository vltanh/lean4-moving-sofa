module

public meta import Lean

-- Every repository module is imported with `import all`, so that the proof bodies of all
-- intermediate results, private and generated declarations included, are visible.
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
import all MovingSofaUniqueness.Selection
import all MovingSofaUniqueness.Variation
-- The first proof of uniqueness and the second proof of optimality: negative controls only.
import all MovingSofaUniqueness.Main
import all MovingSofaUniqueness.MaximizerRoute
import all MovingSofaUniqueness.Rigidity
import all MovingSofaStability.All
import all MovingSofaStability.Basic
import all MovingSofaStability.CapEstimate
import all MovingSofaStability.Deficit
import all MovingSofaStability.Global
import all MovingSofaStability.LocalBound
import all MovingSofaStability.LocalGeometry
import all MovingSofaStability.Margins
import all MovingSofaStability.Recovery
import all MovingSofaStability.Sharpness
import all MovingSofaStability.Terminal
import all MovingSofaStability.WideDomain
import all MovingSofaExtremal.All
import all MovingSofaExtremal.Main
import all MovingSofaExtremal.Unified
import all MovingSofaBridge.GerverConstants
import all MovingSofaBridge.GerverSofa
import all MovingSofaBridge.Motion
import all MovingSofaBridge.RomikParams
import all ChallengeDefs
import all baek.Solution
import all SolutionCoercive
import all CertificateDefs
import all CertificateProof

/-!
# Audit of the coercive route

`MovingSofaExtremal` proves optimality and uniqueness from the coercive certificate
`MovingSofaStability.coercive_certificate`, and `MovingSofaStability` proves stability from the same
certificate and from that uniqueness theorem. The certificate entry (`Challenge.lean`,
`comparator.json`) is proved from them: `SolutionCoercive` proves fifteen of its theorems, with
optimality, uniqueness and stability from these, and `CertificateProof` proves its two statements
about the certificate, with the definitions of `CertificateDefs`. This script
checks, for every declaration of `MovingSofaExtremal`, `MovingSofaStability`, `SolutionCoercive`,
`CertificateDefs` and `CertificateProof`, private and generated ones included:

1. its axioms are among `propext`, `Classical.choice` and `Quot.sound`;
2. its proof does not reach, through the proof bodies of any repository declarations, Baek's
   Theorem 1.1.1 (`theorem1_1_1`, `gm_area_le`), his results on balanced caps (Theorems 1.5.2,
   4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6, Corollary 6.4.4 and Theorem 8.1.1 (2)), any
   declaration of the first proof of uniqueness (`MovingSofaUniqueness.Rigidity`, `.Main`) or of
   the second proof of optimality (`MovingSofaUniqueness.MaximizerRoute`), or `baek.Solution`.

It also checks that the optimality and uniqueness theorems of the route do not reach the stability
proof after the certificate (`MovingSofaStability.Margins` and the modules that import it; no
circularity: the stability theorem uses uniqueness), that the route does use
the certificate where it should (positive controls), that the old routes do reach what they are known
to reach (negative controls, which show that the traversal sees proof bodies), and that the twelve
theorems that `SolutionCoercive` shares with `baek/Solution.lean` (Baek's entry) have exactly the
types of the matching theorems of `baek/Solution.lean`. Comparator checks all seventeen theorems of
the certificate entry against `Challenge.lean`, through the root's `Solution.lean`, which declares
the names of `baek.Solution` and so cannot be imported here.
-/

open Lean Elab Command

namespace CoerciveRouteAudit

meta def isRepositoryModule (m : Name) : Bool :=
  [`MovingSofaOptimality, `MovingSofaUniqueness, `MovingSofaStability,
    `MovingSofaExtremal, `MovingSofaBridge].any (·.isPrefixOf m) ||
    m == `ChallengeDefs || m == `baek.Solution || m == `SolutionCoercive ||
    m == `CertificateDefs || m == `CertificateProof

/-- The modules of the coercive route, all of whose declarations are audited. -/
meta def auditedModule (m : Name) : Bool :=
  (`MovingSofaExtremal).isPrefixOf m || (`MovingSofaStability).isPrefixOf m ||
    m == `SolutionCoercive || m == `CertificateDefs || m == `CertificateProof

/-- The modules whose declarations the route must not reach. -/
meta def forbiddenModules : List Name :=
  [`MovingSofaUniqueness.Main, `MovingSofaUniqueness.Rigidity,
   `MovingSofaUniqueness.MaximizerRoute, `baek.Solution]

/-- Baek's Theorem 1.1.1 and the results of his balance argument. -/
meta def baekForbidden : List Name :=
  [``MovingSofaOptimality.theorem1_1_1, ``MovingSofaOptimality.gm_area_le,
   ``MovingSofaOptimality.theorem1_5_2, ``MovingSofaOptimality.theorem4_1_2,
   ``MovingSofaOptimality.theorem4_1_4, ``MovingSofaOptimality.theorem4_2_5,
   ``MovingSofaOptimality.theorem6_1_1, ``MovingSofaOptimality.theorem6_3_3,
   ``MovingSofaOptimality.theorem6_4_3, ``MovingSofaOptimality.corollary6_4_4,
   ``MovingSofaOptimality.theorem6_5_6, ``MovingSofaOptimality.theorem8_1_1_balanced]

/-- The modules of the route that prove optimality and uniqueness. -/
meta def coreModules : List Name :=
  [`MovingSofaUniqueness.Maximizing, `MovingSofaExtremal.Main]

meta def constantsIn (env : Environment) (select : Name → Bool) : NameSet := Id.run do
  let mut out : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if select m then
      for c in d.constNames do out := out.insert c
  return out

/-- Equation lemmas and similar auxiliary theorems, which Lean creates on demand in the first module
that needs them; several modules may then contain the same one. -/
meta def isRealizedAux (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "mutual_induct" ||
      s == "fun_cases" ||
      (s.startsWith "eq_" && s.length > 3 && (s.toList.drop 3).all Char.isDigit)
  | _ => false

/-- The declarations of the selected modules. An auxiliary theorem of a declaration of another
module belongs to that module, wherever Lean created it. -/
meta def ownedConstants (env : Environment) (select : Name → Bool) : NameSet := Id.run do
  let mut out : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if select m then
      for c in d.constNames do
        if isRealizedAux c then
          if let some idx := env.getModuleIdxFor? c.getPrefix then
            unless select env.header.moduleNames[idx.toNat]! do continue
        out := out.insert c
  return out

meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The constants that `root` reaches through the types and bodies of repository declarations. -/
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

/-- Every repository declaration that reaches a target, with the next declaration on a path to
it: one backward search from the targets over the repository's dependency edges. -/
meta def reaching (env : Environment) (library targets : NameSet) : NameMap Name := Id.run do
  let mut rev : NameMap (Array Name) := {}
  for c in library do
    for d in usedConstants env c do
      if library.contains d || targets.contains d then
        rev := rev.insert d ((rev.getD d #[]).push c)
  let mut next : NameMap Name := {}
  let mut queue : Array Name := #[]
  for t in targets do
    next := next.insert t t
    queue := queue.push t
  let mut i := 0
  while i < queue.size do
    let x := queue[i]!
    i := i + 1
    for c in rev.getD x #[] do
      unless next.contains c do
        next := next.insert c x
        queue := queue.push c
  return next

/-- A path from `n` to a target, along `reaching`. -/
meta def witness (next : NameMap Name) (n : Name) : List Name := Id.run do
  let mut path := [n]
  let mut x := n
  for _ in [0:200] do
    match next.find? x with
    | some y =>
      if y == x then break
      path := path ++ [y]
      x := y
    | none => break
  return path

/-- The modules that import `m`, directly or not, and `m` itself. -/
meta def importersOf (env : Environment) (m : Name) : NameSet := Id.run do
  let mut out : NameSet := ({} : NameSet).insert m
  let mut changed := true
  while changed do
    changed := false
    for n in env.header.moduleNames, d in env.header.moduleData do
      if !out.contains n && d.imports.any (fun i => out.contains i.module) then
        out := out.insert n
        changed := true
  return out

meta def requiredEdges : List (Name × Name) :=
  [-- the cap classification uses the certificate at zero deficit
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaUniqueness.isKi_of_maximizes),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaExtremal.right_angle_maximizer_certificate),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.coercive_certificate),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.sharp_wide_cap_distance_bound),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.wide_deficit_eq_slack_add_integrals),
   (``MovingSofaExtremal.right_angle_maximizer_eq_gerver,
      ``MovingSofaStability.EuclideanClose.eq_of_zero),
   -- optimality uses the certificate's bound on 𝒬
   (``MovingSofaExtremal.gerver_sofa_optimal, ``MovingSofaStability.coercive_certificate),
   (``MovingSofaExtremal.gerver_sofa_optimal, ``MovingSofaStability.wideUpperQ_le_gerver),
   -- uniqueness uses the cap classification
   (``MovingSofaExtremal.image_eq_gerver_of_volume_eq,
      ``MovingSofaExtremal.right_angle_maximizer_eq_gerver),
   (``MovingSofaExtremal.translate_eq_gerver_of_volume_eq,
      ``MovingSofaExtremal.right_angle_maximizer_eq_gerver),
   -- stability uses the certificate and the uniqueness of the route
   (``MovingSofaStability.unrestricted_stability, ``MovingSofaStability.coercive_certificate),
   (``MovingSofaStability.unrestricted_stability,
      ``MovingSofaExtremal.translate_eq_gerver_of_volume_eq),
   (``MovingSofaStability.unrestricted_stability, ``MovingSofaExtremal.area_le_gerver),
   (``MovingSofaStability.terminal_angle_stability, ``MovingSofaStability.coercive_certificate),
   (``MovingSofaStability.terminal_angle_stability,
      ``MovingSofaExtremal.translate_eq_gerver_of_volume_eq),
   -- the unified theorem and the proofs of the certificate entry
   (``MovingSofaExtremal.gerver_sofa_optimal_unique_stable,
      ``MovingSofaStability.coercive_certificate),
   (``CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa,
      ``MovingSofaExtremal.image_eq_gerver_of_volume_eq),
   (``CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa,
      ``MovingSofaBridge.gerversSofa_eq),
   (``CoerciveSolution.gerver_sofa_stable,
      ``MovingSofaExtremal.gerver_sofa_optimal_unique_stable),
   (``CoerciveSolution.gerver_sofa_angle_stable,
      ``MovingSofaExtremal.gerver_sofa_optimal_unique_stable),
   -- the certificate and Gerver's triple
   (``Certificate.coercive_certificate, ``MovingSofaStability.coercive_certificate),
   (``Certificate.gerver_triple, ``MovingSofaStability.wideGerver_value)]

meta def negativeEdges : List (Name × Name) :=
  [(``MovingSofaOptimality.theorem1_1_1, ``MovingSofaOptimality.gm_area_le),
   (``MovingSofaOptimality.gm_area_le, ``MovingSofaOptimality.theorem1_5_2),
   (``MovingSofaOptimality.gm_area_le, ``MovingSofaOptimality.theorem8_1_1_balanced),
   (``MovingSofaUniqueness.area_le_gerver, ``MovingSofaOptimality.theorem1_1_1),
   (``MovingSofaUniqueness.translate_eq_gerver_of_volume_eq,
      ``MovingSofaOptimality.theorem1_1_1),
   (``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
      ``MovingSofaUniqueness.capKernel_of_triple_midpoint),
   (``MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver,
      ``MovingSofaUniqueness.CapKernel.eq_horizontal_translation)]

/-- The twelve theorems that both `baek/Solution.lean` (Baek's entry) and `SolutionCoercive.lean`
(the certificate entry) state, with the same statements. -/
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
  if audited.size == 0 then throwError "no declarations of the coercive route are visible"
  -- negative controls: the traversal sees the proof bodies of the old routes
  for (root, target) in negativeEdges do
    unless (dependencies env library root).contains target do
      throwError m!"negative control failed: {root} does not reach {target}"
  -- positive controls
  for (root, target) in requiredEdges do
    unless audited.contains root do
      throwError m!"{root} is not a declaration of the coercive route"
    unless (dependencies env library root).contains target do
      throwError m!"positive control failed: {root} does not reach {target}"
  -- axioms
  let standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in audited do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then
      throwError m!"non-standard axioms in {n}: {axs}"
  -- the forbidden routes
  let forbidden := baekForbidden.foldl (fun s n => s.insert n)
    (ownedConstants env forbiddenModules.contains)
  let toForbidden := reaching env library forbidden
  -- negative control of the backward search: the first proof of uniqueness reaches Theorem 1.5.2
  -- through Theorem 1.1.1, several declarations away
  let toBalance := reaching env library (({} : NameSet).insert ``MovingSofaOptimality.theorem1_5_2)
  let path := witness toBalance ``MovingSofaUniqueness.translate_eq_gerver_of_volume_eq
  unless path.getLast? == some ``MovingSofaOptimality.theorem1_5_2 && path.length > 3 do
    throwError m!"negative control failed: the backward search found {path}"
  for n in audited do
    if toForbidden.contains n then
      throwError m!"{n} reaches a forbidden declaration: {witness toForbidden n}"
  -- no circularity: optimality and uniqueness do not use the stability theorem
  let upper := importersOf env `MovingSofaStability.Margins
  let core := constantsIn env coreModules.contains
  let toUpper := reaching env library (ownedConstants env upper.contains)
  for n in core do
    if toUpper.contains n then
      throwError m!"{n} reaches the global stability layer: {witness toUpper n}"
  -- the statements that both entries prove
  for (canonical, coercive) in statementPairs do
    let oldInfo ← liftCoreM <| getConstInfo canonical
    let newInfo ← liftCoreM <| getConstInfo coercive
    unless oldInfo.levelParams == newInfo.levelParams do
      throwError m!"different universe parameters: {canonical}, {coercive}"
    -- the same expression up to the names of bound variables, not only definitionally equal
    unless oldInfo.type == newInfo.type do
      throwError m!"different statements: {canonical}, {coercive}"
  logInfo m!"Coercive route: {audited.size} declarations, standard axioms only, none reaches \
    Baek's Theorem 1.1.1, his balance results or the first proof of uniqueness; the \
    {core.size} declarations of optimality and uniqueness do not reach the global stability \
    layer ({upper.size} modules); {requiredEdges.length} positive and {negativeEdges.length + 1} \
    negative controls passed; the {statementPairs.length} statements that SolutionCoercive shares \
    with baek/Solution.lean agree."

end CoerciveRouteAudit

#audit_coercive_route
