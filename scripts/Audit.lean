module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find PaperName -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all MovingSofa.Angle.HorizontalSide
import all MovingSofa.Angle.RightAngle
import all MovingSofa.Balanced.BalancedMaximumSofa
import all MovingSofa.Balanced.MaximumPolygonCap
import all MovingSofa.Balanced.NefPolygon
import all MovingSofa.Balanced.PolygonCap
import all MovingSofa.Basic.ConvexBody
import all MovingSofa.Basic.LebesgueStieltjes
import all MovingSofa.Basic.Plane
import all MovingSofa.Basic.SurfaceArea
import all MovingSofa.Convex.ConvexCurve
import all MovingSofa.Convex.ConvexDomain
import all MovingSofa.Convex.CurveArea
import all MovingSofa.Convex.Mamikon
import all MovingSofa.External.AreaFormula
import all MovingSofa.External.AreaFormula.Param
import all MovingSofa.External.Romik
import all MovingSofa.External.Romik.Calc
import all MovingSofa.External.Romik.Fix
import all MovingSofa.External.Romik.Num
import all MovingSofa.Gerver.AreaBounds
import all MovingSofa.Gerver.Bounds
import all MovingSofa.Gerver.Defs
import all MovingSofa.Gerver.Envelope
import all MovingSofa.Gerver.EnvelopeArea
import all MovingSofa.Gerver.Frame
import all MovingSofa.Gerver.Niche
import all MovingSofa.Gerver.NicheBounds
import all MovingSofa.Gerver.Properties
import all MovingSofa.Gerver.Structure
import all MovingSofa.Gerver.StructureCap
import all MovingSofa.Injectivity.ArmLengths
import all MovingSofa.Injectivity.BoundingArms
import all MovingSofa.Injectivity.DiscreteIneq
import all MovingSofa.Injectivity.LimitIneq
import all MovingSofa.Intro.RotationAngleBound
import all MovingSofa.Main
import all MovingSofa.Monotone.CapContainsNiche
import all MovingSofa.Monotone.CapDefs
import all MovingSofa.Monotone.CapNiche
import all MovingSofa.Monotone.MonotoneSofa
import all MovingSofa.Monotone.SupportingHallway
import all MovingSofa.Optimality.Concavity
import all MovingSofa.Optimality.Domain
import all MovingSofa.Optimality.UpperBound
import all MovingSofa.Optimality.Variation
import all MovingSofa.Sofa.Defs
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`MovingSofa/External/`) that its proof uses. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, proved in `MovingSofa/External/`, with a short label. Their
proofs are not searched: the traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Schneider, Remark 5.1.2: |K| = ½∫ h_K dσ_K", ``MovingSofa.area_eq_half_integral_supp),
   ("Romik 2018: Romik's system has a solution in the box", ``MovingSofa.GerverParams.romik_exists),
   ("Romik 2018: the solution in the box is unique", ``MovingSofa.GerverParams.romik_unique)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Thm 1.1.1", ``MovingSofa.theorem1_1_1),
   ("Prop 1.2.2", ``MovingSofa.proposition1_2_2),
   ("Thm 1.5.1", ``MovingSofa.theorem1_5_1),
   ("Thm 1.5.2", ``MovingSofa.theorem1_5_2),
   ("Thm 1.7.1", ``MovingSofa.theorem1_7_1),
   ("Prop 2.1.2", ``MovingSofa.proposition2_1_2),
   ("Thm 2.1.3 (vint left)", ``MovingSofa.tendsto_vint_left),
   ("Thm 2.1.3 (vint right)", ``MovingSofa.tendsto_vint_right),
   ("Thm 2.1.3 (vminus left)", ``MovingSofa.tendsto_vminus_left),
   ("Thm 2.1.3 (vminus right)", ``MovingSofa.tendsto_vminus_right),
   ("Thm 2.1.3 (vplus left)", ``MovingSofa.tendsto_vplus_left),
   ("Thm 2.1.3 (vplus right)", ``MovingSofa.tendsto_vplus_right),
   ("Prop 2.2.1", ``MovingSofa.proposition2_2_1),
   ("Prop 2.2.2 (hallway)", ``MovingSofa.proposition2_2_2_hallway),
   ("Prop 2.2.2 (innerCorner)", ``MovingSofa.proposition2_2_2_innerCorner),
   ("Prop 2.2.2 (outerCorner)", ``MovingSofa.proposition2_2_2_outerCorner),
   ("Prop 2.2.2 (qMinus)", ``MovingSofa.proposition2_2_2_qMinus),
   ("Prop 2.2.2 (qPlus)", ``MovingSofa.proposition2_2_2_qPlus),
   ("Prop 2.2.2 (wallA)", ``MovingSofa.proposition2_2_2_wallA),
   ("Prop 2.2.2 (wallB)", ``MovingSofa.proposition2_2_2_wallB),
   ("Prop 2.2.2 (wallC)", ``MovingSofa.proposition2_2_2_wallC),
   ("Prop 2.2.2 (wallD)", ``MovingSofa.proposition2_2_2_wallD),
   ("Prop 2.2.3", ``MovingSofa.proposition2_2_3),
   ("Prop 2.3.1 (exists)", ``MovingSofa.proposition2_3_1_exists),
   ("Prop 2.3.1 (subset)", ``MovingSofa.proposition2_3_1_subset),
   ("Prop 2.3.1 (unique)", ``MovingSofa.proposition2_3_1_unique),
   ("Prop 2.3.1 (unique horizontal)", ``MovingSofa.proposition2_3_1_unique_horizontal),
   ("Thm 2.3.2", ``MovingSofa.theorem2_3_2),
   ("Prop 2.3.3", ``MovingSofa.proposition2_3_3),
   ("Prop 2.3.4", ``MovingSofa.proposition2_3_4),
   ("Lemma 2.3.5 (hallway)", ``MovingSofa.lemma2_3_5_hallway),
   ("Lemma 2.3.5 (supp)", ``MovingSofa.lemma2_3_5_supp),
   ("Thm 2.3.6", ``MovingSofa.theorem2_3_6),
   ("Thm 2.4.1", ``MovingSofa.theorem2_4_1),
   ("Thm 2.4.2", ``MovingSofa.theorem2_4_2),
   ("Thm 2.4.3", ``MovingSofa.theorem2_4_3),
   ("Thm 2.4.4", ``MovingSofa.theorem2_4_4),
   ("Thm 2.4.4 (iff)", ``MovingSofa.theorem2_4_4_iff),
   ("Prop 2.5.1", ``MovingSofa.proposition2_5_1),
   ("Prop 2.5.2", ``MovingSofa.proposition2_5_2),
   ("Prop 2.5.3", ``MovingSofa.proposition2_5_3),
   ("Prop 2.5.4 (gaps)", ``MovingSofa.proposition2_5_4_gaps),
   ("Prop 2.5.4 (hallway)", ``MovingSofa.proposition2_5_4_hallway),
   ("Prop 2.5.4 (isCap)", ``MovingSofa.proposition2_5_4_isCap),
   ("Prop 2.5.4 (sets)", ``MovingSofa.proposition2_5_4_sets),
   ("Prop 2.5.4 (sigma)", ``MovingSofa.proposition2_5_4_sigma),
   ("Prop 2.5.4 (supp)", ``MovingSofa.proposition2_5_4_supp),
   ("Prop 2.5.4 (vertices)", ``MovingSofa.proposition2_5_4_vertices),
   ("Thm 2.5.5", ``MovingSofa.theorem2_5_5),
   ("Lemma 2.5.6", ``MovingSofa.lemma2_5_6),
   ("Lemma 2.5.7", ``MovingSofa.lemma2_5_7),
   ("Thm 2.5.8", ``MovingSofa.theorem2_5_8),
   ("Thm 2.5.9", ``MovingSofa.theorem2_5_9),
   ("Rem 2.5.2", ``MovingSofa.remark2_5_2),
   ("Thm 2.5.10", ``MovingSofa.theorem2_5_10),
   ("Prop 3.1.1", ``MovingSofa.proposition3_1_1),
   ("Thm 3.1.2", ``MovingSofa.theorem3_1_2),
   ("Prop 3.2.1", ``MovingSofa.proposition3_2_1),
   ("Prop 3.2.1 (fix)", ``MovingSofa.proposition3_2_1_fix),
   ("Prop 3.2.2", ``MovingSofa.proposition3_2_2),
   ("Thm 3.2.3", ``MovingSofa.theorem3_2_3),
   ("Thm 3.2.3 (le)", ``MovingSofa.theorem3_2_3_le),
   ("Prop 3.3.1", ``MovingSofa.proposition3_3_1),
   ("Prop 3.3.2", ``MovingSofa.proposition3_3_2),
   ("Prop 3.3.3", ``MovingSofa.proposition3_3_3),
   ("Prop 3.3.4", ``MovingSofa.proposition3_3_4),
   ("Prop 3.3.5", ``MovingSofa.proposition3_3_5),
   ("Thm 3.3.6", ``MovingSofa.theorem3_3_6),
   ("Prop 3.3.7", ``MovingSofa.proposition3_3_7),
   ("Lemma 3.4.1", ``MovingSofa.lemma3_4_1),
   ("Lemma 3.4.2", ``MovingSofa.lemma3_4_2),
   ("Thm 3.4.3", ``MovingSofa.theorem3_4_3),
   ("Thm 3.4.4", ``MovingSofa.theorem3_4_4),
   ("Lemma 3.4.5 (one)", ``MovingSofa.lemma3_4_5_one),
   ("Lemma 3.4.5 (two)", ``MovingSofa.lemma3_4_5_two),
   ("Lemma 3.4.6", ``MovingSofa.lemma3_4_6),
   ("Lemma 3.4.7", ``MovingSofa.lemma3_4_7),
   ("Lemma 3.4.8", ``MovingSofa.lemma3_4_8),
   ("Thm 3.4.9", ``MovingSofa.theorem3_4_9),
   ("Thm 3.4.10", ``MovingSofa.theorem3_4_10),
   ("Prop 3.5.1", ``MovingSofa.proposition3_5_1),
   ("Thm 3.5.2", ``MovingSofa.theorem3_5_2),
   ("Lemma 3.5.3", ``MovingSofa.lemma3_5_3),
   ("Thm 3.5.4", ``MovingSofa.theorem3_5_4),
   ("Thm 3.5.5", ``MovingSofa.theorem3_5_5),
   ("Thm 3.5.6", ``MovingSofa.theorem3_5_6),
   ("Lemma 4.1.1", ``MovingSofa.lemma4_1_1),
   ("Thm 4.1.2", ``MovingSofa.theorem4_1_2),
   ("Thm 4.1.3", ``MovingSofa.theorem4_1_3),
   ("Thm 4.1.4", ``MovingSofa.theorem4_1_4),
   ("Prop 4.2.1", ``MovingSofa.proposition4_2_1),
   ("Lemma 4.2.2", ``MovingSofa.lemma4_2_2),
   ("Lemma 4.2.3", ``MovingSofa.lemma4_2_3),
   ("Lemma 4.2.4", ``MovingSofa.lemma4_2_4),
   ("Thm 4.2.5", ``MovingSofa.theorem4_2_5),
   ("Prop 5.1.1", ``MovingSofa.proposition5_1_1),
   ("Lemma 5.1.2", ``MovingSofa.lemma5_1_2),
   ("Lemma 5.1.3", ``MovingSofa.lemma5_1_3),
   ("Prop 5.1.4", ``MovingSofa.proposition5_1_4),
   ("Prop 5.1.4 (as stated false)", ``MovingSofa.proposition5_1_4_as_stated_false),
   ("Prop 5.1.4 (deriv)", ``MovingSofa.proposition5_1_4_deriv),
   ("Lemma 5.2.1", ``MovingSofa.lemma5_2_1),
   ("Thm 5.2.2", ``MovingSofa.theorem5_2_2),
   ("Thm 6.1.1", ``MovingSofa.theorem6_1_1),
   ("Thm 6.1.2", ``MovingSofa.theorem6_1_2),
   ("Prop 6.2.1", ``MovingSofa.proposition6_2_1),
   ("Prop 6.2.2", ``MovingSofa.proposition6_2_2),
   ("Thm 6.2.3 (left)", ``MovingSofa.theorem6_2_3_left),
   ("Thm 6.2.3 (right)", ``MovingSofa.theorem6_2_3_right),
   ("Lemma 6.2.4", ``MovingSofa.lemma6_2_4),
   ("Thm 6.2.5", ``MovingSofa.theorem6_2_5),
   ("Thm 6.2.5 (regular)", ``MovingSofa.theorem6_2_5_regular),
   ("Lemma 6.3.1", ``MovingSofa.lemma6_3_1),
   ("Lemma 6.3.2", ``MovingSofa.lemma6_3_2),
   ("Thm 6.3.3", ``MovingSofa.theorem6_3_3),
   ("Lemma 6.4.1", ``MovingSofa.lemma6_4_1),
   ("Lemma 6.4.2", ``MovingSofa.lemma6_4_2),
   ("Thm 6.4.3", ``MovingSofa.theorem6_4_3),
   ("Cor 6.4.4", ``MovingSofa.corollary6_4_4),
   ("Prop 6.4.5", ``MovingSofa.proposition6_4_5),
   ("Prop 6.4.6 (continuous)", ``MovingSofa.proposition6_4_6_continuous),
   ("Prop 6.4.6 (deriv)", ``MovingSofa.proposition6_4_6_deriv),
   ("Thm 6.5.1", ``MovingSofa.theorem6_5_1),
   ("Lemma 6.5.2", ``MovingSofa.lemma6_5_2),
   ("Lemma 6.5.3", ``MovingSofa.lemma6_5_3),
   ("Lemma 6.5.4", ``MovingSofa.lemma6_5_4),
   ("Lemma 6.5.5", ``MovingSofa.lemma6_5_5),
   ("Thm 6.5.6", ``MovingSofa.theorem6_5_6),
   ("Thm 7.1.1", ``MovingSofa.theorem7_1_1),
   ("Thm 7.1.2 (sigma)", ``MovingSofa.theorem7_1_2_sigma),
   ("Thm 7.1.2 (supp)", ``MovingSofa.theorem7_1_2_supp),
   ("Thm 7.1.2 (vertices)", ``MovingSofa.theorem7_1_2_vertices),
   ("Thm 7.1.3", ``MovingSofa.theorem7_1_3),
   ("Thm 7.1.3 (quadratic)", ``MovingSofa.theorem7_1_3_quadratic),
   ("Lemma 7.1.4", ``MovingSofa.lemma7_1_4),
   ("Thm 7.1.5", ``MovingSofa.theorem7_1_5),
   ("Lemma 7.1.6", ``MovingSofa.lemma7_1_6),
   ("Prop 7.2.2", ``MovingSofa.proposition7_2_2),
   ("Prop 7.2.4", ``MovingSofa.proposition7_2_4),
   ("Prop 7.2.4 (line)", ``MovingSofa.proposition7_2_4_line),
   ("Prop 7.2.5", ``MovingSofa.proposition7_2_5),
   ("Prop 7.2.6", ``MovingSofa.proposition7_2_6),
   ("Lemma 7.3.1", ``MovingSofa.lemma7_3_1),
   ("Lemma 7.3.1 (degenerate)", ``MovingSofa.lemma7_3_1_degenerate),
   ("Thm 7.3.2", ``MovingSofa.theorem7_3_2),
   ("Thm 7.3.2 (quadratic)", ``MovingSofa.theorem7_3_2_quadratic),
   ("Lemma 7.3.3", ``MovingSofa.lemma7_3_3),
   ("Lemma 7.3.3 (self)", ``MovingSofa.lemma7_3_3_self),
   ("Lemma 7.3.4", ``MovingSofa.lemma7_3_4),
   ("Lemma 7.3.5", ``MovingSofa.lemma7_3_5),
   ("Thm 7.4.1", ``MovingSofa.theorem7_4_1),
   ("Thm 7.4.2", ``MovingSofa.theorem7_4_2),
   ("Thm 8.1.1 (balanced)", ``MovingSofa.theorem8_1_1_balanced),
   ("Thm 8.1.1 (convex)", ``MovingSofa.theorem8_1_1_convex),
   ("Thm 8.1.1 (gerver)", ``MovingSofa.theorem8_1_1_gerver),
   ("Def 8.1.2 (exists)", ``MovingSofa.definition8_1_2_exists),
   ("Def 8.1.2 (unique)", ``MovingSofa.definition8_1_2_unique),
   ("Prop 8.1.2", ``MovingSofa.proposition8_1_2),
   ("Lemma 8.1.3", ``MovingSofa.lemma8_1_3),
   ("Lemma 8.1.4", ``MovingSofa.lemma8_1_4),
   ("Lemma 8.1.5", ``MovingSofa.lemma8_1_5),
   ("Lemma 8.1.6 (left)", ``MovingSofa.lemma8_1_6_left),
   ("Lemma 8.1.6 (right)", ``MovingSofa.lemma8_1_6_right),
   ("Lemma 8.1.7 (four)", ``MovingSofa.lemma8_1_7_four),
   ("Lemma 8.1.7 (one)", ``MovingSofa.lemma8_1_7_one),
   ("Lemma 8.1.7 (three)", ``MovingSofa.lemma8_1_7_three),
   ("Lemma 8.1.7 (two)", ``MovingSofa.lemma8_1_7_two),
   ("Thm 8.1.8", ``MovingSofa.theorem8_1_8),
   ("Prop 8.2.1", ``MovingSofa.proposition8_2_1),
   ("Lemma 8.2.2", ``MovingSofa.lemma8_2_2),
   ("Lemma 8.2.3", ``MovingSofa.lemma8_2_3),
   ("Thm 8.2.4", ``MovingSofa.theorem8_2_4),
   ("Thm 8.3.1", ``MovingSofa.theorem8_3_1),
   ("Thm 8.3.2", ``MovingSofa.theorem8_3_2),
   ("Lemma 8.3.3", ``MovingSofa.lemma8_3_3),
   ("Lemma 8.3.4", ``MovingSofa.lemma8_3_4),
   ("Lemma 8.3.5", ``MovingSofa.lemma8_3_5),
   ("Lemma 8.3.6", ``MovingSofa.lemma8_3_6),
   ("Lemma 8.3.7", ``MovingSofa.lemma8_3_7),
   ("Thm 8.3.8", ``MovingSofa.theorem8_3_8),
   ("Thm 8.4.1 (monotone)", ``MovingSofa.theorem8_4_1_monotone),
   ("Thm 8.4.1 (niche)", ``MovingSofa.theorem8_4_1_niche),
   ("Thm 8.4.1 (tangents)", ``MovingSofa.theorem8_4_1_tangents),
   ("Thm 8.4.1 (walls)", ``MovingSofa.theorem8_4_1_walls),
   ("Thm 8.4.2", ``MovingSofa.theorem8_4_2),
   ("Thm 8.4.3 (one)", ``MovingSofa.theorem8_4_3_one),
   ("Thm 8.4.3 (three)", ``MovingSofa.theorem8_4_3_three),
   ("Thm 8.4.3 (two)", ``MovingSofa.theorem8_4_3_two),
   ("Prop 8.4.4", ``MovingSofa.proposition8_4_4),
   ("Thm 8.4.5", ``MovingSofa.theorem8_4_5),
   ("Thm 8.4.6", ``MovingSofa.theorem8_4_6),
   ("Thm 8.5.1", ``MovingSofa.theorem8_5_1),
   ("Thm 8.5.2", ``MovingSofa.theorem8_5_2),
   ("Thm 8.5.3", ``MovingSofa.theorem8_5_3),
   ("Thm 8.5.4", ``MovingSofa.theorem8_5_4),
   ("Thm 8.5.5", ``MovingSofa.theorem8_5_5),
   ("Thm 8.5.6", ``MovingSofa.theorem8_5_6),
   ("Thm 8.5.7", ``MovingSofa.theorem8_5_7),
   ("Cor 8.5.8", ``MovingSofa.corollary8_5_8)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``MovingSofaChallenge.gerver_params_exists,
   ``MovingSofaChallenge.gerver_params_unique,
   ``MovingSofaChallenge.gerver_sofa_optimal]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`MovingSofa).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
