module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the library, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find PaperName -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
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
import all MovingSofaUniqueness.Alternative
import all MovingSofaUniqueness.AngleExtension
import all MovingSofaUniqueness.Curvature
import all MovingSofaUniqueness.Main
import all MovingSofaUniqueness.Maximizers
import all MovingSofaUniqueness.Optimality
import all MovingSofaUniqueness.RegularClosed
import all MovingSofaUniqueness.Rigid
import all MovingSofaUniqueness.Rigidity
import all MovingSofaUniqueness.Selection
import all MovingSofaUniqueness.Variation
import all MovingSofaBridge.GerverConstants
import all MovingSofaBridge.GerverSofa
import all MovingSofaBridge.Motion
import all MovingSofaBridge.RomikParams
import all ChallengeDefs
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`MovingSofaOptimality/External/`) that its proof uses. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the route of every numbered result of the paper to `.lake/route_deps.tsv`: the
other numbered results that its proof uses, found by following the proof through the library's
helper lemmas and stopping at numbered results, with the TeX label that the result's docstring
names in backticks. `scripts/route_check.py` compares these routes with the results that the
paper's proofs cite (`docs/paper_routes.tsv`).

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, proved in `MovingSofaOptimality/External/`, with a short label. Their
proofs are not searched: the traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Schneider, Remark 5.1.2: |K| = ½∫ h_K dσ_K", ``MovingSofaOptimality.area_eq_half_integral_supp),
   ("Romik 2018: Romik's system has a solution in the box", ``MovingSofaOptimality.GerverParams.romik_exists),
   ("Romik 2018: the solution in the box is unique", ``MovingSofaOptimality.GerverParams.romik_unique)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Thm 1.1.1", ``MovingSofaOptimality.theorem1_1_1),
   ("Prop 1.2.2", ``MovingSofaOptimality.proposition1_2_2),
   ("Thm 1.5.1", ``MovingSofaOptimality.theorem1_5_1),
   ("Thm 1.5.2", ``MovingSofaOptimality.theorem1_5_2),
   ("Thm 1.7.1", ``MovingSofaOptimality.theorem1_7_1),
   ("Prop 2.1.2", ``MovingSofaOptimality.proposition2_1_2),
   ("Thm 2.1.3 (vint left)", ``MovingSofaOptimality.tendsto_vint_left),
   ("Thm 2.1.3 (vint right)", ``MovingSofaOptimality.tendsto_vint_right),
   ("Thm 2.1.3 (vminus left)", ``MovingSofaOptimality.tendsto_vminus_left),
   ("Thm 2.1.3 (vminus right)", ``MovingSofaOptimality.tendsto_vminus_right),
   ("Thm 2.1.3 (vplus left)", ``MovingSofaOptimality.tendsto_vplus_left),
   ("Thm 2.1.3 (vplus right)", ``MovingSofaOptimality.tendsto_vplus_right),
   ("Prop 2.2.1", ``MovingSofaOptimality.proposition2_2_1),
   ("Prop 2.2.2 (hallway)", ``MovingSofaOptimality.proposition2_2_2_hallway),
   ("Prop 2.2.2 (innerCorner)", ``MovingSofaOptimality.proposition2_2_2_innerCorner),
   ("Prop 2.2.2 (outerCorner)", ``MovingSofaOptimality.proposition2_2_2_outerCorner),
   ("Prop 2.2.2 (qMinus)", ``MovingSofaOptimality.proposition2_2_2_qMinus),
   ("Prop 2.2.2 (qPlus)", ``MovingSofaOptimality.proposition2_2_2_qPlus),
   ("Prop 2.2.2 (wallA)", ``MovingSofaOptimality.proposition2_2_2_wallA),
   ("Prop 2.2.2 (wallB)", ``MovingSofaOptimality.proposition2_2_2_wallB),
   ("Prop 2.2.2 (wallC)", ``MovingSofaOptimality.proposition2_2_2_wallC),
   ("Prop 2.2.2 (wallD)", ``MovingSofaOptimality.proposition2_2_2_wallD),
   ("Prop 2.2.3", ``MovingSofaOptimality.proposition2_2_3),
   ("Prop 2.3.1 (exists)", ``MovingSofaOptimality.proposition2_3_1_exists),
   ("Prop 2.3.1 (subset)", ``MovingSofaOptimality.proposition2_3_1_subset),
   ("Prop 2.3.1 (unique)", ``MovingSofaOptimality.proposition2_3_1_unique),
   ("Prop 2.3.1 (unique horizontal)", ``MovingSofaOptimality.proposition2_3_1_unique_horizontal),
   ("Thm 2.3.2", ``MovingSofaOptimality.theorem2_3_2),
   ("Prop 2.3.3", ``MovingSofaOptimality.proposition2_3_3),
   ("Prop 2.3.4", ``MovingSofaOptimality.proposition2_3_4),
   ("Lemma 2.3.5 (hallway)", ``MovingSofaOptimality.lemma2_3_5_hallway),
   ("Lemma 2.3.5 (supp)", ``MovingSofaOptimality.lemma2_3_5_supp),
   ("Thm 2.3.6", ``MovingSofaOptimality.theorem2_3_6),
   ("Thm 2.4.1", ``MovingSofaOptimality.theorem2_4_1),
   ("Thm 2.4.2", ``MovingSofaOptimality.theorem2_4_2),
   ("Thm 2.4.3", ``MovingSofaOptimality.theorem2_4_3),
   ("Thm 2.4.4", ``MovingSofaOptimality.theorem2_4_4),
   ("Thm 2.4.4 (iff)", ``MovingSofaOptimality.theorem2_4_4_iff),
   ("Prop 2.5.1", ``MovingSofaOptimality.proposition2_5_1),
   ("Prop 2.5.2", ``MovingSofaOptimality.proposition2_5_2),
   ("Prop 2.5.3", ``MovingSofaOptimality.proposition2_5_3),
   ("Prop 2.5.4 (gaps)", ``MovingSofaOptimality.proposition2_5_4_gaps),
   ("Prop 2.5.4 (hallway)", ``MovingSofaOptimality.proposition2_5_4_hallway),
   ("Prop 2.5.4 (isCap)", ``MovingSofaOptimality.proposition2_5_4_isCap),
   ("Prop 2.5.4 (sets)", ``MovingSofaOptimality.proposition2_5_4_sets),
   ("Prop 2.5.4 (sigma)", ``MovingSofaOptimality.proposition2_5_4_sigma),
   ("Prop 2.5.4 (supp)", ``MovingSofaOptimality.proposition2_5_4_supp),
   ("Prop 2.5.4 (vertices)", ``MovingSofaOptimality.proposition2_5_4_vertices),
   ("Thm 2.5.5", ``MovingSofaOptimality.theorem2_5_5),
   ("Lemma 2.5.6", ``MovingSofaOptimality.lemma2_5_6),
   ("Lemma 2.5.7", ``MovingSofaOptimality.lemma2_5_7),
   ("Thm 2.5.8", ``MovingSofaOptimality.theorem2_5_8),
   ("Thm 2.5.9", ``MovingSofaOptimality.theorem2_5_9),
   ("Rem 2.5.2", ``MovingSofaOptimality.remark2_5_2),
   ("Thm 2.5.10", ``MovingSofaOptimality.theorem2_5_10),
   ("Prop 3.1.1", ``MovingSofaOptimality.proposition3_1_1),
   ("Thm 3.1.2", ``MovingSofaOptimality.theorem3_1_2),
   ("Prop 3.2.1", ``MovingSofaOptimality.proposition3_2_1),
   ("Prop 3.2.1 (fix)", ``MovingSofaOptimality.proposition3_2_1_fix),
   ("Prop 3.2.2", ``MovingSofaOptimality.proposition3_2_2),
   ("Thm 3.2.3", ``MovingSofaOptimality.theorem3_2_3),
   ("Thm 3.2.3 (le)", ``MovingSofaOptimality.theorem3_2_3_le),
   ("Prop 3.3.1", ``MovingSofaOptimality.proposition3_3_1),
   ("Prop 3.3.2", ``MovingSofaOptimality.proposition3_3_2),
   ("Prop 3.3.3", ``MovingSofaOptimality.proposition3_3_3),
   ("Prop 3.3.4", ``MovingSofaOptimality.proposition3_3_4),
   ("Prop 3.3.5", ``MovingSofaOptimality.proposition3_3_5),
   ("Thm 3.3.6", ``MovingSofaOptimality.theorem3_3_6),
   ("Prop 3.3.7", ``MovingSofaOptimality.proposition3_3_7),
   ("Lemma 3.4.1", ``MovingSofaOptimality.lemma3_4_1),
   ("Lemma 3.4.2", ``MovingSofaOptimality.lemma3_4_2),
   ("Thm 3.4.3", ``MovingSofaOptimality.theorem3_4_3),
   ("Thm 3.4.4", ``MovingSofaOptimality.theorem3_4_4),
   ("Lemma 3.4.5 (one)", ``MovingSofaOptimality.lemma3_4_5_one),
   ("Lemma 3.4.5 (two)", ``MovingSofaOptimality.lemma3_4_5_two),
   ("Lemma 3.4.6", ``MovingSofaOptimality.lemma3_4_6),
   ("Lemma 3.4.7", ``MovingSofaOptimality.lemma3_4_7),
   ("Lemma 3.4.8", ``MovingSofaOptimality.lemma3_4_8),
   ("Thm 3.4.9", ``MovingSofaOptimality.theorem3_4_9),
   ("Thm 3.4.10", ``MovingSofaOptimality.theorem3_4_10),
   ("Prop 3.5.1", ``MovingSofaOptimality.proposition3_5_1),
   ("Thm 3.5.2", ``MovingSofaOptimality.theorem3_5_2),
   ("Lemma 3.5.3", ``MovingSofaOptimality.lemma3_5_3),
   ("Thm 3.5.4", ``MovingSofaOptimality.theorem3_5_4),
   ("Thm 3.5.5", ``MovingSofaOptimality.theorem3_5_5),
   ("Thm 3.5.6", ``MovingSofaOptimality.theorem3_5_6),
   ("Lemma 4.1.1", ``MovingSofaOptimality.lemma4_1_1),
   ("Thm 4.1.2", ``MovingSofaOptimality.theorem4_1_2),
   ("Thm 4.1.3", ``MovingSofaOptimality.theorem4_1_3),
   ("Thm 4.1.4", ``MovingSofaOptimality.theorem4_1_4),
   ("Prop 4.2.1", ``MovingSofaOptimality.proposition4_2_1),
   ("Lemma 4.2.2", ``MovingSofaOptimality.lemma4_2_2),
   ("Lemma 4.2.3", ``MovingSofaOptimality.lemma4_2_3),
   ("Lemma 4.2.4", ``MovingSofaOptimality.lemma4_2_4),
   ("Thm 4.2.5", ``MovingSofaOptimality.theorem4_2_5),
   ("Prop 5.1.1", ``MovingSofaOptimality.proposition5_1_1),
   ("Lemma 5.1.2", ``MovingSofaOptimality.lemma5_1_2),
   ("Lemma 5.1.3", ``MovingSofaOptimality.lemma5_1_3),
   ("Prop 5.1.4", ``MovingSofaOptimality.proposition5_1_4),
   ("Prop 5.1.4 (as stated false)", ``MovingSofaOptimality.proposition5_1_4_as_stated_false),
   ("Prop 5.1.4 (deriv)", ``MovingSofaOptimality.proposition5_1_4_deriv),
   ("Lemma 5.2.1", ``MovingSofaOptimality.lemma5_2_1),
   ("Thm 5.2.2", ``MovingSofaOptimality.theorem5_2_2),
   ("Thm 6.1.1", ``MovingSofaOptimality.theorem6_1_1),
   ("Thm 6.1.2", ``MovingSofaOptimality.theorem6_1_2),
   ("Prop 6.2.1", ``MovingSofaOptimality.proposition6_2_1),
   ("Prop 6.2.2", ``MovingSofaOptimality.proposition6_2_2),
   ("Thm 6.2.3 (left)", ``MovingSofaOptimality.theorem6_2_3_left),
   ("Thm 6.2.3 (right)", ``MovingSofaOptimality.theorem6_2_3_right),
   ("Lemma 6.2.4", ``MovingSofaOptimality.lemma6_2_4),
   ("Thm 6.2.5", ``MovingSofaOptimality.theorem6_2_5),
   ("Thm 6.2.5 (regular)", ``MovingSofaOptimality.theorem6_2_5_regular),
   ("Lemma 6.3.1", ``MovingSofaOptimality.lemma6_3_1),
   ("Lemma 6.3.2", ``MovingSofaOptimality.lemma6_3_2),
   ("Thm 6.3.3", ``MovingSofaOptimality.theorem6_3_3),
   ("Lemma 6.4.1", ``MovingSofaOptimality.lemma6_4_1),
   ("Lemma 6.4.2", ``MovingSofaOptimality.lemma6_4_2),
   ("Thm 6.4.3", ``MovingSofaOptimality.theorem6_4_3),
   ("Cor 6.4.4", ``MovingSofaOptimality.corollary6_4_4),
   ("Prop 6.4.5", ``MovingSofaOptimality.proposition6_4_5),
   ("Prop 6.4.6 (continuous)", ``MovingSofaOptimality.proposition6_4_6_continuous),
   ("Prop 6.4.6 (deriv)", ``MovingSofaOptimality.proposition6_4_6_deriv),
   ("Thm 6.5.1", ``MovingSofaOptimality.theorem6_5_1),
   ("Lemma 6.5.2", ``MovingSofaOptimality.lemma6_5_2),
   ("Lemma 6.5.3", ``MovingSofaOptimality.lemma6_5_3),
   ("Lemma 6.5.4", ``MovingSofaOptimality.lemma6_5_4),
   ("Lemma 6.5.5", ``MovingSofaOptimality.lemma6_5_5),
   ("Thm 6.5.6", ``MovingSofaOptimality.theorem6_5_6),
   ("Thm 7.1.1", ``MovingSofaOptimality.theorem7_1_1),
   ("Thm 7.1.2 (sigma)", ``MovingSofaOptimality.theorem7_1_2_sigma),
   ("Thm 7.1.2 (supp)", ``MovingSofaOptimality.theorem7_1_2_supp),
   ("Thm 7.1.2 (vertices)", ``MovingSofaOptimality.theorem7_1_2_vertices),
   ("Thm 7.1.3", ``MovingSofaOptimality.theorem7_1_3),
   ("Thm 7.1.3 (quadratic)", ``MovingSofaOptimality.theorem7_1_3_quadratic),
   ("Lemma 7.1.4", ``MovingSofaOptimality.lemma7_1_4),
   ("Thm 7.1.5", ``MovingSofaOptimality.theorem7_1_5),
   ("Lemma 7.1.6", ``MovingSofaOptimality.lemma7_1_6),
   ("Prop 7.2.2", ``MovingSofaOptimality.proposition7_2_2),
   ("Prop 7.2.4", ``MovingSofaOptimality.proposition7_2_4),
   ("Prop 7.2.4 (line)", ``MovingSofaOptimality.proposition7_2_4_line),
   ("Prop 7.2.5", ``MovingSofaOptimality.proposition7_2_5),
   ("Prop 7.2.6", ``MovingSofaOptimality.proposition7_2_6),
   ("Lemma 7.3.1", ``MovingSofaOptimality.lemma7_3_1),
   ("Lemma 7.3.1 (degenerate)", ``MovingSofaOptimality.lemma7_3_1_degenerate),
   ("Thm 7.3.2", ``MovingSofaOptimality.theorem7_3_2),
   ("Thm 7.3.2 (quadratic)", ``MovingSofaOptimality.theorem7_3_2_quadratic),
   ("Lemma 7.3.3", ``MovingSofaOptimality.lemma7_3_3),
   ("Lemma 7.3.3 (self)", ``MovingSofaOptimality.lemma7_3_3_self),
   ("Lemma 7.3.4", ``MovingSofaOptimality.lemma7_3_4),
   ("Lemma 7.3.5", ``MovingSofaOptimality.lemma7_3_5),
   ("Thm 7.4.1", ``MovingSofaOptimality.theorem7_4_1),
   ("Thm 7.4.2", ``MovingSofaOptimality.theorem7_4_2),
   ("Thm 8.1.1 (balanced)", ``MovingSofaOptimality.theorem8_1_1_balanced),
   ("Thm 8.1.1 (convex)", ``MovingSofaOptimality.theorem8_1_1_convex),
   ("Thm 8.1.1 (gerver)", ``MovingSofaOptimality.theorem8_1_1_gerver),
   ("Def 8.1.2 (exists)", ``MovingSofaOptimality.definition8_1_2_exists),
   ("Def 8.1.2 (unique)", ``MovingSofaOptimality.definition8_1_2_unique),
   ("Prop 8.1.2", ``MovingSofaOptimality.proposition8_1_2),
   ("Lemma 8.1.3", ``MovingSofaOptimality.lemma8_1_3),
   ("Lemma 8.1.4", ``MovingSofaOptimality.lemma8_1_4),
   ("Lemma 8.1.5", ``MovingSofaOptimality.lemma8_1_5),
   ("Lemma 8.1.6 (left)", ``MovingSofaOptimality.lemma8_1_6_left),
   ("Lemma 8.1.6 (right)", ``MovingSofaOptimality.lemma8_1_6_right),
   ("Lemma 8.1.7 (four)", ``MovingSofaOptimality.lemma8_1_7_four),
   ("Lemma 8.1.7 (one)", ``MovingSofaOptimality.lemma8_1_7_one),
   ("Lemma 8.1.7 (three)", ``MovingSofaOptimality.lemma8_1_7_three),
   ("Lemma 8.1.7 (two)", ``MovingSofaOptimality.lemma8_1_7_two),
   ("Thm 8.1.8", ``MovingSofaOptimality.theorem8_1_8),
   ("Prop 8.2.1", ``MovingSofaOptimality.proposition8_2_1),
   ("Lemma 8.2.2", ``MovingSofaOptimality.lemma8_2_2),
   ("Lemma 8.2.3", ``MovingSofaOptimality.lemma8_2_3),
   ("Thm 8.2.4", ``MovingSofaOptimality.theorem8_2_4),
   ("Thm 8.3.1", ``MovingSofaOptimality.theorem8_3_1),
   ("Thm 8.3.2", ``MovingSofaOptimality.theorem8_3_2),
   ("Lemma 8.3.3", ``MovingSofaOptimality.lemma8_3_3),
   ("Lemma 8.3.4", ``MovingSofaOptimality.lemma8_3_4),
   ("Lemma 8.3.5", ``MovingSofaOptimality.lemma8_3_5),
   ("Lemma 8.3.6", ``MovingSofaOptimality.lemma8_3_6),
   ("Lemma 8.3.7", ``MovingSofaOptimality.lemma8_3_7),
   ("Thm 8.3.8", ``MovingSofaOptimality.theorem8_3_8),
   ("Thm 8.4.1 (monotone)", ``MovingSofaOptimality.theorem8_4_1_monotone),
   ("Thm 8.4.1 (niche)", ``MovingSofaOptimality.theorem8_4_1_niche),
   ("Thm 8.4.1 (tangents)", ``MovingSofaOptimality.theorem8_4_1_tangents),
   ("Thm 8.4.1 (walls)", ``MovingSofaOptimality.theorem8_4_1_walls),
   ("Thm 8.4.2", ``MovingSofaOptimality.theorem8_4_2),
   ("Thm 8.4.3 (one)", ``MovingSofaOptimality.theorem8_4_3_one),
   ("Thm 8.4.3 (three)", ``MovingSofaOptimality.theorem8_4_3_three),
   ("Thm 8.4.3 (two)", ``MovingSofaOptimality.theorem8_4_3_two),
   ("Prop 8.4.4", ``MovingSofaOptimality.proposition8_4_4),
   ("Thm 8.4.5", ``MovingSofaOptimality.theorem8_4_5),
   ("Thm 8.4.6", ``MovingSofaOptimality.theorem8_4_6),
   ("Thm 8.5.1", ``MovingSofaOptimality.theorem8_5_1),
   ("Thm 8.5.2", ``MovingSofaOptimality.theorem8_5_2),
   ("Thm 8.5.3", ``MovingSofaOptimality.theorem8_5_3),
   ("Thm 8.5.4", ``MovingSofaOptimality.theorem8_5_4),
   ("Thm 8.5.5", ``MovingSofaOptimality.theorem8_5_5),
   ("Thm 8.5.6", ``MovingSofaOptimality.theorem8_5_6),
   ("Thm 8.5.7", ``MovingSofaOptimality.theorem8_5_7),
   ("Cor 8.5.8", ``MovingSofaOptimality.corollary8_5_8)]

/-- The uniqueness of Gerver's sofa (`MovingSofaUniqueness/`): the theorem and the propositions of its
argument, `docs/archive/uniqueness/20-complete-paper-proof.md`, the refinements that the
manuscript `docs/paper` states, and the second proof of optimality of its Section 8.4; and the
bridge to formal-conjectures' definitions (`MovingSofaBridge/`). -/
meta def uniquenessResults : List (String × Name) :=
  [("Uniqueness theorem", ``MovingSofaUniqueness.image_eq_gerver_of_volume_eq),
   ("Uniqueness: Prop 1", ``MovingSofaUniqueness.exists_selectedCapSequence),
   ("Uniqueness: Prop 2 (floating)", ``MovingSofaUniqueness.floating_defect_le),
   ("Uniqueness: Prop 2 (pinned)", ``MovingSofaUniqueness.pinned_defect_le),
   ("Uniqueness: Prop 3 (curvature)", ``MovingSofaUniqueness.curvature_of_maximal_positive),
   ("Uniqueness: Prop 3 (injectivity)", ``MovingSofaUniqueness.isKi_of_maximal_area),
   ("Uniqueness: Prop 4 (pinned bounds)", ``MovingSofaUniqueness.pinned_bounds_of_maximal_positive),
   ("Uniqueness: Prop 4 (right-angle motion)", ``MovingSofaUniqueness.maximal_monotone_has_right_angle),
   ("Uniqueness: Prop 5", ``MovingSofaUniqueness.ki_sofa_eq_gerver_translate),
   ("Uniqueness: Prop 6", ``MovingSofaUniqueness.gerver_regularClosed),
   ("Uniqueness: maximizing right-angle caps (manuscript `thm:caps`)",
    ``MovingSofaUniqueness.sofaArea_eq_gerver_iff),
   ("Uniqueness: the maximal sofas (manuscript `cor:all`)",
    ``MovingSofaUniqueness.isMaximal_iff_image_eq_gerver),
   ("Uniqueness: no rotation is needed (manuscript `cor:translate`)",
    ``MovingSofaUniqueness.translate_eq_gerver_of_volume_eq),
   ("Uniqueness: a second proof of optimality (manuscript `thm:second`)",
    ``MovingSofaUniqueness.MaximizerRoute.gerver_sofa_optimal),
   ("Uniqueness: the theorem from the second proof (manuscript `sec:second`)",
    ``MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq),
   ("Bridge: moving sofas", ``MovingSofaBridge.isMovingSofa_iff),
   ("Bridge: the sofa constant", ``MovingSofaBridge.sofaConstant_eq),
   ("Bridge: Gerver's constants", ``MovingSofaBridge.GerverConstants.spec_existsUnique),
   ("Bridge: Gerver's sofa", ``MovingSofaBridge.gerversSofa_eq)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``Baek.gerver_params_exists,
   ``Baek.gerver_params_unique,
   ``Baek.gerver_sofa_area,
   ``Baek.gerver_sofa_optimal,
   ``Baek.gerver_sofa_unique,
   ``Bridge.isMovingSofa_iff,
   ``Bridge.sofaConstant_eq,
   ``Bridge.gerversSofa_eq,
   ``FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique,
   ``FormalConjectures.MovingSofa.isMovingSofa_gerversSofa,
   ``FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa,
   ``FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library (Baek's paper, the uniqueness of Gerver's sofa, the bridge
to formal-conjectures' definitions, and the Challenge's definitions). -/
meta def isLibraryModule (m : Name) : Bool :=
  (`MovingSofaOptimality).isPrefixOf m || (`MovingSofaUniqueness).isPrefixOf m ||
    (`MovingSofaBridge).isPrefixOf m || m == `ChallengeDefs

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

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults ++ uniquenessResults do
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
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
