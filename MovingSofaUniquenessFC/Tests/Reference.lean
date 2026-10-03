module

public import MovingSofaUniquenessFC.Final

/-!
# Exact-reference interface examples

These examples record the intended types and dependency directions. They have
NOT been executed. Their presence is not a report of successful elaboration,
passed tests, a source-wide tactic scan, or a computed axiom audit.

No independent Challenge module is imported: all dependencies are the actual
solution modules. In particular parameter existence is not a statement axiom,
and the concrete-reference equality is independent of sofa shape uniqueness.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory
open scoped EuclideanGeometry unitInterval

namespace MovingSofaUniquenessFC.Tests

open MovingSofaUniqueness

/-- The full non-strict upstream parameter domain, not a boxed substitute. -/
example : ∃! q : ℝ × ℝ × ℝ × ℝ,
    MovingSofa.GerversSofa.ABφθSpec q.1 q.2.1 q.2.2.1 q.2.2.2 :=
  MovingSofa.GerversSofa.ABφθSpec.existsUnique

/-- Literal equality of the canonical reference with any valid paper witness. -/
example {P : MovingSofaOptimality.GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    Bridge.coordinates '' MovingSofa.gerversSofa = MovingSofaOptimality.gerverSofa P :=
  Bridge.coordinates_gerversSofa_eq_paper hP hbox

/-- The inverse-coordinate statement is also exact set equality. -/
example {P : MovingSofaOptimality.GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofa.gerversSofa = Bridge.point '' MovingSofaOptimality.gerverSofa P :=
  Bridge.gerversSofa_eq_point_paper hP hbox

/-- The translation BEFORE rotation is not confused with the path AFTER it. -/
example (t : ℝ) :
    MovingSofaOptimality.rot t (MovingSofa.GerversSofa.referenceData.prePath t) =
      MovingSofa.GerversSofa.referenceData.toPaper.path t :=
  Reference.Data.rotated_prePath MovingSofa.GerversSofa.referenceData_valid t

/-- The actual oriented upstream rotation, not an arbitrary realization. -/
example (t : ℝ) (p q : Bridge.Point) :
    Bridge.coordinates (MovingSofa.rotateTranslate (t : Real.Angle) p q) =
      MovingSofaOptimality.rot t (Bridge.coordinates q + Bridge.coordinates p) :=
  Bridge.reference_rotateTranslate_coordinates t p q

/-- Concrete reference motion and attainment are derived facts. -/
example : (∃ m, MovingSofa.IsMovingSofa MovingSofa.gerversSofa m) ∧
    MovingSofa.sofaConstant = volume MovingSofa.gerversSofa :=
  ⟨MovingSofa.isMovingSofa_gerversSofa, MovingSofa.sofaConstant_eq_volume_gerversSofa⟩

/-- Exactly the requested statement, with no additional regularity or
reference-identification hypothesis. -/
example (s : Set ℝ²) (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : ℝ² ≃ᵃⁱ[ℝ] ℝ², s = g '' MovingSofa.gerversSofa :=
  MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa s hs

end MovingSofaUniquenessFC.Tests
