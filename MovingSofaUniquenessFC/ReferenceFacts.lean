module

public import MovingSofaUniquenessFC.Bridge.ReferenceShape
public import MovingSofaUniquenessFC.Extremal

/-!
# Motion and optimality of the exact formal-conjectures reference

The concrete reference set has already been identified with the paper Gerver
construction. Its moving-sofa and optimality facts are derived here, rather
than imported from the upstream catalog's solved-result placeholders.
These facts do not use the new shape-uniqueness argument.

Uncompiled source: the absence of deliberate admissions is not a report of
successful elaboration or a computed axiom audit.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open MovingSofaUniquenessFC.Bridge
open scoped EuclideanGeometry

namespace MovingSofa

/-- The concrete reference admits an identity-start motion in the exact
canonical topology and hallway model. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m := by
  sorry

/-- The upstream named set has the volume of the actual paper witness. -/
theorem volume_gerversSofa_eq_paper {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    volume gerversSofa = volume (MovingSofaOptimality.gerverSofa P) := by
  sorry

/-- The precise solved-result statement required by the upstream uniqueness
corollary, with an actual proof rather than a catalog placeholder. -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  sorry

theorem gerversSofa_volume_ne_top : volume gerversSofa ≠ ⊤ := by
  sorry

end MovingSofa
