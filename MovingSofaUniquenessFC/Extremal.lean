module

public import MovingSofaUniquenessFC.Bridge.Motions

/-!
# The same extremal problem in the paper and formal-conjectures models

This module uses formal-conjectures' canonical Euclidean motion model together
with the paper development `MovingSofaOptimality`. No upstream theorem
placeholder or shape-uniqueness result is used here.

The exact ENNReal supremum equals the volume of each of the paper's Gerver
witnesses. Consequently the canonical supremum is finite and attained, and
being a canonical maximizer is equivalent to being a maximizer in the paper
presentation after taking coordinates.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open MovingSofaUniquenessFC.Bridge
open scoped EuclideanGeometry

namespace MovingSofa.Canonical

/-- A maximizer in the precise identity-start Euclidean motion model. -/
def IsMaximizer (s : Set Point) : Prop :=
  (∃ m, MovingSofa.IsMovingSofa s m) ∧ volume s = MovingSofa.sofaConstant

/-- A canonical moving sofa is compact. This is a property of its actual set,
not just of some congruent placement. -/
theorem compact_of_moving {s : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) : IsCompact s := by
  have h := MovingSofaOptimality.isCompact_of_isMovingSofa (canonical_to_paper hs)
  simpa only [point_coordinates_image] using h.image point_continuous

/-- The supremum in the canonical presentation agrees with the exact volume
of the paper's Gerver witness. This does not identify the two explicit Gerver
parameterizations and makes no use of uniqueness. -/
theorem constant_eq_paper_gerver {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofa.sofaConstant = volume (MovingSofaOptimality.gerverSofa P) := by
  have hG := MovingSofaOptimality.theorem1_1_1 hP hbox
  apply le_antisymm
  · unfold MovingSofa.sofaConstant
    refine iSup_le fun s => iSup_le fun hs => ?_
    rw [← volume_coordinates_image s]
    exact hG.2 _ (canonical_to_paper hs)
  · obtain ⟨s, hs, hvol⟩ := paper_to_canonical hG.1
    rw [← hvol]
    exact volume_le_constant hs

/-- Finiteness is proved before any use of ENNReal.toReal injectivity. -/
theorem constant_ne_top : MovingSofa.sofaConstant ≠ ⊤ := by
  obtain ⟨P, hP, hbox⟩ := MovingSofaOptimality.definition8_1_2_exists
  rw [constant_eq_paper_gerver hP hbox]
  exact MovingSofaOptimality.gerverSofa_volume_ne_top hP hbox

/-- The canonical supremum is attained by an actual identity-start placement. -/
theorem exists_maximizer : ∃ s : Set Point, IsMaximizer s := by
  obtain ⟨P, hP, hbox⟩ := MovingSofaOptimality.definition8_1_2_exists
  obtain ⟨s, hs, hvol⟩ :=
    paper_to_canonical (MovingSofaOptimality.theorem1_1_1 hP hbox).1
  refine ⟨s, hs, ?_⟩
  exact hvol.trans (constant_eq_paper_gerver hP hbox).symm

/-- The canonical maximum bounds every competitor in the paper model,
including a competitor not already placed in the horizontal hallway. -/
theorem paper_volume_le_constant {S : Set CoordinatePlane}
    (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ MovingSofa.sofaConstant := by
  obtain ⟨s, hs, hvol⟩ := paper_to_canonical hS
  rw [← hvol]
  exact volume_le_constant hs

/-- Exact maximality transfer; all paper competitors are compared after an
actual placement, not after an assumption of zero initial translation. -/
theorem maximizer_iff_paper_maximal {s : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    IsMaximizer s ↔
      ∀ T : Set CoordinatePlane, MovingSofaOptimality.IsMovingSofa T →
        volume T ≤ volume (coordinates '' s) := by
  constructor
  · rintro ⟨_, hmax⟩ T hT
    rw [volume_coordinates_image, hmax]
    exact paper_volume_le_constant hT
  · intro hmax
    refine ⟨hs, le_antisymm (volume_le_constant hs) ?_⟩
    unfold MovingSofa.sofaConstant
    refine iSup_le fun t => iSup_le fun ht => ?_
    have h := hmax (coordinates '' t) (canonical_to_paper ht)
    simpa only [volume_coordinates_image] using h

/-- Volume attainment is equivalent to global maximality within the canonical
motion model; the supremum is not treated as an attained maximum by definition. -/
theorem maximizer_iff_global {s : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    IsMaximizer s ↔
      ∀ t : Set Point, (∃ m, MovingSofa.IsMovingSofa t m) → volume t ≤ volume s := by
  constructor
  · rintro ⟨_, hmax⟩ t ht
    rw [hmax]
    exact volume_le_constant ht
  · intro hmax
    refine ⟨hs, le_antisymm (volume_le_constant hs) ?_⟩
    unfold MovingSofa.sofaConstant
    exact iSup_le fun t => iSup_le fun ht => hmax t ht

end MovingSofa.Canonical
