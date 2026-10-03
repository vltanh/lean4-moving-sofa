module

public import MovingSofaUniquenessFC.Extremal
public import MovingSofaUniqueness.Main

/-!
# One Euclidean uniqueness API for the paper and upstream motion model

The canonical definitions come from `SofaSubmission.Model`, which imports only
Mathlib. The actual paper modules are imported directly in their pair-coordinate
presentation, with explicit `MovingSofa.Paper` kernel names for the colliding
hallway and moving-sofa predicates. No source relocation or generation is used.

The generic reference set G needs its actual moving-sofa and optimality facts.
They are explicit inputs, not postulated global instances. For the exact
upstream reference, `SofaSubmission.ReferenceFacts` now derives those facts
from the independent concrete parameter/path/set correspondence. `Final`
instantiates this API with that literal reference. The generic theorem alone
must not be confused with having supplied the concrete-reference facts.

All scripts remain uncompiled: successful elaboration, an admission-free
elaborated dependency graph, and Palomar acceptance have not been established.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open MovingSofaUniquenessFC.Bridge
open scoped EuclideanGeometry

namespace MovingSofa.Canonical

/-- Transfer maximality of this specified canonical sofa to the paper model. -/
theorem IsMaximizer.paper {s : Set Point} (hs : IsMaximizer s) :
    MovingSofaUniqueness.IsGlobalMax (coordinates '' s) := by
  refine ⟨canonical_to_paper hs.1, ?_⟩
  exact (maximizer_iff_paper_maximal hs.1).mp hs

/-- Every two canonical maximizers are congruent as actual sets.
The isometry uses the Euclidean norm, not the ordinary product norm. -/
theorem IsMaximizer.congruent {s t : Set Point}
    (hs : IsMaximizer s) (ht : IsMaximizer t) :
    ∃ g : Point ≃ᵃⁱ[ℝ] Point, s = g '' t := by
  obtain ⟨g, hg⟩ := MovingSofaUniqueness.globalMax_congruent hs.paper ht.paper
  exact ⟨realizeRigid g, congruent_of_coordinates g hg⟩

/-- Any specified optimal reference shape characterizes all maximizers.
The two reference premises concern that shape's motion and area; they are
not uniqueness, regularity, or rigidity assumptions on the competitor. -/
theorem volume_eq_constant_iff_congruent {s G : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m)
    (hG : ∃ m, MovingSofa.IsMovingSofa G m)
    (hGvolume : MovingSofa.sofaConstant = volume G) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : Point ≃ᵃⁱ[ℝ] Point, s = g '' G := by
  constructor
  · intro hvol
    exact IsMaximizer.congruent ⟨hs, hvol⟩ ⟨hG, hGvolume.symm⟩
  · intro hcongruent
    exact (MovingSofaUniquenessFC.volume_eq_of_congruent hcongruent).trans hGvolume.symm

/-- Congruence of reference maximizers does not depend on a choice of valid
Gerver parameters in the pair-coordinate development. -/
theorem optimal_reference_independent {G H : Set Point}
    (hG : IsMaximizer G) (hH : IsMaximizer H) :
    ∀ s : Set Point,
      (∃ g : Point ≃ᵃⁱ[ℝ] Point, s = g '' G) ↔
        ∃ g : Point ≃ᵃⁱ[ℝ] Point, s = g '' H := by
  obtain ⟨e, hGH⟩ := hG.congruent hH
  intro s
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨e.trans g, ?_⟩
    rw [hGH, Set.image_image]
    rfl
  · rintro ⟨g, rfl⟩
    have hHG : H = e.symm '' G :=
      MovingSofaUniquenessFC.eq_image_symm_of_image_eq e hGH.symm
    refine ⟨e.symm.trans g, ?_⟩
    rw [hHG, Set.image_image]
    rfl

end MovingSofa.Canonical
