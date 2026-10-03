module

public import SofaSubmission.Extremal
public import SofaUniqueness.Draft.ShapeUniqueness

/-!
# One Euclidean uniqueness API for the paper and upstream statement

The canonical definitions come from `SofaSubmission.Model`. The actual paper
modules and their coordinate presentation are imported directly. This is an
ordinary Lean source module, not an insertion fragment or generated overlay.

The generic reference set G needs only its actual moving-sofa and optimality
facts. It need not be identified definitionally with the paper's Romik formula.
For the formal-conjectures reference, the final call is

  volume_eq_constant_iff_congruent hs isMovingSofa_gerversSofa
    sofaConstant_eq_volume_gerversSofa

with exactly the original target statement. Those upstream facts are NOT
postulated here or imported from a file containing placeholders.

Status: uncompiled and dependent on the two variational admissions P2 and P4
in `PaperReductions`. An admission-free body is not an admission-free proof
closure. This file must not be advertised as a verified solution.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open SofaUniqueness.Bridge
open scoped EuclideanGeometry

namespace MovingSofa.Canonical

/-- Transfer maximality of this specified canonical sofa to the paper model. -/
theorem IsMaximizer.paper {s : Set Point} (hs : IsMaximizer s) :
    SofaUniqueness.Draft.IsGlobalMax (coordinates '' s) := by
  refine ⟨canonical_to_paper hs.1, ?_⟩
  exact (maximizer_iff_paper_maximal hs.1).mp hs

/-- Every two canonical maximizers are congruent as actual sets.
The isometry has the Euclidean norm, not the ordinary product norm. -/
theorem IsMaximizer.congruent {s t : Set Point}
    (hs : IsMaximizer s) (ht : IsMaximizer t) :
    ∃ g : Point ≃ᵃⁱ[ℝ] Point, s = g '' t := by
  obtain ⟨g, hg⟩ := SofaUniqueness.Draft.globalMax_congruent hs.paper ht.paper
  exact ⟨realizeRigid g, congruent_of_coordinates g hg⟩

/-- Target-shaped theorem for any specified optimal reference sofa.
The two reference hypotheses are ordinary solved-result facts, not uniqueness
or shape-rigidity hypotheses. They are deliberately explicit. -/
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
    exact (SofaUniqueness.volume_eq_of_congruent hcongruent).trans hGvolume.symm

/-- Congruence of reference maximizers is independent of an arbitrary choice
of Gerver parameters in the pair-coordinate development. -/
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
      SofaUniqueness.eq_image_symm_of_image_eq e hGH.symm
    refine ⟨e.symm.trans g, ?_⟩
    rw [hHG, Set.image_image]
    rfl

end MovingSofa.Canonical
