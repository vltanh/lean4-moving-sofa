module

public import MovingSofaUniquenessFC.Uniqueness
public import MovingSofaUniquenessFC.ReferenceFacts

/-!
# Shared and exact-reference moving-sofa uniqueness endpoints

The same core proof supplies the reference-independent publication theorem,
the corollary for the paper's Gerver construction, and the EXACT upstream
`volume_eq_sofaConstant_iff_congruent_gerversSofa` declaration.

The concrete-reference dependencies are now local ordinary Lean modules:
`ReferenceDefs` proves the full four-constant specification analytically;
`Bridge/ReferenceShape` proves equality with the paper Gerver set in
coordinates; `ReferenceFacts` derives the actual motion and optimal volume.
No Challenge placeholder or rejected decision-kernel certificate is imported.
The parameter/path correspondence does not depend on shape uniqueness.

All source remains uncompiled. Explicit proof bodies are not a report of
successful elaboration, a dependency audit, Comparator success, independent
kernel verification, or Palomar acceptance. No such execution was performed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open MovingSofaUniquenessFC.Bridge
open scoped Real unitInterval EuclideanGeometry

namespace MovingSofa.Canonical

/-- Any two canonical sofas attaining the supremum are congruent as actual sets. -/
theorem maximizers_congruent (s t : Set ℝ²)
    (hs : ∃ m, MovingSofa.IsMovingSofa s m)
    (ht : ∃ m, MovingSofa.IsMovingSofa t m)
    (hsvol : volume s = MovingSofa.sofaConstant)
    (htvol : volume t = MovingSofa.sofaConstant) :
    ∃ g : E(2), s = g '' t := by
  exact IsMaximizer.congruent ⟨hs, hsvol⟩ ⟨ht, htvol⟩

/-- The publication's explicit pair-coordinate Gerver witness, without an
assumption that it has already been placed in the horizontal hallway. -/
theorem volume_eq_constant_iff_congruent_paper_gerver {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (s : Set ℝ²)
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : E(2), s = g '' (point '' MovingSofaOptimality.gerverSofa P) := by
  constructor
  · intro hvolume
    have hpaper := canonical_to_paper hs
    have heq : volume (coordinates '' s) = volume (MovingSofaOptimality.gerverSofa P) := by
      rw [volume_coordinates_image, hvolume, constant_eq_paper_gerver hP hbox]
    obtain ⟨g, hg⟩ := MovingSofaUniqueness.image_eq_gerver_of_volume_eq
      hP hbox hpaper heq
    have hcoordinates : coordinates '' s = g.symm '' (coordinates ''
        (point '' MovingSofaOptimality.gerverSofa P)) := by
      rw [coordinates_point_image, ← hg,
        MovingSofaUniqueness.Rigid.symm_image_image]
    exact ⟨realizeRigid g.symm, congruent_of_coordinates g.symm hcoordinates⟩
  · intro hcongruent
    have hv := MovingSofaUniquenessFC.volume_eq_of_congruent hcongruent
    rw [volume_point_image] at hv
    exact hv.trans (constant_eq_paper_gerver hP hbox).symm

/-- Existence is proved rather than inferred from the definition of a supremum. -/
theorem exists_unique_maximizer_modulo_isometry :
    ∃ G : Set ℝ², IsMaximizer G ∧
      ∀ s : Set ℝ², (∃ m, MovingSofa.IsMovingSofa s m) →
        (volume s = MovingSofa.sofaConstant ↔ ∃ g : E(2), s = g '' G) := by
  obtain ⟨G, hG⟩ := exists_maximizer
  exact ⟨G, hG, fun s hs => volume_eq_constant_iff_congruent hs hG.1 hG.2.symm⟩

end MovingSofa.Canonical

namespace MovingSofa

/-- The exact formal-conjectures statement, for its actual integral-defined
Gerver reference. No extra hypotheses on the competing sofa are added. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  exact Canonical.volume_eq_constant_iff_congruent hs
    isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa

end MovingSofa
