module

public import SofaSubmission.Uniqueness

/-!
# Shared uniqueness theorem and the concrete paper Gerver witness

These declarations use the exact identity-start Euclidean motion model and
the local paper proof. They import neither an upstream statement placeholder
nor a reference proof using a prohibited decision tactic.

`maximizers_congruent` is the unconditional unique-maximizer assertion, with
both competitors stated explicitly. The second theorem identifies an arbitrary
canonical maximizer with the actual pair-coordinate Gerver formula of the paper.
It does not redefine Gerver's sofa as an arbitrary chosen maximizer.

IMPORTANT: these are not the exact upstream declaration naming its different
concrete `MovingSofa.gerversSofa`. The prototype of that specialization was
withdrawn after auditing its proposed reference dependency and finding
`decide +kernel`. See docs/uniqueness/21-reference-dependency-audit.md.
The reference-formula integration remains unfinished under the requested
source restrictions; it is not concealed as an extra theorem hypothesis.

All proof scripts are uncompiled. Comparator and independent kernel checking
have not been executed. No acceptance or successful elaboration is claimed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open SofaUniqueness.Bridge
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

/-- Identify a canonical maximizer with the concrete Gerver witness of the
paper, without assuming that witness is already in the horizontal hallway. -/
theorem volume_eq_constant_iff_congruent_paper_gerver {P : MovingSofa.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (s : Set ℝ²)
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : E(2), s = g '' (point '' MovingSofa.gerverSofa P) := by
  constructor
  · intro hvolume
    have hpaper := canonical_to_paper hs
    have heq : volume (coordinates '' s) = volume (MovingSofa.gerverSofa P) := by
      rw [volume_coordinates_image, hvolume, constant_eq_paper_gerver hP hbox]
    obtain ⟨g, hg⟩ := SofaUniqueness.Draft.image_eq_gerver_of_volume_eq
      hP hbox hpaper heq
    have hcoordinates : coordinates '' s = g.symm '' (coordinates ''
        (point '' MovingSofa.gerverSofa P)) := by
      rw [coordinates_point_image, ← hg,
        SofaUniqueness.Draft.Rigid.symm_image_image]
    exact ⟨realizeRigid g.symm, congruent_of_coordinates g.symm hcoordinates⟩
  · intro hcongruent
    have hv := SofaUniqueness.volume_eq_of_congruent hcongruent
    rw [volume_point_image] at hv
    exact hv.trans (constant_eq_paper_gerver hP hbox).symm

/-- The canonical problem has a maximizing shape, and every maximizer is
congruent to it. Existence is proved rather than assumed from the supremum. -/
theorem exists_unique_maximizer_modulo_isometry :
    ∃ G : Set ℝ², IsMaximizer G ∧
      ∀ s : Set ℝ², (∃ m, MovingSofa.IsMovingSofa s m) →
        (volume s = MovingSofa.sofaConstant ↔ ∃ g : E(2), s = g '' G) := by
  obtain ⟨G, hG⟩ := exists_maximizer
  exact ⟨G, hG, fun s hs => volume_eq_constant_iff_congruent hs hG.1 hG.2.symm⟩

end MovingSofa.Canonical
