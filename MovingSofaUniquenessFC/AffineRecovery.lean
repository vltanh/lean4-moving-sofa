module

public import MovingSofaUniqueness.SetRecovery
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Group.Action

/-!
# Exact recovery in the affine-isometry vocabulary

The formal-conjectures target uses `EuclideanSpace ℝ (Fin 2)` and affine
isometry equivalences. These lemmas use that same kind of isometry, and work in
any finite-dimensional real inner product space.

`volume_eq_iff_congruent_of_containment` is deliberately named as a reduction:
it does NOT establish its geometric containment hypothesis. In particular it
must not be reported as a proof of the moving-sofa uniqueness conjecture.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace MovingSofaUniquenessFC

open MovingSofaUniqueness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Decompose an affine isometry into its linear isometry and a translation. -/
theorem affineIsometry_apply_eq (e : E ≃ᵃⁱ[ℝ] E) (x : E) :
    e x = e.linearIsometryEquiv x + e 0 := by
  simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : E) x

/-- The canonical volume is preserved by every affine isometry, including
orientation-reversing ones. -/
theorem affineIsometry_measurePreserving (e : E ≃ᵃⁱ[ℝ] E) :
    MeasurePreserving e (volume : Measure E) volume := by
  have hp : MeasurePreserving (fun x : E => e.linearIsometryEquiv x + e 0)
      (volume : Measure E) volume :=
    (measurePreserving_add_right (volume : Measure E) (e 0)).comp
      e.linearIsometryEquiv.measurePreserving
  have he : (fun x : E => e.linearIsometryEquiv x + e 0) = e := by
    funext x
    exact (affineIsometry_apply_eq e x).symm
  rwa [he] at hp

/-- This image-volume identity is valid even for nonmeasurable sets: the
measurable equivalence allows the embedding version of the preimage formula. -/
theorem volume_image_affineIsometry (e : E ≃ᵃⁱ[ℝ] E) (s : Set E) :
    volume (e '' s) = volume s := by
  have h := (affineIsometry_measurePreserving e).measure_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (e '' s)
  rw [Set.preimage_image_eq s e.injective] at h
  exact h.symm

/-- Affine isometries preserve closedness. -/
theorem isClosed_image_affineIsometry (e : E ≃ᵃⁱ[ℝ] E) {s : Set E}
    (hs : IsClosed s) : IsClosed (e '' s) := by
  have himage : e '' s = e.symm ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, e.symm_apply_apply] using hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  rw [himage]
  exact hs.preimage e.symm.continuous

/-- Reverse the direction of the isometry in an equality of sets.

The paper produces `e '' s = G`; the target requests `s = e.symm '' G`. -/
theorem eq_image_symm_of_image_eq (e : E ≃ᵃⁱ[ℝ] E) {s G : Set E}
    (heq : e '' s = G) : s = e.symm '' G := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [← heq] at hy
    rcases hy with ⟨z, hz, rfl⟩
    simpa only [e.symm_apply_apply] using hz

/-- A closed set contained, after isometry, in a regular-closed set of the same
finite volume is exactly an isometric copy of that set. -/
theorem eq_image_symm_of_containment (e : E ≃ᵃⁱ[ℝ] E) {s G : Set E}
    (hs : IsClosed s) (hG : closure (interior G) = G) (hGfin : volume G ≠ ⊤)
    (hsub : e '' s ⊆ G) (hvol : volume s = volume G) : s = e.symm '' G := by
  apply eq_image_symm_of_image_eq e
  apply eq_of_subset_of_measure_eq (μ := volume)
    (isClosed_image_affineIsometry e hs) hsub hG hGfin
  rw [volume_image_affineIsometry]
  exact hvol

/-- The reverse direction of the formal-conjectures target, apart from
identifying the sofa constant with the reference sofa's volume. -/
theorem volume_eq_of_congruent {s G : Set E}
    (h : ∃ e : E ≃ᵃⁱ[ℝ] E, s = e '' G) : volume s = volume G := by
  obtain ⟨e, rfl⟩ := h
  exact volume_image_affineIsometry e G

/-- The exact final glue for the target statement. Its remaining geometric
input is containment of a maximizer in the reference shape after isometry.

This lemma has explicit hypotheses rather than introducing a uniqueness axiom,
a typeclass with an unproved instance, or a theorem with the target's name. -/
theorem volume_eq_iff_congruent_of_containment {s G : Set E} {c : ℝ≥0∞}
    (hs : IsClosed s) (hG : closure (interior G) = G) (hGfin : volume G ≠ ⊤)
    (hc : c = volume G)
    (hcontain : volume s = c → ∃ e : E ≃ᵃⁱ[ℝ] E, e '' s ⊆ G) :
    volume s = c ↔ ∃ e : E ≃ᵃⁱ[ℝ] E, s = e '' G := by
  constructor
  · intro hvol
    obtain ⟨e, he⟩ := hcontain hvol
    exact ⟨e.symm, eq_image_symm_of_containment e hs hG hGfin he (hvol.trans hc)⟩
  · intro hcongruent
    exact (volume_eq_of_congruent hcongruent).trans hc.symm

end MovingSofaUniquenessFC
