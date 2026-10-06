module

public import MovingSofaStability.ExposedFaceStability

/-!
# Uniform arm margins near an injective reference

Uncompiled proof source. The reference cap is injective; a competitor need
only be a normalized cap. Both endpoints of every competing exposed face
satisfy the margin, so polygonal and other nonsmooth competitors are included.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem UpperSupportClose.mono {δ R : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) (hδ : δ ≤ R) : UpperSupportClose R K L :=
  fun t ht => (h t ht).trans hδ

theorem injective_face_eq_aK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K t) : p = aK K t := by
  have he := inj_vplus_eq_vminus_of_injCond1 hK.2.1 hI (Or.inl ht)
  rw [edge_eq_segment hK.2.1 t, he, segment_same] at hp
  exact mem_singleton_iff.mp hp

theorem injective_face_eq_cK {K : Set Point} (hK : IsCap K (π / 2)) (hI : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (π / 2)) {p : Point} (hp : p ∈ edge K (t + π / 2)) :
    p = cK K t := by
  sorry

/-- A margin for all contacts at all normals of a compact interior angular interval. -/
def CoreArmMargin (K : Set Point) (a b c : ℝ) : Prop :=
  (∀ t ∈ Icc a b, ∀ p ∈ edge K t,
      1 + c ≤ supp K (t + π / 2) - dot p (vvec t)) ∧
  (∀ t ∈ Icc a b, ∀ p ∈ edge K (t + π / 2),
      1 + c ≤ supp K t - dot p (uvec t))

/-- The needed regularity is on the reference, not on every cap in its neighborhood. -/
theorem core_arm_margin_near_reference {K₀ : Set Point} (h₀ : IsKi K₀)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π / 2) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        CoreArmMargin K a b c := by
  sorry

/-- One-sided arm values inherit the all-face margin. -/
theorem CoreArmMargin.oneSided {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (h : CoreArmMargin K a b c) {t : ℝ} (ht : t ∈ Icc a b) :
    1 + c ≤ fPlus K t ∧ 1 + c ≤ fMinus K t ∧
      1 + c ≤ gPlus K t ∧ 1 + c ≤ gMinus K t := by
  have h1 := h.1 t ht (vplus K t) (vplus_mem_edge hK.2.1 t)
  have h2 := h.1 t ht (vminus K t) (vminus_mem_edge hK.2.1 t)
  have h3 := h.2 t ht (vplus K (t + π / 2)) (vplus_mem_edge hK.2.1 _)
  have h4 := h.2 t ht (vminus K (t + π / 2)) (vminus_mem_edge hK.2.1 _)
  rw [← inj_fPlus_eq] at h1
  rw [← inj_fMinus_eq] at h2
  simp only [gPlus, gMinus, cPlus, cMinus, dot_sub_left, inj_dot_outerCorner_uvec]
  exact ⟨h1, h2, h3, h4⟩

end MovingSofaStability
