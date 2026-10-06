module

public import MovingSofaUniqueness.Rigid

/-!
# Elementary horizontal translation for the coercive route

Uncompiled proof source. These are geometric identities, not rigidity theorems.
No equality-in-concavity, CapKernel, or old maximizer classification is imported.
The original versions remain in their existing module for compatibility.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

theorem mem_right_niche_iff (K : Set Plane) (p : Plane) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2),
      dot p (uvec t) < supp K t - 1 ∧ dot p (vvec t) < supp K (t + π / 2) - 1 := by
  have hf : p ∈ fan (π / 2) ↔ 0 ≤ p.2 := by
    simp [fan, halfPlus, uvec_pi_div_two, dot]
  change (p ∈ fan (π / 2) ∧ p ∈ ⋃ t ∈ Ioo (0 : ℝ) (π / 2), qMinus K t) ↔ _
  rw [hf]
  simp only [mem_iUnion, exists_prop, ms_mem_qMinus_iff]

theorem supp_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a t : ℝ) :
    supp (Rigid.translate (a, 0) '' G) t - supp G t = a * cos t := by
  rw [Rigid.coe_translate, supp_translate G _ t hG.2.1 hG.1]
  simp only [dot, uvec]
  ring

private theorem dot_sub_horizontal_u (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (uvec t) = dot p (uvec t) - a * cos t := by
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

private theorem dot_sub_horizontal_v (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (vvec t) = dot p (vvec t) + a * sin t := by
  simp only [dot, vvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

theorem mem_niche_sub_horizontal_iff {K G : Set Plane} (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ niche K (π / 2) ↔ p - (a, 0) ∈ niche G (π / 2) := by
  rw [mem_right_niche_iff, mem_right_niche_iff]
  simp only [Prod.snd_sub, sub_zero]
  have hbounds : ∀ t ∈ Ioo (0 : ℝ) (π / 2),
      supp K t - supp G t = a * cos t ∧
        supp K (t + π / 2) - supp G (t + π / 2) = -a * sin t := by
    intro t ht
    refine ⟨hsupp t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩, ?_⟩
    have h := hsupp (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    simpa [cos_add_pi_div_two, mul_neg, neg_mul] using h
  constructor
  · rintro ⟨hp, t, ht, hu, hv⟩
    refine ⟨hp, t, ht, ?_, ?_⟩
    · rw [dot_sub_horizontal_u]
      linarith [(hbounds t ht).1]
    · rw [dot_sub_horizontal_v]
      linarith [(hbounds t ht).2]
  · rintro ⟨hp, t, ht, hu, hv⟩
    rw [dot_sub_horizontal_u] at hu
    rw [dot_sub_horizontal_v] at hv
    exact ⟨hp, t, ht, by linarith [(hbounds t ht).1], by linarith [(hbounds t ht).2]⟩

theorem niche_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    niche (Rigid.translate (a, 0) '' G) (π / 2) = Rigid.translate (a, 0) '' niche G (π / 2) := by
  ext p
  rw [Rigid.mem_translate_image]
  exact mem_niche_sub_horizontal_iff a (fun t _ => supp_translate_horizontal hG a t) p

theorem cap_minus_niche_translate {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    (Rigid.translate (a, 0) '' G) \ niche (Rigid.translate (a, 0) '' G) (π / 2) =
      Rigid.translate (a, 0) '' (G \ niche G (π / 2)) := by
  rw [niche_translate_horizontal hG a]
  have hinj : Function.Injective (Rigid.translate (a, 0)) := by
    intro p q heq
    have h : p + (a, 0) = q + (a, 0) := by
      simpa only [Rigid.translate_apply] using heq
    exact add_right_cancel h
  exact (image_sdiff hinj _ _).symm

theorem sofaArea_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    sofaArea (π / 2) (Rigid.translate (a, 0) '' G) = sofaArea (π / 2) G := by
  unfold sofaArea
  rw [niche_translate_horizontal hG, Rigid.area_image, Rigid.area_image]

theorem isCap_translate_horizontal {G : Set Plane} (hG : IsCap G (π / 2)) (a : ℝ) :
    IsCap (Rigid.translate (a, 0) '' G) (π / 2) := by
  obtain ⟨hω, hbody, htop, htop', hfloor, hfloor', hplanes⟩ := hG
  have hs : ∀ t, cos t = 0 → supp (Rigid.translate (a, 0) '' G) t = supp G t := by
    intro t ht
    have h := supp_translate_horizontal hbody a t
    rwa [ht, mul_zero, sub_eq_zero] at h
  have hc₁ : cos (π / 2) = 0 := cos_pi_div_two
  have hc₂ : cos (π / 2 + π) = 0 := by rw [cos_add_pi, hc₁, neg_zero]
  have hc₃ : cos (3 * π / 2) = 0 := by rw [show 3 * π / 2 = π / 2 + π by ring, hc₂]
  refine ⟨hω, ?_, (hs _ hc₁).trans htop, (hs _ hc₁).trans htop', (hs _ hc₂).trans hfloor,
    (hs _ hc₃).trans hfloor', ?_⟩
  · rw [Rigid.coe_translate]
    exact nef_isConvexBody_translate hbody _
  · rw [Rigid.coe_translate]
    exact nef_isHalfPlaneInter_translate hplanes _

end MovingSofaExtremal
