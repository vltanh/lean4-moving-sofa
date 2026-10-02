module

public import SofaUniqueness.Draft.Rigid

/-!
# UNCOMPILED DRAFT: recover caps and their niches as actual sets

These are geometric consequences of a support identity, not consequences of
area equality alone. In particular, no regular-closedness assumption on an
arbitrary competing sofa is introduced.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofa

namespace SofaUniqueness.Draft

/-- A right-angle cap is determined by its upper supports and the floor. -/
theorem mem_right_cap_iff {K : Set Plane} (hK : IsCap K (π / 2)) (p : Plane) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨(opt_cap_mem_strip hK hp).1,
      fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩
  · rintro ⟨hfloor, hupper⟩
    obtain ⟨hω, hbody, hωtop, htop, hωfloor, hbottom, hplanes⟩ := hK
    rw [nef_eq_setOf_supp hbody hplanes]
    intro t ht
    simp only [jSet, mem_union, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with (ht | ht) | ht | ht
    · exact hupper t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
    · exact hupper t ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    · have he : t = 3 * π / 2 := by linarith
      rw [he, hbottom, opt_uvec_three_pi_div_two]
      simpa [dot] using hfloor
    · rw [ht, hbottom, opt_uvec_three_pi_div_two]
      simpa [dot] using hfloor

/-- In a right-angle cap, the fan is the upper half-plane. The quadrant
inequalities remain strict; they have not been replaced by their closures. -/
theorem mem_right_niche_iff (K : Set Plane) (p : Plane) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2),
      dot p (uvec t) < supp K t - 1 ∧
      dot p (vvec t) < supp K (t + π / 2) - 1 := by
  have hf : p ∈ fan (π / 2) ↔ 0 ≤ p.2 := by
    simp [fan, halfPlus, opt_uvec_pi_div_two, dot]
  change (p ∈ fan (π / 2) ∧ p ∈ ⋃ t ∈ Ioo (0 : ℝ) (π / 2), qMinus K t) ↔ _
  rw [hf]
  simp only [mem_iUnion, exists_prop, ms_mem_qMinus_iff]

private theorem dot_sub_horizontal_u (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (uvec t) = dot p (uvec t) - a * cos t := by
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

private theorem dot_sub_horizontal_v (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (vvec t) = dot p (vvec t) + a * sin t := by
  simp only [dot, vvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

/-- The upper-support translation mode gives an exact membership equivalence. -/
theorem mem_cap_sub_horizontal_iff {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ K ↔ p - (a, 0) ∈ G := by
  rw [mem_right_cap_iff hK, mem_right_cap_iff hG]
  simp only [Prod.snd_sub, Prod.snd_mk, sub_zero]
  constructor
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    rw [dot_sub_horizontal_u]
    linarith [hu t ht, hsupp t ht]
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    have hi := hu t ht
    rw [dot_sub_horizontal_u] at hi
    linarith [hsupp t ht]

/-- No assumption that either cap contains its niche is needed for covariance. -/
theorem mem_niche_sub_horizontal_iff {K G : Set Plane} (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ niche K (π / 2) ↔ p - (a, 0) ∈ niche G (π / 2) := by
  rw [mem_right_niche_iff, mem_right_niche_iff]
  simp only [Prod.snd_sub, Prod.snd_mk, sub_zero]
  have hbounds : ∀ t ∈ Ioo (0 : ℝ) (π / 2),
      supp K t - supp G t = a * cos t ∧
        supp K (t + π / 2) - supp G (t + π / 2) = -a * sin t := by
    intro t ht
    refine ⟨hsupp t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩, ?_⟩
    have h := hsupp (t + π / 2)
      ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
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
    exact ⟨hp, t, ht, by linarith [(hbounds t ht).1],
      by linarith [(hbounds t ht).2]⟩

theorem cap_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K = Rigid.translate (a, 0) '' G := by
  ext p
  constructor
  · intro hp
    refine ⟨p - (a, 0), (mem_cap_sub_horizontal_iff hK hG a hsupp p).mp hp, ?_⟩
    simp
  · rintro ⟨q, hq, rfl⟩
    apply (mem_cap_sub_horizontal_iff hK hG a hsupp _).mpr
    simpa using hq

theorem sofa_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K \ niche K (π / 2) = Rigid.translate (a, 0) '' (G \ niche G (π / 2)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p - (a, 0), ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp p).mp hp.1,
      fun hn => hp.2 ((mem_niche_sub_horizontal_iff a hsupp p).mpr hn)⟩, ?_⟩
    simp
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp _).mpr (by simpa using hq.1), ?_⟩
    intro hn
    have hqN := (mem_niche_sub_horizontal_iff a hsupp _).mp hn
    exact hq.2 (by simpa using hqN)

end SofaUniqueness.Draft
