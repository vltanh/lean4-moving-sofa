module

public import MovingSofaStability.CutSeparation

/-!
# Wedges and tail areas under the weaker cut-separation hypothesis

These are the geometric parts of source Lemmas 8.1.6 and 8.2.2. Their actual
hypotheses are separated cut corners, canonical endpoint contacts, and finite
niche area; no global injectivity is required.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Inside the right cut half-plane only one of the two wedge inequalities remains. -/
theorem separated_right_wedge {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t : ℝ} (ht : t ∈ Ioc φ (π / 2)) :
    hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t ∧
      hRight φ K ∩ wedge K (π / 2) t = (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K t := by
  have hlt := hsep.1 t ht
  have hpi := pi_pos
  have h2 : hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t := by
    ext p
    simp only [hRight, halfB, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    constructor
    · rintro ⟨hp, h1, -⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, h1, ?_⟩
      by_contra hcon
      push Not at hcon
      have e1 := dot_uvec_eq_cos_add_sin p φ t
      have e2 := dot_uvec_eq_cos_add_sin (innerCorner K t) φ t
      rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
      have hc : 0 ≤ cos (φ - t) :=
        (cos_pos_of_mem_Ioo ⟨by linarith [ht.2, hφ.1], by linarith [ht.1]⟩).le
      have hs : sin (φ - t) ≤ 0 :=
        (sin_neg_of_neg_of_neg_pi_lt (by linarith [ht.1]) (by linarith [ht.2, hφ.1])).le
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hc
          (by linarith : dot p (uvec t) - (supp K t - 1) ≤ 0),
        mul_nonpos_of_nonpos_of_nonneg hs
          (by linarith : 0 ≤ dot p (vvec t) - (supp K (t + π / 2) - 1))]
  refine ⟨h2, ?_⟩
  ext p
  have he := Set.ext_iff.mp h2 p
  simp only [wedge, fan, mem_inter_iff, mem_sdiff] at he ⊢
  tauto

/-- The corresponding reduction in the left cut half-plane. -/
theorem separated_left_wedge {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t : ℝ} (ht : t ∈ Ico 0 (π / 2 - φ)) :
    hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t ∧
      hLeft φ K ∩ wedge K (π / 2) t = (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K t := by
  have hlt := hsep.2 t ht
  have hpi := pi_pos
  have h2 : hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t := by
    ext p
    simp only [hLeft, halfD, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    constructor
    · rintro ⟨hp, -, h1⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, ?_, h1⟩
      by_contra hcon
      push Not at hcon
      have e1 := opt_dot_frame_v p (π / 2 - φ) t
      have e2 := opt_dot_frame_v (innerCorner K t) (π / 2 - φ) t
      rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
      have hc : 0 < cos (π / 2 - φ - t) :=
        cos_pos_of_mem_Ioo ⟨by linarith [ht.2], by linarith [ht.1, hφ.1]⟩
      have hs : 0 ≤ sin (π / 2 - φ - t) :=
        (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1, hφ.1])).le
      nlinarith [mul_nonneg hs (by linarith : 0 ≤ dot p (uvec t) - (supp K t - 1)),
        mul_neg_of_pos_of_neg hc
          (by linarith : dot p (vvec t) - (supp K (t + π / 2) - 1) < 0)]
  refine ⟨h2, ?_⟩
  ext p
  have he := Set.ext_iff.mp h2 p
  simp only [wedge, fan, mem_inter_iff, mem_sdiff] at he ⊢
  tauto

/-- The tail-area inequality with the precise weaker hypotheses needed locally. -/
theorem separated_tail_areas {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (htriple : InWideL φ K (rightBody φ K) (leftBody φ K)) (hsep : CutSeparated φ K) :
    segArea (xB φ (rightBody φ K)) (wRight φ K) -
        convexCurveArea (rightBody φ K) (π + φ) (3 * π / 2) ≤
      area (niche K (π / 2) ∩ hRight φ K) ∧
    segArea (zLeft φ K) (yD φ (leftBody φ K)) -
        convexCurveArea (leftBody φ K) (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) ≤
      area (niche K (π / 2) ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, -, -, -⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp htriple
  have hBcb := htriple.2.1
  have hDcb := htriple.2.2.1
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  have hfin : ∀ A ⊆ niche K (π / 2), volume A ≠ ⊤ := fun A hA =>
    ne_top_of_le_ne_top (nef_niche_isBounded hK).measure_lt_top.ne (measure_mono hA)
  constructor
  · have hvint := opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
    have hsub : ∀ p ∈ K, p ∉ rightBody φ K →
        p ∈ suppHalf (rightBody φ K) (π + φ) ∩ suppHalf (rightBody φ K) (3 * π / 2) →
        p ∈ niche K (π / 2) ∩ hRight φ K := by
      intro p hpK hpB ⟨hpR', hp2⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hBa] at hpR'
      rw [show π + φ = φ + π by ring, dot_uvec_add_pi] at hpR'
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hB3, dot_uvec_three_pi_div_two] at hp2
      have hpR : p ∈ hRight φ K := by
        simp only [hRight, halfB, halfPlus, mem_ofPred_eq]; linarith
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc φ (π / 2), p ∉ halfB K s := by
        by_contra hcon
        push Not at hcon
        exact hpB ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hsφ : φ < s := lt_of_le_of_ne hs.1 (by rintro rfl; exact hps hpR)
      have hsv : s < π / 2 := lt_of_le_of_ne hs.2 (by
        rintro rfl
        apply hps
        simp only [halfB, halfPlus, mem_ofPred_eq, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hpw : p ∈ wedge K (π / 2) s := by
        have he : p ∈ (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K s := by
          refine ⟨⟨hpR, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (separated_right_wedge hφ' hsep ⟨hsφ, hsv.le⟩).2] at he
        exact he.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨by linarith, hsv⟩, hpw.2⟩⟩, hpR⟩
    have he := opt_tail_area_le hBcb (by linarith) (by linarith) inter_subset_left hK.2.1.2.2
      (by rw [hvint]; exact hW.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero rfl (opt_snd_vminus_three_pi_div_two hB3), add_zero] at he
  · have hvint := opt_vint_left_eq hD3 hDb
    have hsub : ∀ p ∈ K, p ∉ leftBody φ K →
        p ∈ suppHalf (leftBody φ K) (3 * π / 2) ∩
          suppHalf (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) →
        p ∈ niche K (π / 2) ∩ hLeft φ K := by
      intro p hpK hpD ⟨hp2, hpL'⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hD3, dot_uvec_three_pi_div_two] at hp2
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hDb] at hpL'
      rw [show 3 * π / 2 + (π / 2 - φ) = (π - φ) + π by ring, dot_uvec_add_pi] at hpL'
      have hpL : p ∈ hLeft φ K := by
        simp only [hLeft, halfD, halfPlus, mem_ofPred_eq,
          show π / 2 - φ + π / 2 = π - φ by ring]
        linarith
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc 0 (π / 2 - φ), p ∉ halfD K s := by
        by_contra hcon
        push Not at hcon
        exact hpD ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by
        rintro rfl
        apply hps
        simp only [halfD, halfPlus, mem_ofPred_eq, zero_add, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hsψ : s < π / 2 - φ := lt_of_le_of_ne hs.2 (by rintro rfl; exact hps hpL)
      have hpw : p ∈ wedge K (π / 2) s := by
        have he : p ∈ (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K s := by
          refine ⟨⟨hpL, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (separated_left_wedge hφ' hsep ⟨hs0.le, hsψ⟩).2] at he
        exact he.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨hs0, by linarith⟩, hpw.2⟩⟩, hpL⟩
    have he := opt_tail_area_le hDcb (by linarith) (by linarith) inter_subset_left hK.2.1.2.2
      (by rw [hvint]; exact hZ.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3)
      (by rw [opt_zLeft_eq]), zero_add] at he

end MovingSofaStability
