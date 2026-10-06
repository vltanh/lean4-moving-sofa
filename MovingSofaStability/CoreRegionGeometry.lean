module

public import MovingSofaStability.SeparatedWedges

/-!
# Positive local core regions

Uncompiled proof source. Gerver's core lies strictly above the floor. This
persists in a fixed support neighborhood and lets the local upper bound use
three positive-area regions, rather than subtract an auxiliary trapezoid.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Core height stays uniformly positive in a neighborhood of Gerver's cap. -/
theorem nearby_core_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      UpperSupportClose δ K P.cap → ∀ t ∈ Icc P.φ (π / 2 - P.φ),
        0 < (innerCorner K t).2 := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  have hφ := gm_φ_mem_Ioo hP hbox
  have hc : Continuous (fun t => (innerCorner P.cap t).2) :=
    (opt_innerCorner_continuous (gm_isConvexBody_cap hP hbox)).snd
  have hp : ∀ t ∈ Icc P.φ (π / 2 - P.φ), 0 < (innerCorner P.cap t).2 := by
    intro t ht
    have htv : t ∈ Icc (0 : ℝ) (π / 2) :=
      ⟨hφ.1.le.trans ht.1, by linarith [ht.2, hφ.1]⟩
    rw [((theorem8_4_1_monotone hP hbox).2 t htv).2.2]
    exact henv.x_pos t ht
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le' hc.continuousOn hp
  let δ := min 1 (m / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδm : δ ≤ m / 4 := min_le_right _ _
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro K hclose t ht
  have htv : t ∈ Icc (0 : ℝ) (π / 2) :=
    ⟨hφ.1.le.trans ht.1, by linarith [ht.2, hφ.1]⟩
  have hd := (abs_snd_le_norm2 (innerCorner K t - innerCorner P.cap t)).trans
    (innerCorner_support_error hclose htv)
  have hlo := (abs_le.mp hd).1
  have href := hmin t ht
  dsimp only [Prod.snd_sub] at hlo
  linarith

/-- Every point strictly below an interior core point belongs to its forbidden
quadrant and lies outside both cuts. -/
theorem separated_core_below {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t s : ℝ}
    (ht : t ∈ Ioo φ (π / 2 - φ)) (hs : 0 < s) :
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hRight φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hLeft φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∈ qMinus K t := by
  have hpi := pi_pos
  have ht' : t ∈ Ioo 0 (π / 2) :=
    ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1]⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht'.1 (by linarith [ht'.2])
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht'.1], ht'.2⟩
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have e1 := hsep.1 t ⟨ht.1, ht'.2.le⟩
  have e2 := hsep.2 t ⟨ht'.1.le, ht.2⟩
  have e3 := (cn_innerCorner_dot K t).1
  have e4 := opt_innerCorner_dot_v K t
  simp only [dot, uvec, vvec] at e1 e2 e3 e4
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at e2
  refine ⟨?_, ?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos hs hs0]
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two,
      dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos hs hs0]
  · rw [proposition2_2_2_qMinus]
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, dot, uvec, cos_add_pi_div_two,
      sin_add_pi_div_two]
    constructor <;> nlinarith [mul_pos hs hst, mul_pos hs hct]

/-- The small right triangular region is inside a cut-endpoint wedge. -/
theorem separated_right_triangle {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {p : Point}
    (h1 : (innerCorner K φ).1 < p.1) (h2 : p.2 < (innerCorner K φ).2)
    (h3 : p ∉ hRight φ K) : p ∉ hLeft φ K ∧ p ∈ qMinus K φ := by
  have hpi := pi_pos
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e2 := hsep.2 φ ⟨hφ.1.le, by linarith [hφ.2]⟩
  have e4 := opt_innerCorner_dot_v K φ
  simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e2 e4
  refine ⟨?_, ?_⟩
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two,
      dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hc, mul_pos (sub_pos.mpr h2) hs]
  · rw [proposition2_2_2_qMinus]
    simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two]
    refine ⟨h3, ?_⟩
    simp only [dot, vvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hs, mul_pos (sub_pos.mpr h2) hc]

/-- The matching left triangular region. -/
theorem separated_left_triangle {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {p : Point}
    (h1 : p.1 < (innerCorner K (π / 2 - φ)).1)
    (h2 : p.2 < (innerCorner K (π / 2 - φ)).2)
    (h3 : p ∉ hLeft φ K) : p ∉ hRight φ K ∧ p ∈ qMinus K (π / 2 - φ) := by
  have hpi := pi_pos
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e1 := hsep.1 (π / 2 - φ) ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  have e3 := (cn_innerCorner_dot K (π / 2 - φ)).1
  simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e1 e3
  refine ⟨?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hc, mul_pos (sub_pos.mpr h2) hs]
  · rw [proposition2_2_2_qMinus]
    simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq]
    refine ⟨?_, h3⟩
    simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hs, mul_pos (sub_pos.mpr h2) hc]

/-- Integration by parts expressed only through the right velocity. -/
theorem core_curveArea_rightVelocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    curveArea (innerCorner K) a b =
      ((innerCorner K b).1 * (innerCorner K b).2 - (innerCorner K a).1 * (innerCorner K a).2) / 2 +
      ∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2 := by
  obtain ⟨hi1, hi2⟩ := corner_coordinate_velocity_integrable hK a b
  have hprod := corner_coordinate_product_integral hK hab
  rw [corner_curveArea_integral hK hab]
  have hcross : (fun t => cross (innerCorner K t) (cornerRightVelocity K t)) =
      fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2 -
        (innerCorner K t).2 * (cornerRightVelocity K t).1 := rfl
  have hneg : (∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2) =
      -(∫ t in a..b, (innerCorner K t).2 * (cornerRightVelocity K t).1) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hcross, intervalIntegral.integral_sub hi1 hi2, hneg]
  linarith

end MovingSofaStability
