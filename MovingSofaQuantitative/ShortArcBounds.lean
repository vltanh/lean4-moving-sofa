module

public import MovingSofaQuantitative.ReferenceDensity

/-!
# Uniform bounds on the short active arcs

Uncompiled proof source. These deliberately coarse bounds suffice for the
64*Delta derivative-energy estimate. They come from the existing cap certificate
and elementary trigonometry on the actual parameter box, not from sampled
support functions.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

/-- Cosine is safely bounded away from zero on the B endpoint interval. -/
theorem short_cos_lower {t : ℝ} (ht : t ∈ Icc 0 (51 / 50)) : (1 / 2 : ℝ) ≤ cos t := by
  have hpoly := cosPoly6_le_cos (x := 51 / 50) (by norm_num)
  have hnum : (1 / 2 : ℝ) ≤ cosPoly6 (51 / 50) := by norm_num [cosPoly6]
  exact hnum.trans (hpoly.trans (cos_le_cos_of_nonneg_of_le_pi ht.1
    (by linarith [pi_gt_three] : (51 / 50 : ℝ) ≤ π) ht.2))

theorem short_tan_bounds {t : ℝ} (ht : t ∈ Icc 0 (51 / 50)) :
    0 ≤ tan t ∧ tan t ≤ 2 := by
  have hc := short_cos_lower ht
  have hs : 0 ≤ sin t := sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht.2, pi_gt_three]⟩
  rw [tan_eq_sin_div_cos]
  constructor
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < cos t)).2
    linarith [sin_le_one t]

/-- Both endpoint sampling intervals of length at most 1/8 stay in their
respective active arcs and away from every singular sine denominator. -/
theorem endpoint_short_arc_locations {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (criticalLeft P + 1 / 8 < π / 2 - P.φ) ∧
    (criticalLeft P + 1 / 8 < (51 / 50 : ℝ)) ∧
    (π / 2 < criticalRight P - 1 / 8) ∧
    (P.φ + P.θ < π / 3) ∧ P.φ < (1 / 8 : ℝ) := by
  have hp := hbox.1
  have ht := hbox.2
  unfold criticalLeft criticalRight
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith [pi_lt_d2, pi_gt_three]

/-- The reference angle has substantially more margin than is needed here. -/
theorem cos_phi_ge_five_sixths {P : GerverParams} (hbox : P.InBox) :
    (5 / 6 : ℝ) ≤ cos P.φ := by
  have hp := hbox.1
  nlinarith [one_sub_sq_div_two_le_cos (x := P.φ)]

theorem active_sine_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (π / 2) (criticalRight P)) :
    (1 / 2 : ℝ) ≤ sin t ∧ (1 / 2 : ℝ) ≤ sin (π - P.φ - t) := by
  have hp := hbox.1
  have hθ := hbox.2
  have hloc := endpoint_short_arc_locations hP hbox
  have hy : t - π / 2 ∈ Icc 0 (π / 3) := by
    unfold criticalRight at ht
    constructor <;> linarith [ht.1, ht.2, pi_gt_three]
  have hz : π / 2 - (π - P.φ - t) ∈ Icc 0 (π / 3) := by
    unfold criticalRight at ht
    constructor <;> linarith [ht.1, ht.2, hloc.2.2.2.1]
  have bound {y : ℝ} (hy : y ∈ Icc 0 (π / 3)) : (1 / 2 : ℝ) ≤ cos y := by
    rw [← cos_pi_div_three]
    exact cos_le_cos_of_nonneg_of_le_pi hy.1 (by linarith [pi_pos]) hy.2
  constructor
  · have h := bound hy
    rwa [cos_sub, cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one, zero_add] at h
  · have h := bound hz
    rwa [cos_pi_div_two_sub] at h

theorem active_cot_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t ∈ Icc (π / 2) (criticalRight P)) :
    |cos t / sin t| ≤ 2 ∧
      |cos (π - P.φ - t) / sin (π - P.φ - t)| ≤ 2 ∧
      1 / sin (π - P.φ - t) ≤ 2 := by
  obtain ⟨h1, h2⟩ := active_sine_bounds hP hbox ht
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by linarith : 0 < sin t)]
    apply (div_le_iff₀ (by linarith : 0 < sin t)).2
    linarith [abs_cos_le_one t]
  · rw [abs_div, abs_of_pos (by linarith : 0 < sin (π - P.φ - t))]
    apply (div_le_iff₀ (by linarith : 0 < sin (π - P.φ - t))).2
    linarith [abs_cos_le_one (π - P.φ - t)]
  · apply (div_le_iff₀ (by linarith : 0 < sin (π - P.φ - t))).2
    linarith

/-- Every energy component and the dual slack are bounded by the actual Q deficit. -/
theorem q_energy_component_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    0 ≤ qDeficit P x ∧ 0 ≤ wideDualSlack hP hbox x ∧
    wideDualSlack hP hbox x ≤ qDeficit P x ∧
    capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 +
      rightResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1 ≤ qDeficit P x ∧
    capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 +
      leftResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2 ≤ qDeficit P x := by
  have hid := wide_deficit_eq_slack_add_integrals hP hbox x
  have hL := neg_nonneg.mpr (gerver_wide_firstVariation_nonpos hP hbox x)
  have hB := displacementEnergy_nonneg (π + P.φ) (3 * π / 2)
    (fun B => tangentParam B.1 (3 * π / 2)) (wideGerverTriple hP hbox).1.2.1 x.1.2.1
  have hD := displacementEnergy_nonneg (3 * π / 2) (3 * π / 2 + (π / 2 - P.φ))
    (fun D => tangentParam D.1 (3 * π / 2 + (π / 2 - P.φ)))
    (wideGerverTriple hP hbox).1.2.2 x.1.2.2
  have hC : 0 ≤ capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 := by
    have he := tripleResidualVector_norm_sq hP hbox x
    nlinarith [sq_nonneg ‖tripleResidualVector hP hbox x‖]
  change 0 ≤ rightResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1 at hB
  change 0 ≤ leftResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2 at hD
  change 0 ≤ wideDualSlack hP hbox x at hL
  change qDeficit P x = _ at hid
  unfold wideResidualEnergy at hid
  refine ⟨?_, hL, ?_, ?_, ?_⟩ <;> linarith

/-- The last cap arc has coefficient one, better than the whole-cap pinned bound. -/
theorem last_cap_profile_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    |capDifference P.cap x.1.1.1 t| ≤ sqrt (qDeficit P x) := by
  let f := capDifference P.cap x.1.1.1
  let df := capDifferenceDeriv P.cap x.1.1.1
  have hf := tripleResidualData hP hbox x
  have hlast := sharp_last_control hf ht
  have h1 := arcSquare_nonneg (gm_φ_pos hP).le (tangentResidual (π / 2) f df)
  have h2 := arcSquare_nonneg (by linarith [gm_φ_lt_θ hP, gm_θ_lt_c hP] : P.φ ≤ π / 2 - P.φ)
    (cornerResidual f df)
  have h3 := arcSquare_nonneg (by linarith [gm_φ_pos hP] : π / 2 - P.φ ≤ π / 2)
    (tangentResidual (π - P.φ) f df)
  have hE := wide_capResidualEnergy_le_deficit hP hbox x
  rw [← (capDifference_data (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1).2] at hE
  have harc : arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * qDeficit P x := by
    unfold fourResidualEnergy at hE
    linarith
  have hhalf : -sin t * cos t ≤ (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (sin t + cos t), sin_sq_add_cos_sq t]
  have hm := mul_le_mul_of_nonneg_right hhalf hlast.energy_nonneg
  have hs : f t ^ 2 ≤ qDeficit P x := by linarith [hlast.bound]
  exact abs_le_sqrt hs

/-- The initial B contact, divided by its cosine, has a safe coefficient three. -/
theorem first_cap_contact_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    |capDifference P.cap x.1.1.1 P.φ / cos P.φ| ≤ 3 * sqrt (qDeficit P x) := by
  have hc := cos_phi_ge_five_sixths hbox
  have hcpos : 0 < cos P.φ := by linarith
  have hf := sharp_wide_cap_support_bound hP hbox x
    (t := P.φ) ⟨(gm_φ_pos hP).le, by linarith [gm_φ_lt_θ hP, gm_θ_lt_c hP, pi_pos]⟩
  have hcoef : (2 / cos P.φ : ℝ) ≤ 3 * cos P.φ := by
    apply (div_le_iff₀ hcpos).2
    nlinarith
  rw [abs_div, abs_of_pos hcpos]
  apply (div_le_iff₀ hcpos).2
  have hm := mul_le_mul_of_nonneg_right hcoef (sqrt_nonneg (qDeficit P x))
  change |capDifference P.cap x.1.1.1 P.φ| ≤ _ * sqrt (qDeficit P x) at hf
  nlinarith only [hf, hm]

end MovingSofaQuantitative
