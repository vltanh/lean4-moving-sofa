module

public import MovingSofaQuantitative.ScalarTaylor
public import MovingSofaQuantitative.ExplicitBudget
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact optimization and rational verification of the sector budget

Uncompiled proof source. The geometric sector-area formula is a separate input
at the recovery layer. This file proves the complete scalar inequality used
there, for EVERY split of the area deficit. Its numerical margin is checked by
rational normalization, not by a sampled minimizing split.

For the centered coefficient it suffices to use sin's degree-five upper bound,
cos's degree-six lower bound and arctan's degree-seventeen upper bound. This is
simpler than the finer interval certificate in the exploratory calculation.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaQuantitative

/-- The odd alternating partial sum ending in a positive term. -/
def atanUpper17 (x : ℝ) :=
  atanPoly7 x + x ^ 9 / 9 - x ^ 11 / 11 + x ^ 13 / 13 - x ^ 15 / 15 + x ^ 17 / 17

theorem hasDerivAt_atanUpper17 (x : ℝ) :
    HasDerivAt atanUpper17
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16) x := by
  convert (((((hasDerivAt_atanPoly7 x).add
    (((hasDerivAt_id x).pow 9).div_const 9)).sub
    (((hasDerivAt_id x).pow 11).div_const 11)).add
    (((hasDerivAt_id x).pow 13).div_const 13)).sub
    (((hasDerivAt_id x).pow 15).div_const 15)).add
    (((hasDerivAt_id x).pow 17).div_const 17) using 1 <;>
    simp only [atanUpper17] <;> norm_num <;> ring

theorem arctan_le_atanUpper17 {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ atanUpper17 x := by
  have hn := nonneg_from_derivative
    (f := fun t => atanUpper17 t - arctan t)
    (df := fun t => t ^ 18 / (1 + t ^ 2)) (by simp [atanUpper17, atanPoly7])
    (fun t => by
      convert (hasDerivAt_atanUpper17 t).sub (hasDerivAt_arctan t) using 1
      field_simp
      ring)
    (by fun_prop (disch := positivity))
    (fun t _ => div_nonneg (by positivity) (by positivity)) hx
  linarith

private theorem sin_mono_quadrant {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ π / 2) : sin x ≤ sin y := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_sin t) (continuous_cos.intervalIntegrable x y)
  have hn : 0 ≤ ∫ t in x..y, cos t := intervalIntegral.integral_nonneg hxy fun t ht =>
    cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2.trans hy⟩
  rw [he] at hn
  linarith

private theorem cos_anti_quadrant {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ π / 2) : cos y ≤ cos x := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_cos t) (continuous_sin.neg.intervalIntegrable x y)
  have hn : (∫ t in x..y, -sin t) ≤ 0 := intervalIntegral.integral_nonpos hxy fun t ht =>
    neg_nonpos.mpr (sin_nonneg_of_mem_Icc ⟨hx.trans ht.1, by linarith [ht.2, hy, pi_pos]⟩)
  rw [he] at hn
  linarith

def sectorAngleProfile (h B x : ℝ) := h - x - sin x * cos x + B * sin x ^ 2

theorem hasDerivAt_sectorAngleProfile (h B x : ℝ) :
    HasDerivAt (sectorAngleProfile h B) (2 * cos x * (B * sin x - cos x)) x := by
  convert ((((hasDerivAt_const x h).sub (hasDerivAt_id x)).sub
    ((hasDerivAt_sin x).mul (hasDerivAt_cos x))).add
    (((hasDerivAt_sin x).pow 2).const_mul B)) using 1
  · rfl
  · nlinarith [sin_sq_add_cos_sq x]

/-- The unique stationary angle supplies a global lower bound on the whole
first quadrant, including its endpoints. -/
theorem sectorAngleProfile_minimum (h : ℝ) {B x : ℝ} (hB : 0 < B)
    (hx : x ∈ Icc 0 (π / 2)) :
    h - arctan (1 / B) ≤ sectorAngleProfile h B x := by
  let a := arctan (1 / B)
  have ha0 : 0 < a := arctan_pos.mpr (one_div_pos.mpr hB)
  have ha1 : a < π / 2 := arctan_lt_pi_div_two _
  have hca : 0 < cos a := cos_arctan_pos _
  have he : B * sin a = cos a := by
    have ht := tan_arctan (1 / B)
    rw [tan_eq_sin_div_cos] at ht
    exact (div_eq_div_iff hca.ne' hB.ne').mp ht
  have hval : sectorAngleProfile h B a = h - a := by
    unfold sectorAngleProfile
    nlinarith [congrArg (fun z : ℝ => sin a * z) he]
  have hcont : Continuous (fun t => 2 * cos t * (B * sin t - cos t)) := by fun_prop
  rcases le_total x a with hxa | hax
  · have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_sectorAngleProfile h B t) (hcont.intervalIntegrable x a)
    have hn : (∫ t in x..a, 2 * cos t * (B * sin t - cos t)) ≤ 0 := by
      apply intervalIntegral.integral_nonpos hxa
      intro t ht
      have ht0 : 0 ≤ t := hx.1.trans ht.1
      have hs := sin_mono_quadrant ht0 ht.2 ha1.le
      have hc := cos_anti_quadrant ht0 ht.2 ha1.le
      have hs' := mul_le_mul_of_nonneg_left hs hB.le
      have hd : B * sin t - cos t ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) (cos_nonneg_of_mem_Icc
          ⟨by linarith [pi_pos], ht.2.trans ha1.le⟩)) hd
    rw [hFTC, hval] at hn
    linarith
  · have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_sectorAngleProfile h B t) (hcont.intervalIntegrable a x)
    have hn : 0 ≤ ∫ t in a..x, 2 * cos t * (B * sin t - cos t) := by
      apply intervalIntegral.integral_nonneg hax
      intro t ht
      have ht1 : t ≤ π / 2 := ht.2.trans hx.2
      have hs := sin_mono_quadrant ha0.le ht.1 ht1
      have hc := cos_anti_quadrant ha0.le ht.1 ht1
      have hs' := mul_le_mul_of_nonneg_left hs hB.le
      have hd : 0 ≤ B * sin t - cos t := by linarith
      exact mul_nonneg (mul_nonneg (by norm_num)
        (cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht1⟩)) hd
    rw [hFTC, hval] at hn
    linarith

/-- Area of the eroded sector divided by the target radius squared, in its
nonempty regime 0<=u<sin(h). -/
def sectorAreaFactor (h u : ℝ) :=
  h - arcsin u - u * sqrt (1 - u ^ 2) + u ^ 2 * (cos h / sin h)

/-- This inequality is valid on the larger scalar interval [0,1]; the geometric
application separately proves u<sin(h), so it never uses a nonexistent sector. -/
theorem sectorAreaFactor_penalized_lower {h q u : ℝ}
    (hB : 0 < cos h / sin h + q) (hu : u ∈ Icc 0 1) :
    h - arctan (1 / (cos h / sin h + q)) ≤ sectorAreaFactor h u + q * u ^ 2 := by
  have hangle : arcsin u ∈ Icc 0 (π / 2) :=
    ⟨arcsin_nonneg.mpr hu.1, arcsin_le_pi_div_two _⟩
  have hs : sin (arcsin u) = u := sin_arcsin (by linarith [hu.1]) hu.2
  have hc : cos (arcsin u) = sqrt (1 - u ^ 2) := cos_arcsin u
  have he := sectorAngleProfile_minimum h hB hangle
  simp only [sectorAngleProfile, hs, hc] at he
  unfold sectorAreaFactor
  nlinarith only [he]

def sectorHalfAngle : ℝ := 153 / 200
def centeredCapCoefficient : ℝ := 1001 / 1000
def missingBudgetCoefficient : ℝ := 10031 / 10000
def sectorPenaltyWeight : ℝ := missingBudgetCoefficient / (2 * centeredCapCoefficient ^ 2)
def sectorAtanUpperInput : ℝ :=
  sinPoly5 sectorHalfAngle / (cosPoly6 sectorHalfAngle + sectorPenaltyWeight * sinPoly5 sectorHalfAngle)

/-- Rational data for the centered sector calculation. The exact margin is
positive even with these deliberately coarser Taylor bounds. -/
theorem sector_rational_margins :
    0 < sinPoly5 sectorHalfAngle ∧ 0 < cosPoly6 sectorHalfAngle ∧
    0 < sectorPenaltyWeight ∧ 0 < sectorAtanUpperInput ∧
    (23 / 10 : ℝ) ^ 2 * (sectorHalfAngle - atanUpper17 sectorAtanUpperInput) >
      missingBudgetCoefficient ∧
    (23 / 10 : ℝ) ^ 2 * (sinPoly7 sectorHalfAngle) ^ 2 >
      2 * centeredCapCoefficient ^ 2 ∧ 0 < sinPoly7 sectorHalfAngle := by
  norm_num [sectorHalfAngle, sectorPenaltyWeight, missingBudgetCoefficient,
    centeredCapCoefficient, sectorAtanUpperInput, sinPoly5, cosPoly6,
    sinPoly7, atanUpper17, atanPoly7]

/-- The numerical arctangent input bounds the true one from above. -/
theorem sector_arctan_input_bound :
    1 / (cos sectorHalfAngle / sin sectorHalfAngle + sectorPenaltyWeight) ≤
      sectorAtanUpperInput := by
  have hh : sectorHalfAngle ∈ Ioo 0 (π / 2) := by
    unfold sectorHalfAngle
    constructor <;> linarith [pi_gt_three]
  have hs : 0 < sin sectorHalfAngle :=
    sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])
  have hc : 0 < cos sectorHalfAngle :=
    cos_pos_of_mem_Ioo ⟨by linarith [hh.1, pi_pos], hh.2⟩
  obtain ⟨hs5, hc6, hq, -, -, -, -⟩ := sector_rational_margins
  have hsin := sin_le_sinPoly5 hh.1.le
  have hcos := cosPoly6_le_cos hh.1.le
  have hl : 0 < cos sectorHalfAngle + sectorPenaltyWeight * sin sectorHalfAngle := by positivity
  have hr : 0 < cosPoly6 sectorHalfAngle + sectorPenaltyWeight * sinPoly5 sectorHalfAngle := by positivity
  have he : 1 / (cos sectorHalfAngle / sin sectorHalfAngle + sectorPenaltyWeight) =
      sin sectorHalfAngle / (cos sectorHalfAngle + sectorPenaltyWeight * sin sectorHalfAngle) := by
    field_simp
  rw [he]
  unfold sectorAtanUpperInput
  apply (div_le_div_iff₀ hl hr).2
  have hp := mul_le_mul hsin hcos hc6.le hs5.le
  nlinarith only [hp]

/-- A real, strict margin for the exact continuum minimum. -/
theorem centered_sector_minimum_margin :
    missingBudgetCoefficient < (23 / 10 : ℝ) ^ 2 *
      (sectorHalfAngle - arctan (1 / (cos sectorHalfAngle / sin sectorHalfAngle + sectorPenaltyWeight))) := by
  have hp := arctan_mono sector_arctan_input_bound
  have hq := arctan_le_atanUpper17 sector_rational_margins.2.2.2.1.le
  have hrat := sector_rational_margins.2.2.2.2.1
  nlinarith only [hp, hq, hrat]

/-- Every possible cap/missing-area split is covered. The square relation is
exactly u=sqrt(2)*k*sqrt(z)/(23/10), but avoids square-root cancellation here. -/
theorem centered_sector_split_budget {u z : ℝ} (hu : u ∈ Icc 0 1)
    (hrel : (23 / 10 : ℝ) ^ 2 * u ^ 2 = 2 * centeredCapCoefficient ^ 2 * z) :
    missingBudgetCoefficient * (1 - z) <
      (23 / 10 : ℝ) ^ 2 * sectorAreaFactor sectorHalfAngle u := by
  have hh : sectorHalfAngle ∈ Ioo 0 (π / 2) := by
    unfold sectorHalfAngle
    constructor <;> linarith [pi_gt_three]
  have hs := sin_pos_of_pos_of_lt_pi hh.1 (by linarith [hh.2, pi_pos])
  have hc := cos_pos_of_mem_Ioo (show sectorHalfAngle ∈ Ioo (-(π / 2)) (π / 2) by
    exact ⟨by linarith [hh.1, pi_pos], hh.2⟩)
  have hb : 0 < cos sectorHalfAngle / sin sectorHalfAngle + sectorPenaltyWeight := by
    have hq := sector_rational_margins.2.2.1
    positivity
  have hm := sectorAreaFactor_penalized_lower hb hu
  have hstrict := centered_sector_minimum_margin
  have he : (23 / 10 : ℝ) ^ 2 * (sectorPenaltyWeight * u ^ 2) =
      missingBudgetCoefficient * z := by
    unfold sectorPenaltyWeight
    have hk : centeredCapCoefficient ≠ 0 := by norm_num [centeredCapCoefficient]
    field_simp
    linear_combination missingBudgetCoefficient * hrel
  nlinarith only [hm, hstrict, he]

end MovingSofaQuantitative
