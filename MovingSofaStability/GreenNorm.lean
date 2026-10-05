module

public import MovingSofaStability.ODEReconstruction

/-!
# Algebraic bound for the four-piece Green evaluation norm

Uncompiled proof source. The four formulas here are the squared evaluation
norms calculated in stability note 01. This file bounds them and proves the
rational numerical constant. Identifying them with the square integrals of
the reconstruction kernels is a distinct analytic obligation.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaStability

/-- The four candidate squared norms of the Green evaluation kernels. -/
def greenNormSquared (φ t : ℝ) : ℝ :=
  if t ≤ φ then cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t)
  else if t ≤ π / 2 - φ then cos t * (2 / cos φ - sin t)
  else if t ≤ π / 2 then sin t * cos t + 2 * tan φ * cos t ^ 2
  else -sin t * cos t

/-- Trigonometric quantities in the cap argument, without decimal approximation. -/
theorem cap_angle_parameters {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    0 < cos φ ∧ 1 ≤ 1 / cos φ ∧ 0 ≤ tan φ ∧
      (1 / cos φ) ^ 2 = 1 + tan φ ^ 2 := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have hA : 1 ≤ 1 / cos φ := by
    apply (le_div_iff₀ hc).2
    simpa using cos_le_one φ
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi hφ.1.le (by linarith [hφ.2])
  have hu : 0 ≤ tan φ := by rw [tan_eq_sin_div_cos]; exact div_nonneg hs hc.le
  refine ⟨hc, hA, hu, ?_⟩
  rw [tan_eq_sin_div_cos]
  have he := sin_sq_add_cos_sq φ
  field_simp [hc.ne']
  nlinarith

/-- The closed-form evaluation norm never exceeds its value at zero. -/
theorem greenNormSquared_le {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 π) : greenNormSquared φ t ≤ 2 * (1 / cos φ) ^ 2 := by
  obtain ⟨hcφ, hA, htanφ, hAid⟩ := cap_angle_parameters hφ
  have hAA : 1 ≤ (1 / cos φ) ^ 2 := by nlinarith
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have hcost : cos t ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t)]
  have hprod : sin t * cos t ≤ 1 / 2 := by
    nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t)]
  unfold greenNormSquared
  split_ifs with h1 h2 h3
  · have hct : 0 < cos t := cos_pos_of_mem_Ioo
      ⟨by linarith [pi_pos, ht.1], by linarith [hφ.2]⟩
    have htnt : 0 ≤ tan t := by rw [tan_eq_sin_div_cos]; exact div_nonneg hs hct.le
    have hmul : 0 ≤ cos t ^ 2 * tan t := mul_nonneg (sq_nonneg _) htnt
    have hscale := mul_le_mul_of_nonneg_right hcost
      (show 0 ≤ 2 * (1 / cos φ) ^ 2 by positivity)
    nlinarith
  · have hct : 0 ≤ cos t := (cos_pos_of_mem_Ioo
      ⟨by linarith [pi_pos, ht.1], by linarith [hφ.1]⟩).le
    have hterm : 0 ≤ cos t * sin t := mul_nonneg hct hs
    have hscale := mul_le_mul_of_nonneg_right (cos_le_one t)
      (show 0 ≤ 2 * (1 / cos φ) by positivity)
    have hrewrite : 2 / cos φ = 2 * (1 / cos φ) := by ring
    rw [hrewrite]
    nlinarith
  · have hscale := mul_le_mul_of_nonneg_left hcost
      (show 0 ≤ 2 * tan φ by positivity)
    nlinarith [sq_nonneg (tan φ - 1 / 2)]
  · have hnegprod : -sin t * cos t ≤ 1 / 2 := by
      nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t + cos t)]
    linarith

@[simp] theorem greenNormSquared_zero {φ : ℝ} (hφ : 0 ≤ φ) :
    greenNormSquared φ 0 = 2 * (1 / cos φ) ^ 2 := by
  simp [greenNormSquared, hφ]

/-- The bound is attained by the coefficient formula at the first endpoint. -/
theorem greenNormSquared_has_maximum {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    greenNormSquared φ 0 = 2 * (1 / cos φ) ^ 2 ∧
      ∀ t ∈ Icc 0 π, greenNormSquared φ t ≤ greenNormSquared φ 0 := by
  refine ⟨greenNormSquared_zero hφ.1.le, ?_⟩
  intro t ht
  rw [greenNormSquared_zero hφ.1.le]
  exact greenNormSquared_le hφ ht

/-- A purely rational upper bound for the explicit cap constant in the source box. -/
theorem cap_constant_lt_2002 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    2 / cos φ ≤ 2500 / 1249 ∧ 2 / cos φ < 1001 / 500 := by
  have hc0 := one_sub_sq_div_two_le_cos (x := φ)
  have hclower : (1249 / 1250 : ℝ) ≤ cos φ := by nlinarith [hφ.1, hφ.2]
  have hc : 0 < cos φ := by linarith
  have hbound : 2 / cos φ ≤ (2500 / 1249 : ℝ) := by
    apply (div_le_iff₀ hc).2
    nlinarith
  refine ⟨hbound, hbound.trans_lt ?_⟩
  norm_num

/-- Convert a verified squared evaluation bound to the explicit cap scale.
The analytic premise is kept visible until the kernel integrals are identified. -/
theorem green_evaluation_from_squared {φ value E : ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (hE : 0 ≤ E)
    (he : value ^ 2 ≤ 4 * (1 / cos φ) ^ 2 * E) :
    |value| ≤ (2 / cos φ) * sqrt E := by
  have hc : 0 < cos φ := (cap_angle_parameters hφ).1
  apply abs_le_mul_sqrt_of_sq_le (show 0 ≤ 2 / cos φ by positivity) hE
  convert he using 1 <;> ring

end MovingSofaStability
