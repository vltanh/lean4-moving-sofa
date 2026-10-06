module

public import MovingSofaStability.SharpReconstruction
public import MovingSofaStability.GreenNorm

/-!
# The actual kernel integrals equal the closed-form Green norms

Uncompiled proof source. These equalities connect the displayed Green formulas
to integrals, rather than merely bounding the formulas as independent scalars.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

private theorem reciprocal_endpoint_cancel (A c s : ℝ) (hs : s ≠ 0)
    (hAc : A * c = 1) (hunit : s ^ 2 + c ^ 2 = 1) :
    A * s + (A ^ 2 + 1) * (c / s) - 2 * A / s = 0 := by
  field_simp [hs]
  linear_combination A * hunit + (A - c) * hAc

private theorem middle_variable_cancel (A c s : ℝ) (hc : c ≠ 0)
    (hunit : s ^ 2 + c ^ 2 = 1) :
    ((A - s) ^ 2 - (A ^ 2 + 1)) * (s / c) + 2 * A / c = c * (2 * A - s) := by
  field_simp [hc]
  linear_combination (s - 2 * A) * hunit

/-- Norm of the r3 kernel on its whole arc. -/
theorem third_full_kernel_norm {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) = tan φ := by
  have hs : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, hφ.1, pi_pos])).ne'
  rw [shifted_cosecant_sq_integral (by linarith [hφ.1]) hs]
  simp only [cotangent, show π - φ - π / 2 = π / 2 - φ by ring,
    show π - φ - (π / 2 - φ) = π / 2 by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub, cos_pi_div_two, sin_pi_div_two,
    zero_div, sub_zero, tan_eq_sin_div_cos]

/-- The third-arc evaluation includes a last-arc component, and their squared
norms add before estimating f. -/
theorem third_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    (-(cos t / cos φ)) ^ 2 * (-sin (π - φ) * cos (π - φ)) +
      sin (π - φ - t) ^ 2 *
        (∫ u in t..(π / 2), (1 / sin (π - φ - u)) ^ 2) =
      sin t * cos t + 2 * tan φ * cos t ^ 2 := by
  sorry

/-- The middle-arc kernel has two disjoint pieces on the last residual arc. -/
theorem middle_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc φ (π / 2 - φ)) :
    (π / 2 - φ - t) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) +
      ((1 / cos φ - sin t) ^ 2 *
        (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) ^ 2) +
        (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u ^ 2)) =
      cos t * (2 / cos φ - sin t) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hcφ : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hp0 (by linarith)).ne'
  have hct : cos t ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩).ne'
  have hs : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hsin1 : ∀ u ∈ Icc (π / 2) (π / 2 + t), sin u ≠ 0 :=
    fun u hu => hs u ⟨hu.1, by linarith [hu.2, ht.2]⟩
  have hsin2 : ∀ u ∈ Icc (π / 2 + t) (π - φ), sin u ≠ 0 :=
    fun u hu => hs u ⟨by linarith [hu.1, ht.1], hu.2⟩
  rw [third_full_kernel_norm hφ,
    cosecant_sq_integral (by linarith [ht.1]) hsin1,
    tailKernel_sq_integral (1 / cos φ) (by linarith [ht.2]) hsin2]
  let A := 1 / cos φ
  have hAc : A * cos φ = 1 := by
    dsimp [A]
    field_simp [hcφ]
  have hbase := reciprocal_endpoint_cancel A (cos φ) (sin φ) hsφ hAc (sin_sq_add_cos_sq φ)
  have hvar := middle_variable_cancel A (cos t) (sin t) hct (sin_sq_add_cos_sq t)
  change (π / 2 - φ - t) + tan φ +
    ((A - sin t) ^ 2 * (cotangent (π / 2) - cotangent (π / 2 + t)) +
      (tailKernelPrimitive A (π - φ) - tailKernelPrimitive A (π / 2 + t))) = _
  simp only [tailKernelPrimitive, cotangent, sin_pi_sub, cos_pi_sub,
    sin_add, cos_add, sin_pi_div_two, cos_pi_div_two,
    one_mul, zero_mul, zero_add, add_zero, zero_div, zero_sub,
    tan_eq_sin_div_cos]
  have htan : sin φ / cos φ = A * sin φ := by dsimp [A]; ring
  have htwo : 2 / cos φ = 2 * A := by dsimp [A]; ring
  rw [htan, htwo]
  linear_combination hbase + hvar

/-- On the first arc the middle evaluation at phi has disjoint energy from r1. -/
theorem first_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) :
    (cos t / cos φ) ^ 2 * (cos φ * (2 / cos φ - sin φ)) +
      cos t ^ 2 * (∫ u in t..φ, (1 / cos u) ^ 2) =
      cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t) := by
  have hcφ := (cap_angle_parameters hφ).1.ne'
  have hc : ∀ u ∈ Icc t φ, cos u ≠ 0 := by
    intro u hu
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1, pi_pos],
      by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
  rw [secant_sq_integral ht.2 hc, tan_eq_sin_div_cos φ]
  field_simp [hcφ]
  ring

end MovingSofaStability
