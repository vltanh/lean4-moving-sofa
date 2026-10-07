module

public import MovingSofaQuantitative.KernelGram

/-!
# Closed primitives for the continuum Gram matrix

Uncompiled proof source. These identities concern integrals of the actual
continuous kernel weights. They are the missing semantic step between a
finite trigonometric expression and a Hilbert inner product. Empty overlaps
are still handled by KernelGram, never by reversing an integral.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

/-- The derivative of minus cosecant gives the mixed cosecant-cotangent term. -/
theorem neg_cosecant_derivative {t : ℝ} (hs : sin t ≠ 0) :
    HasDerivAt (fun u : ℝ => -(1 / sin u)) (cos t / sin t ^ 2) t := by
  convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_sin t) hs).neg using 1 <;> ring

theorem cosecant_cotangent_integral {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t ∈ Icc a b, sin t ≠ 0) :
    (∫ t in a..b, (1 / sin t) * (cos t / sin t)) = 1 / sin a - 1 / sin b := by
  have hc : ContinuousOn (fun t => (1 / sin t) * (cos t / sin t)) (Icc a b) :=
    (continuousOn_const.div continuous_sin.continuousOn hs).mul
      (continuous_cos.continuousOn.div continuous_sin.continuousOn hs)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(1 / sin t))
    (f' := fun t => (1 / sin t) * (cos t / sin t))
    (fun t ht => by
      have hst := hs t (by simpa only [uIcc_of_le hab] using ht)
      convert neg_cosecant_derivative hst using 1 <;> ring)
    (hc.intervalIntegrable_of_Icc hab)
  linarith

theorem cotangent_sq_integral {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t ∈ Icc a b, sin t ≠ 0) :
    (∫ t in a..b, (cos t / sin t) ^ 2) =
      cotangent a - cotangent b - (b - a) := by
  have hc : ContinuousOn (fun t => (1 / sin t) ^ 2) (Icc a b) :=
    (continuousOn_const.div continuous_sin.continuousOn hs).pow 2
  have hid : (∫ t in a..b, (cos t / sin t) ^ 2) =
      ∫ t in a..b, (1 / sin t) ^ 2 - 1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hst := hs t (by simpa only [uIcc_of_le hab] using ht)
    field_simp [hst]
    nlinarith [sin_sq_add_cos_sq t]
  rw [hid, intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc hab) intervalIntegrable_const,
    cosecant_sq_integral hab hs]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- The last-arc Gram entry for two general cosecant/cotangent combinations. -/
theorem last_kernel_cross_integral (A B C D : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t ∈ Icc a b, sin t ≠ 0) :
    (∫ t in a..b, (A / sin t + B * (cos t / sin t)) *
      (C / sin t + D * (cos t / sin t))) =
      A * C * (cotangent a - cotangent b) +
      (A * D + B * C) * (1 / sin a - 1 / sin b) +
      B * D * (cotangent a - cotangent b - (b - a)) := by
  have h1 : ContinuousOn (fun t => 1 / sin t) (Icc a b) :=
    continuousOn_const.div continuous_sin.continuousOn hs
  have h2 : ContinuousOn (fun t => cos t / sin t) (Icc a b) :=
    continuous_cos.continuousOn.div continuous_sin.continuousOn hs
  have i1 := (h1.pow 2).intervalIntegrable_of_Icc hab
  have i2 := (h1.mul h2).intervalIntegrable_of_Icc hab
  have i3 := (h2.pow 2).intervalIntegrable_of_Icc hab
  have he : (∫ t in a..b, (A / sin t + B * (cos t / sin t)) *
      (C / sin t + D * (cos t / sin t))) =
      ∫ t in a..b, A * C * (1 / sin t) ^ 2 +
        (A * D + B * C) * ((1 / sin t) * (cos t / sin t)) +
        B * D * (cos t / sin t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he, intervalIntegral.integral_add
    ((i1.const_mul (A * C)).add (i2.const_mul (A * D + B * C))) (i3.const_mul (B * D)),
    intervalIntegral.integral_add (i1.const_mul (A * C)) (i2.const_mul (A * D + B * C)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, cosecant_sq_integral hab hs,
    cosecant_cotangent_integral hab hs, cotangent_sq_integral hab hs]

/-- First-arc Gram entry. -/
theorem first_kernel_cross_integral (A C : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, cos t ≠ 0) :
    (∫ t in a..b, (A / cos t) * (C / cos t)) = A * C * (tan b - tan a) := by
  have he : (∫ t in a..b, (A / cos t) * (C / cos t)) =
      A * C * ∫ t in a..b, (1 / cos t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he, secant_sq_integral hab hc]

/-- Third-arc Gram entry, with the shifted denominator retained. -/
theorem third_kernel_cross_integral (A C T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0) :
    (∫ t in a..b, (A / sin (T - t)) * (C / sin (T - t))) =
      A * C * (cotangent (T - b) - cotangent (T - a)) := by
  have he : (∫ t in a..b, (A / sin (T - t)) * (C / sin (T - t))) =
      A * C * ∫ t in a..b, (1 / sin (T - t)) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he, shifted_cosecant_sq_integral hab hs]

/-- A bounded integrand on a possibly empty overlap has the elementary signed
length enclosure used when interval endpoints cannot yet be ordered. -/
theorem integral_overlap_bounds {a b L U : ℝ} {f : ℝ → ℝ}
    (hi : IntegrableOn f (Icc a b)) (hf : ∀ t ∈ Icc a b, L ≤ f t ∧ f t ≤ U) :
    L * max 0 (b - a) ≤ (∫ t in Icc a b, f t) ∧
      (∫ t in Icc a b, f t) ≤ U * max 0 (b - a) := by
  by_cases hab : a ≤ b
  · have hL := setIntegral_mono_on (integrableOn_const (by simp)) hi measurableSet_Icc
      (fun t ht => (hf t ht).1)
    have hU := setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Icc
      (fun t ht => (hf t ht).2)
    rw [max_eq_right (sub_nonneg.mpr hab)]
    simp only [integral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul] at hL hU
    constructor <;> nlinarith only [hL, hU]
  · have hba := not_le.mp hab
    rw [Icc_eq_empty hba, max_eq_left (sub_nonpos.mpr hba.le)]
    simp

end MovingSofaQuantitative
