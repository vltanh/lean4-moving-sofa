module

public import MovingSofaStability.MamikonEnergy

/-!
# Integral estimates for the residual-to-support step

Uncompiled proof source. Integrability assumptions are explicit: totalized
Bochner integrals must not be used to conceal a nonintegrable residual.
The Cauchy--Schwarz proof below uses nonnegativity of a square integral and
also handles a zero square norm. No new integration axioms are introduced.
-/

@[expose] public section
noncomputable section

open Real MeasureTheory Filter
open MovingSofaUniqueness

namespace MovingSofaStability

section Integral

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

/-- Cauchy--Schwarz in a form convenient for the real tangent residuals. -/
theorem integral_mul_sq_le
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let A : ℝ := ∫ x, f x ^ 2 ∂μ
  let B : ℝ := ∫ x, g x ^ 2 ∂μ
  let C : ℝ := ∫ x, f x * g x ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg (f x)
  change C ^ 2 ≤ A * B
  by_cases hA0 : A = 0
  · have hfzero : ∀ᵐ x ∂μ, f x = 0 := by
      have hz : ∀ᵐ x ∂μ, f x ^ 2 = 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf).1 hA0
      filter_upwards [hz] with x hx
      have hmul : f x * f x = 0 := by simpa only [pow_two] using hx
      exact (mul_eq_zero.mp hmul).elim id id
    have hC0 : C = 0 := by
      change (∫ x, f x * g x ∂μ) = 0
      calc
        _ = ∫ _ : X, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hfzero] with x hx
          simp only [hx, zero_mul]
        _ = 0 := integral_zero X ℝ
    rw [hA0, hC0]
    norm_num
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hleft : Integrable (fun x => C ^ 2 * f x ^ 2 + A ^ 2 * g x ^ 2) μ :=
      (hf.const_mul _).add (hg.const_mul _)
    have hright : Integrable (fun x => (2 * C * A) * (f x * g x)) μ :=
      hfg.const_mul _
    have hi : (∫ x, (C * f x - A * g x) ^ 2 ∂μ) =
        C ^ 2 * A + A ^ 2 * B - (2 * C * A) * C := by
      calc
        _ = ∫ x, (C ^ 2 * f x ^ 2 + A ^ 2 * g x ^ 2) -
            (2 * C * A) * (f x * g x) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
        _ = _ := by
          rw [integral_sub hleft hright,
            integral_add (hf.const_mul _) (hg.const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
    have hn : 0 ≤ C ^ 2 * A + A ^ 2 * B - (2 * C * A) * C := by
      rw [← hi]
      exact integral_nonneg fun x => sq_nonneg _
    have hp : A * C ^ 2 ≤ A * (A * B) := by nlinarith
    exact (mul_le_mul_iff_right₀ hApos).mp hp

/-- Absolute-value form of the preceding estimate. -/
theorem abs_integral_mul_le
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    |∫ x, f x * g x ∂μ| ≤
      sqrt (∫ x, f x ^ 2 ∂μ) * sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hn : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h := Real.sqrt_le_sqrt (integral_mul_sq_le μ hf hg hfg)
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_mul hn] using h

/-- A bound on the square norm of a Green evaluation kernel gives a uniform
error estimate from the half-square residual energy. -/
theorem green_evaluation_bound {k r : X → ℝ} {C value : ℝ}
    (hC : 0 ≤ C)
    (hk : Integrable (fun x => k x ^ 2) μ)
    (hr : Integrable (fun x => r x ^ 2) μ)
    (hkr : Integrable (fun x => k x * r x) μ)
    (hkernel : (∫ x, k x ^ 2 ∂μ) ≤ C ^ 2)
    (hvalue : value = ∫ x, k x * r x ∂μ) :
    |value| ≤ C * sqrt (2 * halfSquareIntegral μ r) := by
  have hkC : sqrt (∫ x, k x ^ 2 ∂μ) ≤ C := (Real.sqrt_le_left hC).2 hkernel
  have he : (∫ x, r x ^ 2 ∂μ) = 2 * halfSquareIntegral μ r := by
    unfold halfSquareIntegral
    ring
  rw [hvalue]
  calc
    _ ≤ sqrt (∫ x, k x ^ 2 ∂μ) * sqrt (∫ x, r x ^ 2 ∂μ) :=
      abs_integral_mul_le μ hk hr hkr
    _ ≤ C * sqrt (∫ x, r x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right hkC (sqrt_nonneg _)
    _ = _ := by rw [he]

end Integral

/-- The elementary four-term Cauchy--Schwarz identity used when keeping the
four residual intervals separate. -/
theorem four_term_sq_le (a b c d x y z w : ℝ) :
    (a * x + b * y + c * z + d * w) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  have he :
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) -
        (a * x + b * y + c * z + d * w) ^ 2 =
      (a * y - b * x) ^ 2 + (a * z - c * x) ^ 2 + (a * w - d * x) ^ 2 +
      (b * z - c * y) ^ 2 + (b * w - d * y) ^ 2 + (c * w - d * z) ^ 2 := by ring
  apply sub_nonneg.mp
  rw [he]
  positivity

/-- The final scalar passage from a squared norm estimate to square-root stability. -/
theorem abs_le_mul_sqrt_of_sq_le {d C E : ℝ} (hC : 0 ≤ C)
    (h : d ^ 2 ≤ C ^ 2 * E) : |d| ≤ C * sqrt E := by
  have hroot := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hC] at hroot
  exact hroot

end MovingSofaStability
