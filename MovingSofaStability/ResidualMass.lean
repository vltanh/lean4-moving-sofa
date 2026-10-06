module

public import MovingSofaStability.ResidualIntegrability

/-!
# First-moment bounds for residual reconstruction

These estimates give a deliberately non-sharp route from the four residual
equations to cap stability. They avoid the double integral calculation needed to
identify the sharp Green norm.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter

namespace MovingSofaStability

def arcMass (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, |f t|

def arcSquare (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t ^ 2

theorem arcMass_nonneg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : 0 ≤ arcMass a b f :=
  intervalIntegral.integral_nonneg_of_forall hab fun _ => abs_nonneg _

theorem arcSquare_nonneg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : 0 ≤ arcSquare a b f :=
  intervalIntegral.integral_nonneg_of_forall hab fun _ => sq_nonneg _

theorem arcMass_mono {a b c d : ℝ} {f : ℝ → ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hf : IntervalIntegrable f volume a b) : arcMass c d f ≤ arcMass a b f := by
  exact intervalIntegral.integral_mono_interval hac hcd hdb
    (Eventually.of_forall fun _ => abs_nonneg _) hf.abs

/-- Cauchy--Schwarz for one angular interval. -/
theorem arcMass_sq_le {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    arcMass a b f ^ 2 ≤ (b - a) * arcSquare a b f := by
  have h := integral_mul_sq_le (volume.restrict (Ioc a b))
    (f := fun t => |f t|) (g := fun _ => (1 : ℝ))
    (by simpa only [sq_abs] using hf2.1.integrable)
    (by simp)
    (by simpa only [mul_one] using hf.abs.1.integrable)
  have h1 : (∫ _ : ℝ in Ioc a b, (1 : ℝ)) = b - a := by
    rw [← intervalIntegral.integral_of_le hab]
    simp
  simp only [mul_one, sq_abs, one_pow] at h
  rw [h1, mul_comm] at h
  simpa only [arcMass, arcSquare, intervalIntegral.integral_of_le hab] using h

/-- Multiplication by a continuous bounded kernel only costs its uniform bound. -/
theorem weighted_integral_le_mass {a b B : ℝ} (hab : a ≤ b)
    {r k : ℝ → ℝ} (hr : IntervalIntegrable r volume a b)
    (hk : ContinuousOn k (Icc a b)) (hB : ∀ t ∈ Icc a b, |k t| ≤ B) :
    |∫ t in a..b, r t * k t| ≤ B * arcMass a b r := by
  have hik : IntervalIntegrable (fun t => r t * k t) volume a b := by
    exact hr.mul_continuousOn (by simpa only [uIcc_of_le hab] using hk)
  calc
    _ ≤ ∫ t in a..b, |r t * k t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, B * |r t| := by
      apply intervalIntegral.integral_mono_on hab hik.abs (hr.abs.const_mul B)
      intro t ht
      rw [abs_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB t ht) (abs_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

/-- A simple bound for integrating a uniformly controlled error function. -/
theorem abs_integral_le_length_mul {a b B : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, |f t| ≤ B) :
    |∫ t in a..b, f t| ≤ (b - a) * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := a) (b := b)
    (fun t ht => by
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs] using hf t ⟨ht.1.le, ht.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using h

/-- Four intervals, each of length at most two, suffice for a fixed energy constant. -/
theorem four_masses_le_four_sqrt {m₁ m₂ m₃ m₄ q₁ q₂ q₃ q₄ E : ℝ}
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    (h₁ : m₁ ^ 2 ≤ 2 * q₁) (h₂ : m₂ ^ 2 ≤ 2 * q₂)
    (h₃ : m₃ ^ 2 ≤ 2 * q₃) (h₄ : m₄ ^ 2 ≤ 2 * q₄)
    (htotal : q₁ + q₂ + q₃ + q₄ = 2 * E) :
    m₁ + m₂ + m₃ + m₄ ≤ 4 * sqrt E := by
  have hc := four_term_sq_le 1 1 1 1 m₁ m₂ m₃ m₄
  have hs : (m₁ + m₂ + m₃ + m₄) ^ 2 ≤ 4 ^ 2 * E := by
    nlinarith
  have h := abs_le_mul_sqrt_of_sq_le (C := 4) (by norm_num) hs
  rw [abs_of_nonneg (by positivity)] at h
  exact h

end MovingSofaStability
