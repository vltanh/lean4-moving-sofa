module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The scalar equality case behind Mamikon convexity

The Mamikon formula is one half the integral of a squared tangent displacement.
The exact convexity gap is therefore a positive multiple of the squared L²
distance between the two displacement functions. This module proves that scalar
step without any moving-sofa definitions or unproved geometric assumptions.

Integrability is explicit. In particular, the fact that Lean's integral of a
nonintegrable function is defined to be zero cannot produce a spurious equality
case here.
-/

@[expose] public section

open MeasureTheory Filter

namespace MovingSofaUniqueness

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

/-- The scalar functional appearing in Mamikon's formula. -/
noncomputable def halfSquareIntegral (f : X → ℝ) : ℝ :=
  (1 / 2) * ∫ x, (f x) ^ 2 ∂μ

/-- Integrability of the squared displacement difference follows from the three
integrable quadratic monomials. -/
theorem integrable_sq_sub
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun x => (f x - g x) ^ 2) μ := by
  have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) μ :=
    (hf.add hg).sub (hfg.const_mul 2)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  ring

/-- Expanding the integral of a squared difference. -/
theorem integral_sq_sub
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) =
      (∫ x, (f x) ^ 2 ∂μ) + (∫ x, (g x) ^ 2 ∂μ) -
        2 * (∫ x, f x * g x ∂μ) := by
  calc
    (∫ x, (f x - g x) ^ 2 ∂μ) =
        ∫ x, (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf.add hg
      rw [integral_sub hsum (hfg.const_mul 2), integral_add hf hg, integral_const_mul]

/-- Expanding a squared affine combination before integrating. The identity is
valid for every real `c`, not only for convex coefficients. -/
theorem integral_sq_combo (c : ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
      (1 - c) ^ 2 * (∫ x, (f x) ^ 2 ∂μ) +
        (2 * c * (1 - c)) * (∫ x, f x * g x ∂μ) +
        c ^ 2 * (∫ x, (g x) ^ 2 ∂μ) := by
  calc
    (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
        ∫ x, (1 - c) ^ 2 * (f x) ^ 2 +
          (2 * c * (1 - c)) * (f x * g x) + c ^ 2 * (g x) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      have h12 : Integrable
          (fun x => (1 - c) ^ 2 * (f x) ^ 2 + (2 * c * (1 - c)) * (f x * g x)) μ :=
        (hf.const_mul ((1 - c) ^ 2)).add (hfg.const_mul (2 * c * (1 - c)))
      rw [integral_add h12 (hg.const_mul (c ^ 2)),
        integral_add (hf.const_mul ((1 - c) ^ 2)) (hfg.const_mul (2 * c * (1 - c))),
        integral_const_mul, integral_const_mul, integral_const_mul]

/-- Exact square-gap identity. At the midpoint the coefficient is `1/8`. -/
theorem halfSquareIntegral_combo_gap (c : ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g -
        halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
      (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
  unfold halfSquareIntegral
  rw [integral_sq_combo μ c hf hg hfg, integral_sq_sub μ hf hg hfg]
  ring

/-- Zero squared L² distance is exactly almost-everywhere equality. -/
theorem integral_sq_sub_eq_zero_iff
    (hint : Integrable (fun x => (f x - g x) ^ 2) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) = 0 ↔ f =ᵐ[μ] g := by
  have hzero := integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg (f x - g x)) hint
  constructor
  · intro h
    have hae := hzero.mp h
    filter_upwards [hae] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    apply hzero.mpr
    filter_upwards [h] with x hx
    simp [hx]

/-- Equality in a nontrivial convex combination forces equality of the
underlying displacement functions almost everywhere, and conversely. -/
theorem halfSquareIntegral_combo_eq_iff {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
        (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g ↔
      f =ᵐ[μ] g := by
  have hcoef : c * (1 - c) / 2 ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (by norm_num))
  have hint := integrable_sq_sub μ hf hg hfg
  constructor
  · intro heq
    have hz : (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) = 0 := by
      rw [← halfSquareIntegral_combo_gap μ c hf hg hfg, heq, sub_self]
    exact (integral_sq_sub_eq_zero_iff μ hint).mp
      ((mul_eq_zero.mp hz).resolve_left hcoef)
  · intro hae
    have hz := (integral_sq_sub_eq_zero_iff μ hint).mpr hae
    have hgap := halfSquareIntegral_combo_gap μ c hf hg hfg
    rw [hz, mul_zero] at hgap
    exact (sub_eq_zero.mp hgap).symm

end MovingSofaUniqueness
