module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Exact certificates for the two angular thresholds

These are ordinary algebraic proof scripts for the inequalities in paper note 19.
There is no generated certificate, external computation, `decide` tactic, or
native reduction. The file has not been elaborated or compiled.

The smaller threshold cannot be used over the entire angle interval; the last
lemma records the exact failed inequality, rather than hiding it in a decimal
check. These lemmas alone do not prove the geometric angular reduction.
-/

@[expose] public section

namespace SofaUniqueness.AngleCertificates

/-- The first polynomial certificate, expanded at `19/10`. -/
theorem first_polynomial (T : ℝ) :
    40 * T ^ 3 - 89 * T ^ 2 + 40 * T - 25 =
      40 * (T - 19 / 10) ^ 3 + 139 * (T - 19 / 10) ^ 2 +
        135 * (T - 19 / 10) + 407 / 100 := by
  ring

/-- The first threshold is valid on the larger-angle variable range needed. -/
theorem first_polynomial_pos {T : ℝ} (hT : 19 / 10 ≤ T) :
    0 < 40 * T ^ 3 - 89 * T ^ 2 + 40 * T - 25 := by
  rw [first_polynomial]
  have h : 0 ≤ T - 19 / 10 := sub_nonneg.mpr hT
  positivity

/-- The second polynomial certificate, expanded at `11/5`. -/
theorem second_polynomial (T : ℝ) :
    220 * T ^ 3 - 521 * T ^ 2 + 220 * T - 121 =
      220 * (T - 11 / 5) ^ 3 + 931 * (T - 11 / 5) ^ 2 +
        1122 * (T - 11 / 5) + 4598 / 25 := by
  ring

/-- The smaller threshold is used only in the second range. -/
theorem second_polynomial_pos {T : ℝ} (hT : 11 / 5 ≤ T) :
    0 < 220 * T ^ 3 - 521 * T ^ 2 + 220 * T - 121 := by
  rw [second_polynomial]
  have h : 0 ≤ T - 11 / 5 := sub_nonneg.mpr hT
  positivity

/-- Clearing the positive denominator in the first squared-height estimate. -/
theorem first_height_identity {T : ℝ} (hT : T ≠ 0) :
    (1 - (1 - (5 / 4 : ℝ) / T) ^ 2 - 4 / (1 + T ^ 2)) *
        (16 * T ^ 2 * (1 + T ^ 2)) =
      40 * T ^ 3 - 89 * T ^ 2 + 40 * T - 25 := by
  have hden : (1 : ℝ) + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

/-- Clearing the positive denominator in the second squared-height estimate. -/
theorem second_height_identity {T : ℝ} (hT : T ≠ 0) :
    (1 - (1 - (11 / 10 : ℝ) / T) ^ 2 - 4 / (1 + T ^ 2)) *
        (100 * T ^ 2 * (1 + T ^ 2)) =
      220 * T ^ 3 - 521 * T ^ 2 + 220 * T - 121 := by
  have hden : (1 : ℝ) + T ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

/-- The first squared-height estimate, without taking square roots. -/
theorem first_height_strict {T : ℝ} (hT : 19 / 10 ≤ T) :
    4 / (1 + T ^ 2) < 1 - (1 - (5 / 4 : ℝ) / T) ^ 2 := by
  have hpos : 0 < T := by linarith
  have hden : 0 < 16 * T ^ 2 * (1 + T ^ 2) := by positivity
  have hid := first_height_identity hpos.ne'
  have hp := first_polynomial_pos hT
  have hmul : 0 <
      (1 - (1 - (5 / 4 : ℝ) / T) ^ 2 - 4 / (1 + T ^ 2)) *
        (16 * T ^ 2 * (1 + T ^ 2)) := by rw [hid]; exact hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hmul)

/-- The second squared-height estimate. -/
theorem second_height_strict {T : ℝ} (hT : 11 / 5 ≤ T) :
    4 / (1 + T ^ 2) < 1 - (1 - (11 / 10 : ℝ) / T) ^ 2 := by
  have hpos : 0 < T := by linarith
  have hden : 0 < 100 * T ^ 2 * (1 + T ^ 2) := by positivity
  have hid := second_height_identity hpos.ne'
  have hp := second_polynomial_pos hT
  have hmul : 0 <
      (1 - (1 - (11 / 10 : ℝ) / T) ^ 2 - 4 / (1 + T ^ 2)) *
        (100 * T ^ 2 * (1 + T ^ 2)) := by rw [hid]; exact hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hmul)

/-- Increasing the excess extent up to `T` increases the squared height. -/
theorem height_mono {d₀ d T : ℝ} (hT : 0 < T) (hd₀ : 0 ≤ d₀)
    (hdd : d₀ ≤ d) (hdT : d ≤ T) :
    1 - (1 - d₀ / T) ^ 2 ≤ 1 - (1 - d / T) ^ 2 := by
  have hdiv : d₀ / T ≤ d / T := div_le_div_of_nonneg_right hdd hT.le
  have hdnonneg : 0 ≤ d / T := div_nonneg (hd₀.trans hdd) hT.le
  have hdle : d / T ≤ 1 := (div_le_one hT).mpr hdT
  nlinarith

/-- The truncated-parallelogram bound in the first range. -/
theorem first_area_strict {c T : ℝ} (hc : c < 1 / 4)
    (hT : 0 < T) (hThi : T < 11 / 5) :
    c + 2 * (5 / 4 : ℝ) - (5 / 4 : ℝ) ^ 2 / T < 11 / 5 := by
  have hq : (125 / 176 : ℝ) < (5 / 4 : ℝ) ^ 2 / T := by
    apply (lt_div_iff₀ hT).mpr
    nlinarith
  linarith

/-- The truncated-parallelogram bound in the second range. -/
theorem second_area_strict {c T : ℝ} (hc : c < 1 / T) (hT : 0 < T) :
    c + 2 * (11 / 10 : ℝ) - (11 / 10 : ℝ) ^ 2 / T < 11 / 5 := by
  have hq : (1 : ℝ) / T < (11 / 10 : ℝ) ^ 2 / T := by
    apply (div_lt_div_iff_of_pos_right hT).mpr
    norm_num
  linarith

/-- Negative regression: the uniform `11/10` threshold fails at the lower angle.
Only the known squared sine value is needed to exhibit the failure. -/
theorem smaller_threshold_fails {s : ℝ} (hs : s ^ 2 = 96 / 121) :
    ((11 / 10 : ℝ) * s) ^ 2 = 24 / 25 ∧
      ((11 / 10 : ℝ) * s) ^ 2 < 1 := by
  have h : ((11 / 10 : ℝ) * s) ^ 2 = 24 / 25 := by
    rw [mul_pow, hs]
    norm_num
  exact ⟨h, by rw [h]; norm_num⟩

end SofaUniqueness.AngleCertificates
