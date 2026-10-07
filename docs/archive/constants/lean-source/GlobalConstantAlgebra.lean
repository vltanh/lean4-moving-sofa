module

public import MovingSofaStability.DeficitBudget
public import MovingSofaOptimality.Gerver.Bounds

/-!
# Explicit constants: scalar and parameter arithmetic

Uncompiled proof source. These declarations prove the arithmetic part of the
new estimates. They are not labelled as an assembled theorem for moving sofas:
the new reference-geometry and sharp-erosion adapters are distinct obligations.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality

namespace MovingSofaStability

/-- The reference enclosures give comfortable rational wing and roof widths. -/
theorem reference_width_bounds {P : GerverParams} (h : P.Bounds) :
    (4 / 5 : ℝ) < 2 - 2 * P.a₁ - 2 * P.κ₃.1 ∧
      2 - 2 * P.a₁ - 2 * P.κ₃.1 < 1 ∧
      1 < 2 * P.κ₃.1 + 4 * P.a₁ - 2 ∧
      2 * P.κ₃.1 + 4 * P.a₁ - 2 < 2 ∧ 2 - 2 * P.κ₃.1 < 4 := by
  have ha := h.a₁_mem
  have hk := h.κ₃₁_mem
  constructor
  · linarith [ha.2, hk.2]
  constructor
  · linarith [ha.1, hk.1]
  constructor
  · linarith [ha.1, hk.1]
  constructor
  · linarith [ha.2, hk.2]
  · linarith [hk.1]

/-- Only pi>3 is needed for the conservative reverse-distance coefficient. -/
theorem reverse_coefficient_squared {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    2 * k ^ 2 + 2 / π < (3 : ℝ) ^ 2 := by
  have hpi : (3 : ℝ) < π := pi_gt_three
  have hfrac : 2 / π < (2 / 3 : ℝ) := by
    apply (div_lt_iff₀ pi_pos).2
    linarith
  nlinarith

/-- Preserve the split deficit through Cauchy--Schwarz. -/
theorem split_recovery_cost_lt_three {ε e k : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) < 3 * sqrt ε := by
  have h := split_sqrt_budget he heε (sqrt 2 * k) (sqrt (2 / π))
  have h2 : (sqrt (2 : ℝ)) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hpi : 0 ≤ (2 / π : ℝ) := div_nonneg (by norm_num) pi_pos.le
  rw [mul_pow, h2, sq_sqrt hpi] at h
  have hlt := mul_lt_mul_of_pos_right (reverse_coefficient_squared hk0 hk) hε
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε.le
  have hsum : 0 ≤ sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) := by positivity
  nlinarith

/-- The reverse coefficient 84 corresponds to kappa=1/28 and scaled radius 3. -/
theorem recovery_budget_84 {ε e k : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) <
      (1 / 28) * (84 * sqrt ε) := by
  convert split_recovery_cost_lt_three hε he heε hk0 hk using 1 <;> ring

/-- With a smaller threshold the linear angle allowance costs at most one unit
of sqrt epsilon before the roof factor 26 is applied. -/
theorem forward_budget_84 {ε e k B : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) (hB : 0 ≤ B)
    (hsmall : B * sqrt ε ≤ 1) :
    26 * (k * sqrt e + B * (ε - e)) < 84 * sqrt ε := by
  have hs := sqrt_pos.mpr hε
  have hse := sqrt_le_sqrt heε
  have hke := mul_le_mul_of_nonneg_left hse hk0
  have hBe := mul_le_mul_of_nonneg_left (show ε - e ≤ ε by linarith) hB
  have hBsmall := mul_le_mul_of_nonneg_right hsmall hs.le
  have hs2 := sq_sqrt hε.le
  have hkl := mul_le_mul_of_nonneg_right hk hs.le
  nlinarith

/-- The improved trapezoid's floor area exceeds 21/80 times the omitted angle. -/
theorem terminal_trapezoid_coefficient {D : ℝ} (hD : (4 / 5 : ℝ) ≤ D) :
    (21 / 80 : ℝ) ≤ (105 / 256) * D ^ 2 := by nlinarith

/-- Subtracting an arbitrarily small omitted-wedge gain leaves a fixed angle coefficient. -/
theorem terminal_budget_four {s u α lost gained : ℝ}
    (hα : 0 ≤ α) (hcompare : s + lost ≤ u + gained)
    (hlost : (21 / 80) * α ≤ lost) (hgain : gained ≤ (1 / 80) * α) :
    s ≤ u - α / 4 ∧ α ≤ 4 * (u - s) := by
  constructor <;> linarith

/-- A scalar area consequence of the reference dilation and roof-band estimates.
This is deliberately separate from proving those geometric hypotheses. -/
theorem symmetric_difference_budget_15000 {ε h d : ℝ}
    (hε : 0 ≤ ε) (hh : 0 ≤ h) (hhbound : h ≤ 84 * sqrt ε)
    (hd : d ≤ ε + 172 * h + 128 * h ^ 2)
    (hsmall : sqrt ε ≤ 552 / 903169) : d ≤ 15000 * sqrt ε := by
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε
  have hsq : h ^ 2 ≤ 84 ^ 2 * ε := by nlinarith
  have hlin : 172 * h ≤ 14448 * sqrt ε := by linarith
  have hrem := mul_le_mul_of_nonneg_right hsmall hs
  have htotal : d ≤ 14448 * sqrt ε + 903169 * ε := by nlinarith
  nlinarith

end MovingSofaStability
