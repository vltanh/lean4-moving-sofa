module

public import MovingSofaStability.GlobalConstantAlgebra

/-!
# Refined numerical budgets

Uncompiled proof source. These are scalar consequences used by the analytic
constant proof. They are not disguised unconditional theorems about sofas:
the geometric estimates producing their hypotheses are recorded separately.
The constants are 80 for Hausdorff distance, 204 for symmetric-difference area,
and 31/10 for the terminal angle, on a sufficiently small deficit regime.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality

namespace MovingSofaStability

/-- The reference box supplies the tighter lengths used in the area estimate. -/
theorem reference_width_bounds_tight {P : GerverParams} (h : P.Bounds) :
    (403 / 500 : ℝ) < 2 - 2 * P.a₁ - 2 * P.κ₃.1 ∧
      2 - 2 * P.a₁ - 2 * P.κ₃.1 < 1 ∧
      1 < 2 * P.κ₃.1 + 4 * P.a₁ - 2 ∧
      2 * P.κ₃.1 + 4 * P.a₁ - 2 < 13 / 8 ∧
      2 - 2 * P.κ₃.1 < 13 / 4 := by
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

/-- Euclidean geometry needs 26.1 radii of vertical shift, not 27. -/
theorem roof_cone_euclidean_bound {x y w : ℝ} (hw : 0 ≤ w)
    (hball : x ^ 2 + y ^ 2 ≤ w ^ 2) :
    26 * |x| - y ≤ (261 / 10) * w := by
  have hc : (26 * |x| - y) ^ 2 ≤ 677 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (|x| + 26 * y), sq_abs x]
  have hscale := mul_le_mul_of_nonneg_left hball (by norm_num : (0 : ℝ) ≤ 677)
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 261 / 10) hw]

/-- A strict rational bound suffices; no numerical value of pi is inserted. -/
theorem reverse_coefficient_lt_295 {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    2 * k ^ 2 + 2 / π < (59 / 20 : ℝ) ^ 2 := by
  have hpi : (3 : ℝ) < π := pi_gt_three
  have hfrac : 2 / π < (2 / 3 : ℝ) := by
    apply (div_lt_iff₀ pi_pos).2
    linarith
  nlinarith

/-- The improved interior-ball ratio closes a reverse-distance budget of 80. -/
theorem recovery_budget_80 {ε e k : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) <
      (10 / 271) * (80 * sqrt ε) := by
  have h := split_sqrt_budget he heε (sqrt 2 * k) (sqrt (2 / π))
  have h2 : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hpi : 0 ≤ (2 / π : ℝ) := div_nonneg (by norm_num) pi_pos.le
  rw [mul_pow, h2, sq_sqrt hpi] at h
  have hlt := mul_lt_mul_of_pos_right (reverse_coefficient_lt_295 hk0 hk) hε
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε.le
  have hsum : 0 ≤ sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) := by positivity
  have hsmall : sqrt 2 * k * sqrt e + sqrt (2 / π) * sqrt (ε - e) <
      (59 / 20) * sqrt ε := by nlinarith
  have harith : (59 / 20 : ℝ) < (10 / 271) * 80 := by norm_num
  exact hsmall.trans (by nlinarith [sqrt_pos.mpr hε])

/-- The missing-angle error remains linear and is absorbed only through a threshold. -/
theorem forward_budget_80 {ε e k B : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) (hB : 0 ≤ B)
    (hsmall : B * sqrt ε ≤ 1) :
    26 * (k * sqrt e + B * (ε - e)) < 80 * sqrt ε := by
  have hs := sqrt_pos.mpr hε
  have hke := mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) hk0
  have hBe := mul_le_mul_of_nonneg_left (show ε - e ≤ ε by linarith) hB
  have hBsmall := mul_le_mul_of_nonneg_right hsmall hs.le
  have hs2 := sq_sqrt hε.le
  have hkl := mul_le_mul_of_nonneg_right hk hs.le
  nlinarith

/-- Bound symmetric difference directly from the cap, not from the global
Hausdorff coefficient. The surplus uses only the unspent deficit. -/
theorem symmetric_difference_budget_204 {ε e k δ g d : ℝ}
    (hε : 0 ≤ ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ k * sqrt e)
    (hgain : g ≤ ε - e)
    (harea : d ≤ ε + 2 * g + (203 / 2) * δ + 8 * δ ^ 2)
    (hsmall : sqrt ε ≤ 1 / 50) : d ≤ 204 * sqrt ε := by
  have hs := sqrt_nonneg ε
  have hse := sqrt_nonneg e
  have hse2 := sq_sqrt he
  have hs2 := sq_sqrt hε
  have hδ2 : δ ^ 2 ≤ k ^ 2 * e := by nlinarith
  have hk2 : k ^ 2 ≤ (401 / 100 : ℝ) := by nlinarith
  have hδ2' : δ ^ 2 ≤ (401 / 100) * e :=
    hδ2.trans (mul_le_mul_of_nonneg_right hk2 he)
  have hδlinear : δ ≤ (1001 / 500) * sqrt ε := by
    exact hδbound.trans ((mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) hk0).trans
      (mul_le_mul_of_nonneg_right hk hs))
  have hd : d ≤ (203203 / 1000) * sqrt ε + (827 / 25) * ε := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hsmall hs
  nlinarith

/-- Truncate a vanishingly thin terminal triangle, losing only one part in 1000
from each of its height and horizontal width. -/
theorem terminal_trapezoid_coefficient_31 {D : ℝ} (hD : (403 / 500 : ℝ) ≤ D) :
    (10 / 31 : ℝ) < (999 / 1000) * (499 / 1000) * D ^ 2 - 1 / 1000 := by
  nlinarith

theorem terminal_budget_31_tenths {s u α lost gained D : ℝ}
    (hα : 0 ≤ α) (hD : (403 / 500 : ℝ) ≤ D)
    (hcompare : s + lost ≤ u + gained)
    (hlost : (999 / 1000) * (499 / 1000) * D ^ 2 * α ≤ lost)
    (hgain : gained ≤ α / 1000) :
    s ≤ u - (10 / 31) * α ∧ α ≤ (31 / 10) * (u - s) := by
  have hc := mul_le_mul_of_nonneg_right (terminal_trapezoid_coefficient_31 hD).le hα
  constructor <;> nlinarith

end MovingSofaStability
