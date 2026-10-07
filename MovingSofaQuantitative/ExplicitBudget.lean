module

public import MovingSofaStability.Basic

/-!
# Complementary deficit budgets

Uncompiled proof source. `S` need not be contained in its full-angle envelope
`U`. Surplus area is retained in the exact balance identity. The scalar lemmas
below are the arithmetic assembly, not the geometric terminal-loss theorem.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- Exact balance for the two actual sets, written with their two deficits. -/
theorem missing_area_identity {S U : Set Point} (hS : MeasurableSet S)
    (hU : MeasurableSet U) (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) (M : ℝ) :
    area (U \ S) = (M - area S) - (M - area U) + area (S \ U) := by
  have he := area_sdiff_balance hS hU hSf hUf
  linarith

/-- A terminal loss and an endpoint-wedge gain give the complementary budget.
The inequalities in the hypotheses are geometric inputs proved separately. -/
theorem precise_terminal_budget {S U : Set Point} {M α : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤)
    (hα : 0 ≤ α) (hmax : area U ≤ M)
    (hloss : area S ≤ area U - (10 / 31) * α)
    (hgain : area (S \ U) ≤ α / 1000) :
    0 ≤ M - area U ∧ M - area U ≤ M - area S ∧
      α ≤ (31 / 10) * ((M - area S) - (M - area U)) ∧
      area (S \ U) ≤ (31 / 10000) * ((M - area S) - (M - area U)) ∧
      area (U \ S) ≤ (10031 / 10000) * ((M - area S) - (M - area U)) := by
  have he := missing_area_identity hS hU hSf hUf M
  refine ⟨sub_nonneg.mpr hmax, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- No factor two is necessary when the sofa actually is contained in U. -/
theorem contained_budget {S U : Set Point} (hSU : S ⊆ U)
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) (M : ℝ) :
    area (U \ S) = (M - area S) - (M - area U) := by
  have he := missing_area_identity hS hU hSf hUf M
  simpa only [sdiff_eq_empty.mpr hSU, area, measure_empty, ENNReal.toReal_zero, add_zero] using he

/-- The two errors spend disjoint portions of the same total deficit. -/
theorem complementary_sqrt_budget {ε e : ℝ} (he : 0 ≤ e) (heε : e ≤ ε)
    (a b : ℝ) :
    (a * sqrt e + b * sqrt (ε - e)) ^ 2 ≤ (a ^ 2 + b ^ 2) * ε := by
  have hs := sq_nonneg (a * sqrt (ε - e) - b * sqrt e)
  have h1 := sq_sqrt he
  have h2 := sq_sqrt (sub_nonneg.mpr heε)
  nlinarith only [hs, congrArg (fun x : ℝ => a ^ 2 * x) h1,
    congrArg (fun x : ℝ => a ^ 2 * x) h2,
    congrArg (fun x : ℝ => b ^ 2 * x) h1,
    congrArg (fun x : ℝ => b ^ 2 * x) h2]

/-- A strict improvement in the leading coefficient absorbs a linear error. -/
theorem absorb_linear_term {A C B : ℝ} (hAC : A < C) (hB : 0 ≤ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      A * sqrt ε + B * ε ≤ C * sqrt ε := by
  let r := (C - A) / (B + 1)
  have hr : 0 < r := div_pos (sub_pos.mpr hAC) (by linarith)
  have he : (B + 1) * r = C - A := by
    dsimp [r]
    field_simp
  refine ⟨r ^ 2, sq_pos_of_pos hr, ?_⟩
  intro ε hε hsmall
  have hroot : sqrt ε ≤ r := by
    nlinarith [sq_sqrt hε, sqrt_nonneg ε]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot hB) (sqrt_nonneg ε)
  have hs := congrArg (fun x : ℝ => B * x) (sq_sqrt hε)
  have hslack : 0 ≤ r * sqrt ε := mul_nonneg hr.le (sqrt_nonneg ε)
  nlinarith only [hm, hs, congrArg (fun x : ℝ => x * sqrt ε) he, hslack]

/-- The direct roof-band area estimate with midpoint cap coefficient.
This is exact rational arithmetic; no Hausdorff coefficient is used. -/
theorem midpoint_area_budget {ε e : ℝ} (he : 0 ≤ e) (heε : e ≤ ε) :
    2 * (62307 / 2500) * (1001 / 1000) * sqrt e +
      (3 * ε - 2 * e) + 8 * (1001 / 1000) ^ 2 * e ≤
    (62369307 / 1250000) * sqrt ε + (1377001 / 125000) * ε := by
  have hs := sqrt_le_sqrt heε
  have heps : 0 ≤ ε := he.trans heε
  nlinarith only [hs, he, heε, heps]

/-- At sqrt(epsilon)<=1/200, the linear remainder fits below coefficient 50. -/
theorem midpoint_area_coefficient {ε : ℝ} (hε : 0 ≤ ε) (hs : sqrt ε ≤ 1 / 200) :
    (62369307 / 1250000) * sqrt ε + (1377001 / 125000) * ε ≤ 50 * sqrt ε := by
  have hmul := mul_le_mul_of_nonneg_right hs (sqrt_nonneg ε)
  rw [sq, ← mul_assoc] at hmul
  have he := sq_sqrt hε
  nlinarith [sqrt_nonneg ε]

end MovingSofaQuantitative
