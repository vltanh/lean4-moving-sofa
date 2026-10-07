module

public import MovingSofaStability.TerminalBookkeeping

/-!
# The cap and the missing set spend the same deficit

Uncompiled proof source. The geometric inputs are the existing terminal loss
and omitted-region bound. This strengthens the bookkeeping conclusion; it is
not an assumed stability estimate and does not assume S is contained in U.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaStability

/-- The surplus and missing area are paid by the deficit left after the cap. -/
theorem split_terminal_budget {S U : Set Point} {M c α : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤)
    (hc : 0 ≤ c) (hα : 0 ≤ α) (hmax : area U ≤ M)
    (hloss : area S ≤ area U - c * α)
    (hgain : area (S \ U) ≤ c * α) :
    0 ≤ M - area U ∧ M - area U ≤ M - area S ∧
      c * α ≤ (M - area S) - (M - area U) ∧
      area (S \ U) ≤ (M - area S) - (M - area U) ∧
      area (U \ S) ≤ 2 * ((M - area S) - (M - area U)) := by
  have hca : 0 ≤ c * α := mul_nonneg hc hα
  have hb := area_sdiff_balance hS hU hSf hUf
  refine ⟨sub_nonneg.mpr hmax, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- At a full-angle contained sofa there is no factor two in the missing budget. -/
theorem contained_missing_budget {S U : Set Point} (hSU : S ⊆ U)
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤) (M : ℝ) :
    area (U \ S) = (M - area S) - (M - area U) := by
  have hzero : S \ U = ∅ := sdiff_eq_empty.mpr hSU
  have hb := area_sdiff_balance hS hU hSf hUf
  rw [hzero] at hb
  simp only [area, measure_empty, ENNReal.toReal_zero, add_zero] at hb
  change (volume (U \ S)).toReal = _
  linarith

/-- A two-term Cauchy--Schwarz inequality, with its exact remainder. -/
theorem two_term_square_bound (a b x y : ℝ) :
    (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x)]

/-- Combine cap displacement and missing area in quadrature, not by giving
both contributions the entire deficit. -/
theorem split_sqrt_budget {ε e : ℝ} (he : 0 ≤ e) (heε : e ≤ ε) (a b : ℝ) :
    (a * sqrt e + b * sqrt (ε - e)) ^ 2 ≤ (a ^ 2 + b ^ 2) * ε := by
  have h := two_term_square_bound a b (sqrt e) (sqrt (ε - e))
  rw [sq_sqrt he, sq_sqrt (sub_nonneg.mpr heε)] at h
  simpa only [add_sub_cancel] using h

/-- A linear remainder affects the entry threshold, not any larger leading
square-root coefficient. This retains the original two-scale information. -/
theorem absorb_linear_remainder {A C B : ℝ} (hAC : A < C) (hB : 0 ≤ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      A * sqrt ε + B * ε ≤ C * sqrt ε := by
  let q := (C - A) / (B + 1)
  have hq : 0 < q := div_pos (sub_pos.mpr hAC) (by linarith)
  refine ⟨q ^ 2, sq_pos_of_pos hq, ?_⟩
  intro ε hε hsmall
  have hs : 0 ≤ sqrt ε := sqrt_nonneg ε
  have hs2 := sq_sqrt hε
  have hsq : sqrt ε ≤ q := by nlinarith
  have hqeq : (B + 1) * q = C - A := by
    dsimp [q]
    field_simp
  have hBq := mul_le_mul_of_nonneg_left hsq hB
  have hp := mul_le_mul_of_nonneg_right hBq hs
  nlinarith

end MovingSofaStability
