module

public import MovingSofaStability.PhaseAwareConstants
public import MovingSofaStability.BudgetedRecovery

/-!
# Numerical recovery from a small terminal surplus

Uncompiled proof source. The theorem below has explicit local geometric inputs
and an exact numerical coefficient. It is not the missing unconditional Gerver
reference specialization or a numerical global-entry certificate.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaStability

/-- Use the improved terminal gain, instead of losing a factor two in missing area. -/
theorem terminal_surplus_split {S U : Set Point} {M α : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S ≠ ⊤) (hUf : volume U ≠ ⊤)
    (hangle : α ≤ (31 / 10) * (area U - area S))
    (hgain : area (S \ U) ≤ α / 1000) :
    area (S \ U) ≤ (31 / 10000) * ((M - area S) - (M - area U)) ∧
      area (U \ S) ≤ (10031 / 10000) * ((M - area S) - (M - area U)) := by
  have hbal := area_sdiff_balance hS hU hSf hUf
  constructor <;> linarith

theorem reverse_budget_61_halves {ε e k : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) :
    sqrt 2 * k * sqrt e + sqrt (10031 / (10000 * π)) * sqrt (ε - e) <
      (100 / 1051) * ((61 / 2) * sqrt ε) := by
  have hfrac : (10031 / (10000 * π) : ℝ) < 10031 / 30000 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10000 * π)).mpr
    linarith [pi_gt_three]
  have hcoeff : 2 * k ^ 2 + 10031 / (10000 * π) < (29 / 10 : ℝ) ^ 2 := by nlinarith
  have h := split_sqrt_budget he heε (sqrt 2 * k) (sqrt (10031 / (10000 * π)))
  rw [mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_sqrt (by positivity : (0 : ℝ) ≤ 10031 / (10000 * π))] at h
  have hlt := mul_lt_mul_of_pos_right hcoeff hε
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε.le
  have hn : 0 ≤ sqrt 2 * k * sqrt e + sqrt (10031 / (10000 * π)) * sqrt (ε - e) := by positivity
  have hbound : sqrt 2 * k * sqrt e + sqrt (10031 / (10000 * π)) * sqrt (ε - e) <
      (29 / 10) * sqrt ε := by nlinarith
  have hrat : (29 / 10 : ℝ) < (100 / 1051) * (61 / 2) := by norm_num
  exact hbound.trans (by nlinarith [sqrt_pos.mpr hε])

/-- Actual-set reverse recovery, retaining both deficits and the explicit ratio. -/
theorem reverse_distance_61_halves_of_local_data {K₀ K S : Set Point} {r₀ ε e k δ : ℝ}
    (h₀ : IsCap K₀ (π / 2)) (hK : IsCap K (π / 2))
    (hballs : HasInteriorBalls (capShape K₀) (100 / 1051) r₀)
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500)
    (hδ : 0 ≤ δ) (hδbound : δ ≤ k * sqrt e)
    (hclose : UpperSupportClose δ K K₀)
    (hscale : (61 / 2) * sqrt ε ≤ r₀)
    (hmissing : area (capShape K \ S) ≤ (10031 / 10000) * (ε - e)) :
    DirectedClose ((61 / 2) * sqrt ε) (capShape K₀) S := by
  let r := sqrt 2 * δ
  let η := (10031 / 10000) * (ε - e)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hsqr : sqrt (η / π) = sqrt (10031 / (10000 * π)) * sqrt (ε - e) := by
    have heq : η / π = (10031 / (10000 * π)) * (ε - e) := by dsimp [η]; ring
    rw [heq, sqrt_mul (by positivity : (0 : ℝ) ≤ 10031 / (10000 * π))]
  have hroom : r + sqrt (η / π) < (100 / 1051) * ((61 / 2) * sqrt ε) := by
    have hcap := mul_le_mul_of_nonneg_left hδbound (sqrt_nonneg (2 : ℝ))
    rw [hsqr]
    have hbudget := reverse_budget_61_halves hε he heε hk0 hk
    dsimp [r]
    nlinarith
  obtain ⟨hradius, harea⟩ := residual_radius_area_condition hη hroom
  exact directedClose_of_residual_radius
    (show 0 < (61 / 2 : ℝ) * sqrt ε by positivity) hscale
    (show 0 ≤ r by dsimp [r]; positivity) hradius hballs
    (reference_erosion_subset_sqrt_two hδ h₀ hK hclose)
    (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
    hmissing harea

/-- Forward recovery needs much less than 30.5 after the linear remainder is kept linear. -/
theorem forward_budget_61_halves {ε e k B : ℝ}
    (hε : 0 < ε) (he : 0 ≤ e) (heε : e ≤ ε)
    (hk0 : 0 ≤ k) (hk : k ≤ 1001 / 500) (hB : 0 ≤ B)
    (hsmall : B * sqrt ε ≤ 1 / 2) :
    (51 / 5) * (k * sqrt e + B * (ε - e)) < (61 / 2) * sqrt ε := by
  have hs := sqrt_pos.mpr hε
  have hke := mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) hk0
  have hBe := mul_le_mul_of_nonneg_left (show ε - e ≤ ε by linarith) hB
  have hBsmall := mul_le_mul_of_nonneg_right hsmall hs.le
  have hs2 := sq_sqrt hε.le
  have hkl := mul_le_mul_of_nonneg_right hk hs.le
  nlinarith

/-- Primitive scalar version of the explicit outer-wall margin. -/
theorem explicit_outer_margin {D H s c v : ℝ}
    (hD : (4 / 5 : ℝ) ≤ D) (hH : H ≤ 2 / 3)
    (hs : 0 ≤ s) (hc : 0 ≤ c) (hunit : c ^ 2 + s ^ 2 = 1)
    (hv1 : D * c - H * s ≤ v) (hv2 : (1 - H) * s ≤ v) :
    (1 / 5 : ℝ) ≤ v := by
  have hDc := mul_le_mul_of_nonneg_right hD hc
  have hHs := mul_le_mul_of_nonneg_right hH hs
  by_contra hnot
  have hv : v < 1 / 5 := not_le.mp hnot
  have hsb : s < 3 / 5 := by nlinarith
  have hcb : c < 3 / 4 := by nlinarith
  nlinarith

/-- Exact rational downstream smallness checks. This does NOT show entry into
the local cap/terminal certificate regime for every sofa of this deficit. -/
theorem downstream_recovery_smallness {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : sqrt ε ≤ 1 / 10000000) :
    (1001 / 500) * sqrt ε + (248 / 5) * ε < 1 / 2040000 ∧
      (1001 / 500) * sqrt ε < 1 / 5 ∧
      (61 / 2) * sqrt ε < 1 / 24 ∧
      (248 / 5) * sqrt ε ≤ 1 / 2 ∧ sqrt ε ≤ 1 / 200 := by
  have hs := sqrt_nonneg ε
  have hs2 := sq_sqrt hε
  have hεsmall : ε ≤ (1 / 10000000 : ℝ) ^ 2 := by nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end MovingSofaStability
