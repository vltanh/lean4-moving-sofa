module

public import MovingSofaQuantitative.CenteredCap

/-!
# Consequences of a finite-deficit full-Q estimate

Uncompiled proof source. This module proves the exact power and infimum
arguments. Its main implications explicitly take `Targets.FullQFinite` or a
feasible-family theorem as inputs. They are not registered as unconditional
proofs of those still separate geometric/operator inputs.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- Taking a sixth root preserves a nonnegative power bound, including zero. -/
theorem rpow_sixth_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y ^ (6 : ℕ)) :
    x ^ (1 / 6 : ℝ) ≤ y := by
  calc
    _ ≤ (y ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := rpow_le_rpow hx hxy (by norm_num)
    _ = y := by
      rw [← rpow_natCast y 6, ← rpow_mul hy]
      norm_num

/-- The 2/3 remainder is a square-root term times a vanishing sixth root. -/
theorem rpow_two_thirds_factor {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 / 3 : ℝ) = sqrt x * x ^ (1 / 6 : ℝ) := by
  rcases hx.eq_or_lt with hz | hp
  · subst x
    norm_num
  · rw [sqrt_eq_rpow, ← rpow_add hp]
    congr 1
    norm_num

/-- An arbitrary coefficient larger than c is valid on an explicit scalar scale. -/
theorem absorb_two_thirds {x c C : ℝ} (hx : 0 ≤ x) (hC : c < C)
    (hsmall : x ≤ ((C - c) / 8) ^ (6 : ℕ)) :
    c * sqrt x + 8 * x ^ (2 / 3 : ℝ) ≤ C * sqrt x := by
  have hy : 0 ≤ (C - c) / 8 := by positivity
  have hr := rpow_sixth_le hx hy hsmall
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sqrt_nonneg x))
  rw [rpow_two_thirds_factor hx]
  nlinarith only [hm]

/-- The exact decimal corollary is rational: .93+.008 is below .94. -/
theorem fullQ_scalar_094 {x : ℝ} (hx : 0 ≤ x)
    (hsmall : x ≤ 1 / (10 : ℝ) ^ (18 : ℕ)) :
    (93 / 100) * sqrt x + 8 * x ^ (2 / 3 : ℝ) ≤ (94 / 100) * sqrt x := by
  have hpower : x ≤ (1 / 1000 : ℝ) ^ (6 : ℕ) := by
    norm_num at hsmall ⊢
    exact hsmall
  have hr := rpow_sixth_le hx (by norm_num : (0 : ℝ) ≤ 1 / 1000) hpower
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (sqrt_nonneg x))
  rw [rpow_two_thirds_factor hx]
  nlinarith [sqrt_nonneg x]

/-- Zero Q deficit gives zero geometric translation distance without a division. -/
theorem capTranslationDistance_eq_zero_of_qDeficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) (hz : qDeficit P x = 0) :
    capTranslationDistance P.cap x.1.1.1 = 0 := by
  have hclose := centered_cap P hP hbox x
  rw [hz, sqrt_zero, mul_zero] at hclose
  have hu : capTranslationDistance P.cap x.1.1.1 ≤ 0 :=
    capTranslationDistance_le_of_close le_rfl
      ⟨horizontalMidpoint x.1.1.1 - horizontalMidpoint P.cap, hclose⟩
  exact hu.antisymm (capTranslationDistance_formula (wideGerverTriple hP hbox).2.1 x.2.1).2.1

/-- Final .94 corollary once the actual .93 plus remainder theorem is supplied. -/
theorem fullQ094_of_finite (hfinite : Targets.FullQFinite) : Targets.FullQ094 := by
  intro P hP hbox x hΔ hsmall
  rcases hΔ.eq_or_lt with hz | hp
  · have he := capTranslationDistance_eq_zero_of_qDeficit hP hbox x hz.symm
    rw [he, ← hz, sqrt_zero, mul_zero]
  · have hrange : qDeficit P x ≤ 1 / 512 := hsmall.trans (by norm_num)
    exact (hfinite P hP hbox x hp hrange).trans (fullQ_scalar_094 hp.le hsmall)

/-- The infimum of eventual coefficients is at most .93, although the finite
estimate carries a positive higher-order remainder. -/
theorem intrinsic_upper_of_finite (hfinite : Targets.FullQFinite)
    {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    intrinsicQCoefficient P ≤ 93 / 100 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hc : (93 / 100 : ℝ) < 93 / 100 + δ := by linarith
  let η := min (1 / 512 : ℝ) (δ / 8) ^ (6 : ℕ)
  have hη : 0 < η := lt_min (by norm_num) (pow_pos (by positivity) _)
  have hmem : 93 / 100 + δ ∈ localQCoefficients P := by
    refine ⟨by positivity, η, hη, ?_⟩
    intro x hΔ hx
    have h1 : qDeficit P x ≤ 1 / 512 := hx.le.trans (min_le_left _ _)
    have h2 : qDeficit P x ≤ ((93 / 100 + δ - 93 / 100) / 8) ^ (6 : ℕ) := by
      simpa only [add_sub_cancel_left] using hx.le.trans (min_le_right _ _)
    exact (hfinite P hP hbox x hΔ h1).trans (absorb_two_thirds hΔ.le hc h2)
  exact csInf_le ⟨0, fun _ hh => hh.1⟩ hmem

/-- The uniform strict lower margin and the finite upper theorem give precisely
the advertised intrinsic interval; pointwise strict examples would not suffice. -/
theorem intrinsic_interval_of_bounds (hfinite : Targets.FullQFinite)
    (hlower : Targets.FeasibleCriticalLower) : Targets.IntrinsicInterval := by
  intro P hP hbox
  obtain ⟨L, hL, hfamily⟩ := hlower P hP hbox
  refine ⟨strict_intrinsic_lower_of_uniform_trial hP hbox hL ?_,
    intrinsic_upper_of_finite hfinite hP hbox⟩
  intro η hη
  obtain ⟨x, _, hpos, hsmall, hratio⟩ := hfamily η hη
  exact ⟨x, hpos, hsmall, hratio⟩

/-- A fixed rational margin supplied by every trial with energy below 147/125. -/
theorem feasible_trial_uniform_margin {E : ℝ} (hE : 0 ≤ E) (hupper : E ≤ 147 / 125) :
    (461 / 500 : ℝ) < 9221 / 10000 ∧ (9221 / 10000 : ℝ) * sqrt E < 1 := by
  refine ⟨by norm_num, ?_⟩
  have hs := sq_sqrt hE
  have hn := sqrt_nonneg E
  have hmul := mul_le_mul_of_nonneg_left hupper
    (by norm_num : (0 : ℝ) ≤ (9221 / 10000) ^ 2)
  have he := congrArg (fun x : ℝ => (9221 / 10000) ^ 2 * x) hs
  nlinarith only [hmul, he, hn]

end MovingSofaQuantitative
