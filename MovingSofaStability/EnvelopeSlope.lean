module

public import MovingSofaStability.CurveRoof

/-!
# The niche envelope has a finite vertical slope bound

Uncompiled proof source. The two tails have slope at most two when their
angles stay within a quarter turn of the floor. On the compact middle arc,
the negative horizontal speed has a positive minimum. The three bounds are
joined at the actual matching endpoints.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

section Envelope

variable {t₁ t₂ t₃ t₄ sA sC : ℝ} {x : ℝ → Point} {α β ρA ρC : ℝ → ℝ}
variable (h : EnvHyp t₁ t₂ t₃ t₄ sA sC x α β ρA ρC)

theorem envelope_left_slope (ht₂ : t₂ < π / 4) :
    VerticalSlopeBound (envD x β '' Icc 0 t₂) 2 := by
  sorry

theorem envelope_right_slope (ht₃ : π / 4 < t₃) :
    VerticalSlopeBound (envB x α '' Icc t₃ (π / 2)) 2 := by
  sorry

/-- The middle arc is a Lipschitz graph because its horizontal speed is uniformly nonzero. -/
theorem envelope_core_slope : ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (x '' Icc t₁ t₄) L := by
  sorry

/-- The whole three-piece envelope inherits a single finite slope bound. -/
theorem envelope_slope_bound (ht₂ : t₂ < π / 4) (ht₃ : π / 4 < t₃) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (envCurve t₁ t₂ t₃ t₄ x α β) L := by
  sorry

end Envelope

end MovingSofaStability
