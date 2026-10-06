module

public import MovingSofaStability.SharpKernelNorms

/-!
# Sharp evaluation of the four residuals

Uncompiled proof source. Kernel norms and residual energies are kept separate.
The two pieces of r4 on the middle arc are recombined using their disjoint
integration intervals, so the same energy is not counted twice.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

section Evaluation

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (H : FourResidualData φ f df)

theorem sharp_last_control {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    SquareControl (f t) (-sin t * cos t) (arcSquare (π / 2) π (tangentResidual π f df)) := by
  sorry

theorem sharp_third_control {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    SquareControl (f t) (sin t * cos t + 2 * tan φ * cos t ^ 2)
      (arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  sorry

theorem sharp_middle_control {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    SquareControl (f t) (cos t * (2 / cos φ - sin t))
      (arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  sorry

theorem sharp_first_control {t : ℝ} (ht : t ∈ Icc 0 φ) :
    SquareControl (f t) (cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t))
      (2 * fourResidualEnergy φ f df) := by
  sorry

/-- The actual square-integral norm at every evaluation point. -/
theorem sharp_green_control {t : ℝ} (ht : t ∈ Icc 0 π) :
    SquareControl (f t) (greenNormSquared φ t) (2 * fourResidualEnergy φ f df) := by
  sorry

/-- The coefficient is 2/cos(phi), not the earlier non-sharp 80. -/
theorem sharp_four_arc_coercivity {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t| ≤ (2 / cos φ) * sqrt (fourResidualEnergy φ f df) := by
  sorry

end Evaluation
end MovingSofaStability
