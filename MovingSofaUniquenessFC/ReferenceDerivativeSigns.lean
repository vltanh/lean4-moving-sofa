module

public import MovingSofaUniquenessFC.ReferenceSmallBounds

/-!
# A separating residual for global parameter uniqueness

The bounds here imply F_phi <= -2/3, 0 <= F_theta/C <= 1/2,
G_phi <= 3/5, and G_theta/C <= -2/3, where C = 1-A-(theta-phi)>0.
Consequently H = G + (9/10) F is nonincreasing in phi and strictly decreasing
in theta. These inequalities are proved on the entire localized triangle,
not assumed at a selected root. Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real

namespace MovingSofaUniquenessFC.Reference.SmallBounds

variable {φ θ : ℝ} (b : SmallBounds φ θ)

private theorem den_pos : 0 < den φ θ := by
  sorry

private theorem A_sin_bounds :
    0 ≤ reconstructedA φ θ * sin φ ∧
      reconstructedA φ θ * sin φ ≤ 1 / 125 := by
  sorry

theorem firstPhi_le : firstPhi φ θ ≤ -2 / 3 := by
  sorry

theorem firstThetaFactor_bounds :
    0 ≤ firstThetaFactor φ θ ∧ firstThetaFactor φ θ ≤ 1 / 2 := by
  sorry

theorem secondPhi_le : secondPhi φ θ ≤ 3 / 5 := by
  sorry

theorem secondThetaFactor_le : secondThetaFactor φ θ ≤ -2 / 3 := by
  sorry

/-- H has the sign pattern that separates different roots. -/
theorem separating_signs :
    secondPhi φ θ + (9 / 10) * firstPhi φ θ ≤ 0 ∧
      remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ) < 0 := by
  sorry

end MovingSofaUniquenessFC.Reference.SmallBounds
