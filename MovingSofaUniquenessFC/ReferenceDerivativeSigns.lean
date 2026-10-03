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
include b

private theorem den_pos : 0 < den φ θ := by linarith [b.den_mem.1]

private theorem A_sin_bounds :
    0 ≤ reconstructedA φ θ * sin φ ∧
      reconstructedA φ θ * sin φ ≤ 1 / 125 := by
  refine ⟨mul_nonneg b.A_mem.1 b.sin_phi.1, ?_⟩
  have h := mul_le_mul b.A_mem.2 b.sin_phi.2 b.sin_phi.1
    (by norm_num : (0 : ℝ) ≤ 4 / 25)
  norm_num at h
  exact h

theorem firstPhi_le : firstPhi φ θ ≤ -2 / 3 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hks : 0 ≤ slope φ θ * sin φ :=
    mul_nonneg (by linarith [b.slope_mem.1]) b.sin_phi.1
  have hT : 3 * cos φ + cos θ - 6 * slope φ θ * sin φ ≤ 4 := by
    linarith [b.cos_phi.2, b.cos_theta.2]
  have hnum : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) ≤ 4 / 125 := by
    have h := mul_le_mul_of_nonneg_left hT has0
    nlinarith
  have hcor : reconstructedA φ θ * sin φ *
      (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ) ≤ 1 / 100 := by
    apply (div_le_iff₀ (show 0 < 2 * den φ θ by linarith [b.den_pos])).mpr
    linarith [b.den_mem.1]
  have hmain : (7 / 10 : ℝ) * (499 / 500) ≤ reconstructedB φ θ * cos φ := by
    apply mul_le_mul b.B_mem.1 b.cos_phi.1 (by norm_num)
    linarith [b.B_mem.1]
  unfold firstPhi
  linarith

theorem firstThetaFactor_bounds :
    0 ≤ firstThetaFactor φ θ ∧ firstThetaFactor φ θ ≤ 1 / 2 := by
  have hJ0 : 0 ≤ frameDen φ θ := by linarith [b.frame_mem.1]
  have hquot0 := div_nonneg (mul_nonneg b.sin_theta.1 hJ0) b.den_pos.le
  have hnum : sin θ * frameDen φ θ ≤ 4 / 5 := by
    have h := mul_le_mul_of_nonneg_left b.frame_mem.2 b.sin_theta.1
    nlinarith [b.sin_theta.2]
  have hquot : sin θ * frameDen φ θ / den φ θ ≤ 9 / 20 := by
    apply (div_le_iff₀ b.den_pos).mpr
    linarith [b.den_mem.1]
  unfold firstThetaFactor
  constructor <;> linarith [b.sin_phi.1, b.sin_phi.2]

theorem secondPhi_le : secondPhi φ θ ≤ 3 / 5 := by
  obtain ⟨has0, has1⟩ := b.A_sin_bounds
  have hkcos : 0 ≤ slope φ θ * cos φ :=
    mul_nonneg (by linarith [b.slope_mem.1]) (by linarith [b.cos_phi.1])
  have hH : armCoefficient φ θ ≤ 5 / 2 := by
    unfold armCoefficient
    linarith [b.sin_theta.2, b.sin_phi.2]
  have hnum : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ ≤ 3 / 50 := by
    have h := mul_le_mul_of_nonneg_left hH (show 0 ≤ 3 * reconstructedA φ θ * sin φ by nlinarith)
    nlinarith
  have hquot : 3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ ≤ 1 / 25 := by
    apply (div_le_iff₀ b.den_pos).mpr
    linarith [b.den_mem.1]
  have hac : reconstructedA φ θ * cos φ ≤ 4 / 25 := by
    have h := mul_le_mul_of_nonneg_left b.cos_phi.2 b.A_mem.1
    nlinarith [b.A_mem.2]
  have hbs : reconstructedB φ θ * sin φ ≤ 1 / 10 := by
    have h := mul_le_mul b.B_mem.2 b.sin_phi.2 b.sin_phi.1 (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  unfold secondPhi
  linarith

theorem secondThetaFactor_le : secondThetaFactor φ θ ≤ -2 / 3 := by
  have hD := b.den_pos
  have hid := secondThetaFactor_identity φ θ hD.ne'
  have hc0 : 0 ≤ cos φ := by linarith [b.cos_phi.1]
  have hcSq : cos φ ^ 2 ≤ 1 := by nlinarith [b.cos_phi.1, b.cos_phi.2]
  have hsmall : sin φ * sin θ ≤ sin θ / 20 := by
    have h := mul_le_mul_of_nonneg_right b.sin_phi.2 b.sin_theta.1
    nlinarith
  have hcos : (499 / 50 : ℝ) * cos θ ≤ 10 * cos φ * cos θ := by
    have h := mul_le_mul_of_nonneg_right b.cos_phi.1
      (show 0 ≤ cos θ by linarith [b.cos_theta.1])
    nlinarith
  have hkc : (499 / 500 : ℝ) ≤ slope φ θ * cos φ := by
    have h := mul_le_mul_of_nonneg_right b.slope_mem.1 hc0
    nlinarith [b.cos_phi.1]
  have hsin : (499 / 250 : ℝ) * sin θ ≤ 2 * slope φ θ * cos φ * sin θ := by
    have h := mul_le_mul_of_nonneg_right hkc b.sin_theta.1
    nlinarith
  have hsum : (37849 / 5000 : ℝ) ≤ (499 / 50) * cos θ + (973 / 500) * sin θ := by
    nlinarith [b.trig_sum, b.cos_theta.1]
  have hnum : den φ θ * secondThetaFactor φ θ ≤ -7849 / 5000 := by
    nlinarith
  apply (mul_le_mul_iff_right₀ hD).mp
  nlinarith [b.den_mem.2]

/-- H has the sign pattern that separates different roots. -/
theorem separating_signs :
    secondPhi φ θ + (9 / 10) * firstPhi φ θ ≤ 0 ∧
      remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ) < 0 := by
  have hF := b.firstPhi_le
  have hFt := b.firstThetaFactor_bounds.2
  have hG := b.secondPhi_le
  have hGt := b.secondThetaFactor_le
  refine ⟨by linarith, mul_neg_of_pos_of_neg b.remainder_pos (by linarith)⟩

end MovingSofaUniquenessFC.Reference.SmallBounds
