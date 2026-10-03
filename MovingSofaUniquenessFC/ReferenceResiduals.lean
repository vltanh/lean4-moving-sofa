module

public import MovingSofaUniquenessFC.ReferencePhiLocalization

/-!
# Residuals after reconstructing A and B

The equations used for uniqueness are F = eq3 and G = eq2 after substitution
of the exactly reconstructed coefficients. On the small-phi triangle,
H = G + (9/10) F will be nonincreasing in phi and strictly decreasing in theta,
whereas F is strictly decreasing in phi and nondecreasing in theta.
This supplies a two-variable order argument without an implicit-function
choice or a numerically checked Jacobian determinant.

This module proves only the displayed identities and derivatives. Their sign
bounds are proved separately. All source is uncompiled.
-/

@[expose] public section
noncomputable section

open Set Real

namespace MovingSofaUniquenessFC.Reference

def remainder (φ θ : ℝ) : ℝ := 1 - reconstructedA φ θ - gap φ θ

def firstResidual (φ θ : ℝ) : ℝ :=
  reconstructedA φ θ * cos φ - (reconstructedB φ θ + 1) * sin φ + (cos φ - 1) / 2

def secondResidual (φ θ : ℝ) : ℝ :=
  -3 * remainder φ θ * sin θ + (reconstructedA φ θ - 1) * sin φ +
    (1 - 2 * reconstructedB φ θ) * cos φ + 3 * cos θ

def separatingResidual (φ θ : ℝ) : ℝ := secondResidual φ θ + (9 / 10) * firstResidual φ θ

def armCoefficient (φ θ : ℝ) : ℝ := 3 * sin θ + sin φ - 2 * slope φ θ * cos φ

def firstPhi (φ θ : ℝ) : ℝ :=
  -reconstructedB φ θ * cos φ + reconstructedA φ θ * sin φ *
    (3 * cos φ + cos θ - 6 * slope φ θ * sin φ) / (2 * den φ θ)

def firstThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * frameDen φ θ / den φ θ + sin φ / 2

def secondPhi (φ θ : ℝ) : ℝ :=
  3 * reconstructedA φ θ * sin φ * armCoefficient φ θ / den φ θ +
    2 * reconstructedA φ θ * cos φ + 2 * reconstructedB φ θ * sin φ

def secondThetaFactor (φ θ : ℝ) : ℝ :=
  sin θ * armCoefficient φ θ / den φ θ + cos φ - 3 * cos θ

theorem firstResidual_eq (φ θ : ℝ) :
    firstResidual φ θ = eq3 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold firstResidual eq3
  ring

theorem secondResidual_eq (φ θ : ℝ) :
    secondResidual φ θ = eq2 (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  unfold secondResidual eq2 remainder gap
  ring

theorem Spec.residuals_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    firstResidual φ θ = 0 ∧ separatingResidual φ θ = 0 := by
  have hA := h.coefficients.1
  have hB := h.coefficients.2
  have h2 := (spec_iff.mp h).2.2.2.2.2.2.1
  have h3 := (spec_iff.mp h).2.2.2.2.2.2.2.1
  have hF : firstResidual φ θ = 0 := by
    rw [firstResidual_eq, ← hA, ← hB]
    exact h3
  have hG : secondResidual φ θ = 0 := by
    rw [secondResidual_eq, ← hA, ← hB]
    exact h2
  exact ⟨hF, by simp only [separatingResidual, hF, hG, mul_zero, add_zero]⟩

theorem reconstructedA_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => reconstructedA p θ)
      (1 + 3 * reconstructedA φ θ * sin φ / den φ θ) φ := by
  apply ((num_phi_deriv φ θ).div (den_phi_deriv φ θ) hD).congr_deriv
  unfold reconstructedA
  field_simp
  ring

theorem reconstructedA_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => reconstructedA φ t) (remainder φ θ * sin θ / den φ θ) θ := by
  apply ((num_theta_deriv φ θ).div (den_theta_deriv φ θ) hD).congr_deriv
  unfold remainder reconstructedA
  field_simp
  ring

theorem reconstructedB_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => reconstructedB p θ)
      (slope φ θ * (3 * reconstructedA φ θ * sin φ / den φ θ) -
        (reconstructedA φ θ + 1) / 2) φ := by
  apply (((reconstructedA_phi_deriv φ θ hD).mul (slope_phi_deriv φ θ)).add
    (offset_phi_deriv φ θ)).congr_deriv
  ring

theorem reconstructedB_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => reconstructedB φ t)
      (slope φ θ * (remainder φ θ * sin θ / den φ θ) - remainder φ θ / 2) θ := by
  apply (((reconstructedA_theta_deriv φ θ hD).mul (slope_theta_deriv φ θ)).add
    (offset_theta_deriv φ θ)).congr_deriv
  unfold remainder
  ring

theorem firstResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => firstResidual p θ) (firstPhi φ θ) φ := by
  have hd := (((reconstructedA_phi_deriv φ θ hD).mul (hasDerivAt_cos φ)).sub
    (((reconstructedB_phi_deriv φ θ hD).add_const 1).mul (hasDerivAt_sin φ))).add
      (((hasDerivAt_cos φ).sub_const 1).div_const 2)
  apply hd.congr_deriv
  unfold firstPhi
  field_simp
  unfold den
  ring

theorem firstResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => firstResidual φ t)
      (remainder φ θ * firstThetaFactor φ θ) θ := by
  have hd := (((reconstructedA_theta_deriv φ θ hD).mul_const (cos φ)).sub
    (((reconstructedB_theta_deriv φ θ hD).add_const 1).mul_const (sin φ))).add_const
      ((cos φ - 1) / 2)
  apply hd.congr_deriv
  unfold firstThetaFactor frameDen
  ring

theorem secondResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => secondResidual p θ) (secondPhi φ θ) φ := by
  have ha := reconstructedA_phi_deriv φ θ hD
  have hb := reconstructedB_phi_deriv φ θ hD
  have hr : HasDerivAt (fun p => remainder p θ)
      (-(3 * reconstructedA φ θ * sin φ / den φ θ)) φ :=
    ((ha.const_sub 1).sub ((hasDerivAt_id φ).const_sub θ)).congr_deriv (by ring)
  have hd := ((((hr.const_mul (-3)).mul_const (sin θ)).add
    ((ha.sub_const 1).mul (hasDerivAt_sin φ))).add
    (((hb.const_mul 2).const_sub 1).mul (hasDerivAt_cos φ))).add_const (3 * cos θ)
  apply hd.congr_deriv
  unfold secondPhi armCoefficient
  ring

theorem secondResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => secondResidual φ t)
      (remainder φ θ * secondThetaFactor φ θ) θ := by
  have ha := reconstructedA_theta_deriv φ θ hD
  have hb := reconstructedB_theta_deriv φ θ hD
  have hr : HasDerivAt (fun t => remainder φ t)
      (-remainder φ θ * sin θ / den φ θ - 1) θ :=
    ((ha.const_sub 1).sub ((hasDerivAt_id θ).sub_const φ)).congr_deriv (by ring)
  have hd := ((((hr.const_mul (-3)).mul (hasDerivAt_sin θ)).add
    ((ha.sub_const 1).mul_const (sin φ))).add
    (((hb.const_mul 2).const_sub 1).mul_const (cos φ))).add
      ((hasDerivAt_cos θ).const_mul 3)
  apply hd.congr_deriv
  unfold secondThetaFactor armCoefficient
  ring

/-- A denominator-free form of the last derivative factor. -/
theorem secondThetaFactor_identity (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    den φ θ * secondThetaFactor φ θ =
      3 + 3 * cos φ ^ 2 + sin φ * sin θ - 10 * cos φ * cos θ -
        2 * slope φ θ * cos φ * sin θ := by
  unfold secondThetaFactor armCoefficient
  field_simp [hD]
  unfold den
  linear_combination 3 * (sin_sq_add_cos_sq θ)

theorem separatingResidual_phi_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun p => separatingResidual p θ)
      (secondPhi φ θ + (9 / 10) * firstPhi φ θ) φ :=
  (secondResidual_phi_deriv φ θ hD).add ((firstResidual_phi_deriv φ θ hD).const_mul _)

theorem separatingResidual_theta_deriv (φ θ : ℝ) (hD : den φ θ ≠ 0) :
    HasDerivAt (fun t => separatingResidual φ t)
      (remainder φ θ * (secondThetaFactor φ θ + (9 / 10) * firstThetaFactor φ θ)) θ := by
  apply ((secondResidual_theta_deriv φ θ hD).add
    ((firstResidual_theta_deriv φ θ hD).const_mul (9 / 10))).congr_deriv
  ring

end MovingSofaUniquenessFC.Reference
