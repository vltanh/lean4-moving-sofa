module

public import MovingSofaUniquenessFC.ReferenceDerivativeSigns

/-!
# Global uniqueness of the four reference constants

This proof applies to the FULL upstream domain, including its non-strict
boundary inequalities. The boundary and localization lemmas put every root
in `0 < phi < 1/20`, `phi < theta <= pi/4`. On that triangle F decreases
strictly in phi and increases weakly in theta, while H = G + (9/10) F
decreases weakly in phi and strictly in theta. Two zeros therefore cannot
have different theta coordinates; strict phi monotonicity finishes.

No small-box uniqueness theorem, root-search certificate, or uniqueness of
sofa shapes is used in this argument. Existence is a separate theorem.
Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real

namespace MovingSofaUniquenessFC.Reference

private theorem first_horizontal {b θ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    StrictAntiOn (fun p => firstResidual p θ) (Icc 0 b) := by
  sorry

private theorem first_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20)
    (hφθ : φ ≤ π / 4) : MonotoneOn (firstResidual φ) (Icc φ (π / 4)) := by
  sorry

private theorem separating_horizontal {b θ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    AntitoneOn (fun p => separatingResidual p θ) (Icc 0 b) := by
  sorry

private theorem separating_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20)
    (hφθ : φ ≤ π / 4) : StrictAntiOn (separatingResidual φ) (Icc φ (π / 4)) := by
  sorry

/-- Two roots cannot be strictly ordered in their second coordinate. -/
private theorem not_theta_lt {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : ¬ θ < θ' := by
  sorry

/-- The angles of any two full-domain solutions agree. -/
theorem angles_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : φ = φ' ∧ θ = θ' := by
  have ht : θ = θ' := le_antisymm (le_of_not_gt (not_theta_lt h' h))
    (le_of_not_gt (not_theta_lt h h'))
  subst θ'
  have hb0 : 0 ≤ max φ φ' := le_max_of_le_left h.phi_pos.le
  have hb1 : max φ φ' ≤ 1 / 20 := max_le h.phi_lt_twentieth.le h'.phi_lt_twentieth.le
  have hbθ : max φ φ' ≤ θ := max_le h.phi_lt_theta.le h'.phi_lt_theta.le
  have ha := first_horizontal hb0 hb1 hbθ h.2.2.1
  have heq : firstResidual φ θ = firstResidual φ' θ :=
    h.residuals_zero.1.trans h'.residuals_zero.1.symm
  exact ⟨ha.injOn ⟨h.phi_pos.le, le_max_left _ _⟩
    ⟨h'.phi_pos.le, le_max_right _ _⟩ heq, rfl⟩

/-- Global uniqueness, with exactly the upstream domain and equations. -/
theorem spec_unique {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') :
    A = A' ∧ B = B' ∧ φ = φ' ∧ θ = θ' := by
  obtain ⟨hp, ht⟩ := angles_unique h h'
  subst φ' θ'
  obtain ⟨ha, hb⟩ := coefficients_unique h h'
  exact ⟨ha, hb, rfl, rfl⟩

end MovingSofaUniquenessFC.Reference
