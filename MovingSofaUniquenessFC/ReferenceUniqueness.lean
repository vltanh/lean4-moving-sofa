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

-- `hb0` belongs to the fixed statement; the proof does not need it.
set_option linter.unusedVariables false in
private theorem first_horizontal {b θ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    StrictAntiOn (fun p => firstResidual p θ) (Icc 0 b) := by
  have hd : ∀ p ∈ Icc 0 b,
      HasDerivAt (fun p => firstResidual p θ) (firstPhi p θ) p := by
    intro p hp
    exact firstResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne'
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hd p ⟨hp.1.le, hp.2.le⟩).deriv]
    have h := (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).firstPhi_le
    linarith

-- `hφθ` belongs to the fixed statement; the proof does not need it.
set_option linter.unusedVariables false in
private theorem first_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20)
    (hφθ : φ ≤ π / 4) : MonotoneOn (firstResidual φ) (Icc φ (π / 4)) := by
  have hd : ∀ t ∈ Icc φ (π / 4), HasDerivAt (firstResidual φ)
      (remainder φ t * firstThetaFactor φ t) t := by
    intro t ht
    exact firstResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
    have b := smallBounds hφ0 hφ1 ht.1.le ht.2.le
    exact mul_nonneg b.remainder_pos.le b.firstThetaFactor_bounds.1

-- `hb0` belongs to the fixed statement; the proof does not need it.
set_option linter.unusedVariables false in
private theorem separating_horizontal {b θ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 20) (hbθ : b ≤ θ) (hθ : θ ≤ π / 4) :
    AntitoneOn (fun p => separatingResidual p θ) (Icc 0 b) := by
  have hd : ∀ p ∈ Icc 0 b, HasDerivAt (fun p => separatingResidual p θ)
      (secondPhi p θ + (9 / 10) * firstPhi p θ) p := by
    intro p hp
    exact separatingResidual_phi_deriv p θ (den_pos hp.1 (hp.2.trans hbθ) hθ).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · intro p hp
    exact (hd p (interior_subset hp)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hd p ⟨hp.1.le, hp.2.le⟩).deriv]
    exact (smallBounds hp.1.le (hp.2.le.trans hb1) (hp.2.le.trans hbθ) hθ).separating_signs.1

-- `hφθ` belongs to the fixed statement; the proof does not need it.
set_option linter.unusedVariables false in
private theorem separating_vertical {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 20)
    (hφθ : φ ≤ π / 4) : StrictAntiOn (separatingResidual φ) (Icc φ (π / 4)) := by
  have hd : ∀ t ∈ Icc φ (π / 4), HasDerivAt (separatingResidual φ)
      (remainder φ t * (secondThetaFactor φ t + (9 / 10) * firstThetaFactor φ t)) t := by
    intro t ht
    exact separatingResidual_theta_deriv φ t (den_pos hφ0 ht.1 ht.2).ne'
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact (smallBounds hφ0 hφ1 ht.1.le ht.2.le).separating_signs.2

/-- Two roots cannot be strictly ordered in their second coordinate. -/
private theorem not_theta_lt {A B φ θ A' B' φ' θ' : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ' θ') : ¬ θ < θ' := by
  intro htt
  have hp0 := h.phi_pos.le
  have hp1 := h.phi_lt_twentieth.le
  have hpθ := h.phi_lt_theta.le
  have ht1 := h.2.2.1
  have hp'0 := h'.phi_pos.le
  have hp'1 := h'.phi_lt_twentieth.le
  have hp'θ := h'.phi_lt_theta.le
  have ht'1 := h'.2.2.1
  obtain ⟨hF, hH⟩ := h.residuals_zero
  obtain ⟨hF', hH'⟩ := h'.residuals_zero
  have hFgrow : 0 ≤ firstResidual φ θ' := by
    have hh := first_vertical hp0 hp1 (hpθ.trans ht1)
      ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt.le
    rwa [hF] at hh
  have hpp : φ ≤ φ' := by
    by_contra hn
    have hlt : φ' < φ := lt_of_not_ge hn
    have hh : firstResidual φ θ' < firstResidual φ' θ' :=
      first_horizontal hp0 hp1 (hpθ.trans htt.le) ht'1 ⟨hp'0, hlt.le⟩ ⟨hp0, le_rfl⟩ hlt
    rw [hF'] at hh
    linarith
  have hHshrink : separatingResidual φ θ' < 0 := by
    have hh := separating_vertical hp0 hp1 (hpθ.trans ht1)
      ⟨hpθ, ht1⟩ ⟨hpθ.trans htt.le, ht'1⟩ htt
    rwa [hH] at hh
  have hHphi : separatingResidual φ' θ' ≤ separatingResidual φ θ' :=
    separating_horizontal hp'0 hp'1 hp'θ ht'1 ⟨hp0, hpp⟩ ⟨hp'0, le_rfl⟩ hpp
  rw [hH'] at hHphi
  linarith

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
