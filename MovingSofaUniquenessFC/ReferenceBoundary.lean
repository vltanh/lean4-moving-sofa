module

public import MovingSofaUniquenessFC.ReferenceEquations

/-!
# Exclude degenerate boundaries of the upstream parameter domain

These arguments use elementary differentiation and the four defining equations,
not interval-certificate evaluation. They apply to the full upstream domain,
including its initially non-strict inequalities. The later analytic localization
and residual-separation modules use these nondegenerate bounds.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaUniquenessFC.Reference

/-- The upstream system has no solution with phi equal to zero. -/
theorem Spec.phi_pos {A B φ θ : ℝ} (h : Spec A B φ θ) : 0 < φ := by
  obtain ⟨hφ, horder, hθ, hAnonneg, hBnonneg, h1, h2, h3, h4⟩ := spec_iff.mp h
  by_contra hnot
  have hφzero : φ = 0 := le_antisymm (le_of_not_gt hnot) hφ
  subst φ
  have hAzero : A = 0 := by simpa [eq3] using h3
  have hθpos : 0 < θ := by
    by_contra hn
    have hθzero : θ = 0 := le_antisymm (le_of_not_gt hn) horder
    subst θ
    have hBtwo : B = 2 := by
      simp [eq2, hAzero] at h2
      linarith
    have hπfour : π = 4 := by
      simp [eq4, hAzero, hBtwo] at h4
      linarith
    linarith [pi_lt_four]
  let f : ℝ → ℝ := fun t => (t - 1) * cos t - sin t + 1
  have hf' (t : ℝ) : HasDerivAt f ((1 - t) * sin t) t := by
    convert (((((hasDerivAt_id t).sub_const 1).mul (hasDerivAt_cos t)).sub
      (hasDerivAt_sin t)).add_const 1) using 1 <;> dsimp [f]
    ring
  have hθone : θ < 1 := by linarith [pi_lt_four]
  have hstrict : StrictMonoOn f (Icc 0 θ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 θ)
    · exact fun t _ => (hf' t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hf' t).deriv]
      apply mul_pos
      · linarith [ht.2]
      · exact sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hzero : f 0 = 0 := by simp [f]
  have hlast : f θ = 0 := by
    simpa [f, eq1, hAzero] using h1
  have hlt := hstrict ⟨le_rfl, hθpos.le⟩ ⟨hθpos.le, le_rfl⟩ hθpos
  rw [hzero, hlast] at hlt
  exact (lt_irrefl (0 : ℝ)) hlt

/-- The diagonal phi=theta is also impossible under the original domain. -/
theorem Spec.phi_lt_theta {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < θ := by
  have hφpos := h.phi_pos
  obtain ⟨hφ, horder, hθ, hAnonneg, hBnonneg, h1, h2, h3, h4⟩ := spec_iff.mp h
  rcases lt_or_eq_of_le horder with hlt | heq
  · exact hlt
  · subst θ
    have hsin : 0 < sin φ :=
      sin_pos_of_pos_of_lt_pi hφpos (by linarith [pi_pos])
    have hid : eq1 A B φ φ = -2 * (B * sin φ) := by
      unfold eq1
      ring
    have hBprod : B * sin φ = 0 := by
      rw [hid] at h1
      linarith
    have hBzero : B = 0 := (mul_eq_zero.mp hBprod).resolve_right hsin.ne'
    have hAnonpos : A ≤ 0 := by
      unfold eq4 at h4
      rw [hBzero] at h4
      nlinarith
    have hAzero : A = 0 := le_antisymm hAnonpos hAnonneg
    have hc := cos_le_one φ
    simp only [eq3, hAzero, hBzero, zero_mul, add_zero] at h3
    exfalso
    linarith

/-- Nondegeneracy on the original full domain. -/
theorem Spec.strict_order {A B φ θ : ℝ} (h : Spec A B φ θ) :
    0 < φ ∧ φ < θ ∧ θ ≤ π / 4 :=
  ⟨h.phi_pos, h.phi_lt_theta, h.2.2.1⟩

end MovingSofaUniquenessFC.Reference
