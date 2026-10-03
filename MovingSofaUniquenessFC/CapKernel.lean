module

public import SofaUniqueness.TangentKernel
import Mathlib.Tactic

/-!
# Matching the four cap equality equations

This is the scalar rigidity argument: once the four Mamikon equality equations
have been obtained for a support-function difference, their only freedom is a
horizontal translation. The conclusion gives the translation explicitly as
`-f π`.

The analytic hypotheses are stated, not inferred from an unproved cap theorem.
A geometric application must still establish the Mamikon equalities and the
piecewise differentiability of the support functions.
-/

@[expose] public section

open Real Set

namespace SofaUniqueness

/-- Match the tangent, outer-corner, tangent, and tangent equations in the order
fourth, third, second, first. The possible top-edge corner at `π/2` is allowed:
there is no differentiability hypothesis at that angle. -/
theorem cap_support_kernel {φ : ℝ} {f f' : ℝ → ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (π / 4))
    (hf : ContinuousOn f (Icc 0 π)) (htop : f (π / 2) = 0)
    (hd : ∀ t ∈ Ioo (0 : ℝ) π, t ≠ π / 2 → HasDerivAt f (f' t) t)
    (he₁ : ∀ t ∈ Ioo (0 : ℝ) φ,
      sin (π / 2 - t) * f' t + cos (π / 2 - t) * f t = f (π / 2))
    (he₂ : ∀ t ∈ Ioo φ (π / 2 - φ), f' t = f (t + π / 2))
    (he₃ : ∀ t ∈ Ioo (π / 2 - φ) (π / 2),
      sin (π - φ - t) * f' t + cos (π - φ - t) * f t = f (π - φ))
    (he₄ : ∀ t ∈ Ioo (π / 2) π,
      sin (π - t) * f' t + cos (π - t) * f t = f π) :
    EqOn f (fun t => -f π * cos t) (Icc 0 π) := by
  let a : ℝ := -f π
  have hπ := Real.pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hc : 0 < cos φ :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcont : ∀ {u v : ℝ}, 0 ≤ u → v ≤ π → ContinuousOn f (Icc u v) :=
    fun hu hv => hf.mono (Icc_subset_Icc hu hv)

  -- The fourth tangent term fixes the whole upper-left quadrant.
  have hs₄ : ∀ t ∈ Ioo (π / 2) π, sin (π - t) ≠ 0 := by
    intro t ht
    exact (sin_pos_of_pos_of_lt_pi (by linarith [ht.2])
      (by linarith [ht.1])).ne'
  have hd₄ : ∀ t ∈ Ioo (π / 2) π, HasDerivAt f (f' t) t := by
    intro t ht
    exact hd t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
  obtain ⟨C₄, h₄⟩ := tangent_solution_on_Icc
    (T := π) (A := f π) (by linarith : π / 2 < π)
    (hcont (by linarith) le_rfl) hs₄ hd₄ he₄
  have hC₄ : C₄ = 0 := by
    have h := h₄ (show π / 2 ∈ Icc (π / 2) π from ⟨le_rfl, by linarith⟩)
    rw [htop, show π - π / 2 = π / 2 by ring, cos_pi_div_two, sin_pi_div_two] at h
    nlinarith
  have hleft : ∀ t ∈ Icc (π / 2) π, f t = a * cos t := by
    intro t ht
    rw [h₄ ht, hC₄, zero_mul, add_zero, cos_pi_sub]
    dsimp only [a]
    ring

  -- The third term has a target strictly inside the quadrant just identified.
  have htarget : f (π - φ) = a * cos (π - φ) :=
    hleft (π - φ) ⟨by linarith, by linarith⟩
  have hs₃ : ∀ t ∈ Ioo (π / 2 - φ) (π / 2), sin (π - φ - t) ≠ 0 := by
    intro t ht
    exact (sin_pos_of_pos_of_lt_pi (by linarith [ht.2])
      (by linarith [ht.1])).ne'
  have hd₃ : ∀ t ∈ Ioo (π / 2 - φ) (π / 2), HasDerivAt f (f' t) t := by
    intro t ht
    exact hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by linarith [ht.2])
  obtain ⟨C₃, h₃⟩ := tangent_solution_on_Icc
    (T := π - φ) (A := f (π - φ)) (by linarith : π / 2 - φ < π / 2)
    (hcont (by linarith) (by linarith)) hs₃ hd₃ he₃
  have hC₃ : C₃ = a * sin φ := by
    have h := h₃ (show π / 2 ∈ Icc (π / 2 - φ) (π / 2) from ⟨by linarith, le_rfl⟩)
    rw [htop, htarget, show π - φ - π / 2 = π / 2 - φ by ring,
      cos_pi_div_two_sub, sin_pi_div_two_sub, cos_pi_sub] at h
    have hfactor : (C₃ - a * sin φ) * cos φ = 0 := by nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hc.ne')
  have hthird : ∀ t ∈ Icc (π / 2 - φ) (π / 2), f t = a * cos t := by
    intro t ht
    calc
      f t = f (π - φ) * cos (π - φ - t) + C₃ * sin (π - φ - t) := h₃ ht
      _ = a * (cos (π - φ) * cos (π - φ - t) +
          sin (π - φ) * sin (π - φ - t)) := by
        rw [htarget, hC₃, sin_pi_sub]
        ring
      _ = a * cos t := by rw [← cos_sub, sub_sub_cancel]

  -- The outer-corner equation transmits the translation through the middle.
  let F : ℝ → ℝ := fun t => f t - a * cos t
  have hFcont : ContinuousOn F (Icc φ (π / 2 - φ)) := by
    exact (hcont (by linarith) (by linarith)).sub
      ((Real.continuous_cos.const_mul a).continuousOn)
  have hFd : ∀ t ∈ Ioo φ (π / 2 - φ), HasDerivAt F 0 t := by
    intro t ht
    have hdf := hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by linarith [ht.2])
    have hshift : f (t + π / 2) = a * cos (t + π / 2) :=
      hleft (t + π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hzero : f' t - a * (-sin t) = 0 := by
      rw [he₂ t ht, hshift, cos_add_pi_div_two]
      ring
    exact (hdf.sub ((Real.hasDerivAt_cos t).const_mul a)).congr_deriv hzero
  have hFend : F (π / 2 - φ) = 0 := by
    dsimp only [F]
    rw [hthird (π / 2 - φ) ⟨le_rfl, by linarith⟩]
    ring
  have hmiddle : ∀ t ∈ Icc φ (π / 2 - φ), f t = a * cos t := by
    intro t ht
    have hEq := eq_endpoints_of_hasDerivAt_zero ht.2
      (hFcont.mono (Icc_subset_Icc ht.1 le_rfl))
      (fun z hz => hFd z ⟨lt_of_le_of_lt ht.1 hz.1, hz.2⟩)
    have hz : F t = 0 := hEq.symm.trans hFend
    exact sub_eq_zero.mp hz

  -- The first tangent term fixes the last remaining integration constant.
  have hs₁ : ∀ t ∈ Ioo (0 : ℝ) φ, sin (π / 2 - t) ≠ 0 := by
    intro t ht
    exact (sin_pos_of_pos_of_lt_pi (by linarith [ht.2])
      (by linarith [ht.1])).ne'
  have hd₁ : ∀ t ∈ Ioo (0 : ℝ) φ, HasDerivAt f (f' t) t := by
    intro t ht
    exact hd t ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2])
  obtain ⟨C₁, h₁⟩ := tangent_solution_on_Icc
    (T := π / 2) (A := f (π / 2)) hφ0
    (hcont le_rfl (by linarith)) hs₁ hd₁ he₁
  have hC₁ : C₁ = a := by
    have h := h₁ (show φ ∈ Icc (0 : ℝ) φ from ⟨hφ0.le, le_rfl⟩)
    rw [htop, zero_mul, zero_add, sin_pi_div_two_sub,
      hmiddle φ ⟨le_rfl, by linarith⟩] at h
    have hfactor : (C₁ - a) * cos φ = 0 := by nlinarith [h]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hc.ne')
  have hfirst : ∀ t ∈ Icc (0 : ℝ) φ, f t = a * cos t := by
    intro t ht
    rw [h₁ ht, htop, zero_mul, zero_add, sin_pi_div_two_sub, hC₁]

  change EqOn f (fun t => a * cos t) (Icc 0 π)
  intro t ht
  by_cases h₁ : t ≤ φ
  · exact hfirst t ⟨ht.1, h₁⟩
  by_cases h₂ : t ≤ π / 2 - φ
  · exact hmiddle t ⟨(not_le.mp h₁).le, h₂⟩
  by_cases h₃ : t ≤ π / 2
  · exact hthird t ⟨(not_le.mp h₂).le, h₃⟩
  · exact hleft t ⟨(not_le.mp h₃).le, ht.2⟩

end SofaUniqueness
