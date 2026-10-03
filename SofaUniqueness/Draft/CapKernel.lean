module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-!
# UNCOMPILED DRAFT: matching the four Mamikon equality intervals

This file proves the algebraic/integral propagation step independently of caps.
The analytic obligation of deriving `CapKernel` from vanishing Mamikon gaps is
kept separately in `PaperReductions.lean`. `CapKernel` is input data, not an axiom
or a typeclass with an asserted global instance.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory

namespace SofaUniqueness.Draft

/-- The solved first-order equation of a tangent term, including its target value.
The target can lie outside the interval on which the equation was solved. -/
def TangentKernel (f : ℝ → ℝ) (a b T : ℝ) : Prop :=
  ∃ p q : ℝ, EqOn f (fun t => p * cos t + q * sin t) (Icc a b) ∧
    f T = p * cos T + q * sin T

/-- Consequences of the four separate zero square gaps.

The middle relation is an integral identity, so no unjustified pointwise
classical derivative or differentiability at the top support is assumed. -/
structure CapKernel (φ : ℝ) (f : ℝ → ℝ) : Prop where
  top : f (π / 2) = 0
  first : TangentKernel f 0 φ (π / 2)
  middle : ∀ t ∈ Icc φ (π / 2 - φ),
    f t = f (π / 2 - φ) - ∫ u in t..(π / 2 - φ), f (u + π / 2)
  third : TangentKernel f (π / 2 - φ) (π / 2) (π - φ)
  fourth : TangentKernel f (π / 2) π π

/-- The upper-left quadrant is determined by the top value. -/
theorem CapKernel.upper_left {φ : ℝ} {f : ℝ → ℝ} (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc (π / 2) π) := by
  obtain ⟨p, q, heq, hπ⟩ := h.fourth
  have hL := heq (x := π / 2) ⟨le_rfl, by linarith [pi_pos]⟩
  have hq : q = 0 := by simpa [h.top] using hL.symm
  have hp : p = -f π := by
    simp only [cos_pi, sin_pi, mul_neg_one, mul_zero, add_zero] at hπ
    linarith
  intro t ht
  simpa [hp, hq] using heq ht

/-- Equality in the four cap terms has only the horizontal-translation mode. -/
theorem CapKernel.eq_horizontal_translation {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc 0 π) := by
  set a : ℝ := -f π
  have hleft : EqOn f (fun t => a * cos t) (Icc (π / 2) π) := h.upper_left
  have hcos : cos φ ≠ 0 := (cos_pos_of_mem_Ioo
    ⟨by linarith [pi_pos, hφ.1], by linarith [hφ.2, pi_pos]⟩).ne'
  have hT : cos (π - φ) ≠ 0 := by simpa [cos_pi_sub] using hcos
  have hψ : φ ≤ π / 2 - φ := by linarith [hφ.2]
  have hthird : EqOn f (fun t => a * cos t) (Icc (π / 2 - φ) (π / 2)) := by
    obtain ⟨p, q, heq, htarget⟩ := h.third
    have hL := heq (x := π / 2) ⟨by linarith [hφ.1], le_rfl⟩
    have hq : q = 0 := by simpa [h.top] using hL.symm
    have htarget' := hleft (x := π - φ)
      ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩
    have hpa : p = a := by
      have he : p * cos (π - φ) = a * cos (π - φ) := by
        simpa [hq] using htarget.symm.trans htarget'
      exact (mul_right_cancel₀ hT) he
    intro t ht
    simpa [hpa, hq] using heq ht
  have hmiddle : EqOn f (fun t => a * cos t) (Icc φ (π / 2 - φ)) := by
    intro t ht
    have hi : (∫ u in t..(π / 2 - φ), f (u + π / 2)) =
        a * (cos (π / 2 - φ) - cos t) := by
      calc
        _ = ∫ u in t..(π / 2 - φ), -a * sin u := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le ht.2] at hu
          show f (u + π / 2) = -a * sin u
          rw [hleft (x := u + π / 2) ⟨by linarith [hu.1, ht.1, hφ.1],
            by linarith [hu.2, hφ.1]⟩]
          simp only [cos_add_pi_div_two]
          ring
        _ = -a * (cos t - cos (π / 2 - φ)) := by
          rw [intervalIntegral.integral_const_mul, integral_sin]
        _ = _ := by ring
    rw [h.middle t ht, hi,
      hthird (x := π / 2 - φ) ⟨le_rfl, by linarith [hφ.1]⟩]
    ring
  have hfirst : EqOn f (fun t => a * cos t) (Icc 0 φ) := by
    obtain ⟨p, q, heq, htarget⟩ := h.first
    have hq : q = 0 := by simpa [h.top] using htarget.symm
    have he := heq (x := φ) ⟨hφ.1.le, le_rfl⟩
    have hm := hmiddle (x := φ) ⟨le_rfl, hψ⟩
    have hp : p = a := by
      have he' : p * cos φ = a * cos φ := by simpa [hq] using he.symm.trans hm
      exact (mul_right_cancel₀ hcos) he'
    intro t ht
    simpa [hp, hq] using heq ht
  intro t ht
  by_cases hL : π / 2 ≤ t
  · exact hleft ⟨hL, ht.2⟩
  by_cases hψt : π / 2 - φ ≤ t
  · exact hthird ⟨hψt, (not_le.mp hL).le⟩
  by_cases hφt : φ ≤ t
  · exact hmiddle ⟨hφt, (not_le.mp hψt).le⟩
  · exact hfirst ⟨ht.1, (not_le.mp hφt).le⟩

/-- A normalization fixing the left support eliminates the remaining mode. -/
theorem CapKernel.eq_zero_of_left_support {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) (hπ : f π = 0) :
    EqOn f (fun _ => 0) (Icc 0 π) := by
  intro t ht
  simpa [hπ] using h.eq_horizontal_translation hφ ht

/-- All horizontal translations satisfy the full kernel data, including the
middle integral identity. This checks the sign and the remaining degree of freedom. -/
theorem capKernel_translation (φ a : ℝ) : CapKernel φ (fun t => a * cos t) := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · exact ⟨a, 0, fun _ _ => by simp, by simp⟩
  · intro t _
    have he : (fun u : ℝ => a * cos (u + π / 2)) = fun u => -a * sin u := by
      funext u
      rw [cos_add_pi_div_two]
      ring
    rw [he, intervalIntegral.integral_const_mul, integral_sin]
    ring
  · exact ⟨a, 0, fun _ _ => by simp, by simp⟩
  · exact ⟨a, 0, fun _ _ => by simp, by simp⟩

end SofaUniqueness.Draft
