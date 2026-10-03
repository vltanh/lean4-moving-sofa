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
  sorry

/-- Equality in the four cap terms has only the horizontal-translation mode. -/
theorem CapKernel.eq_horizontal_translation {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc 0 π) := by
  sorry

/-- A normalization fixing the left support eliminates the remaining mode. -/
theorem CapKernel.eq_zero_of_left_support {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) (hπ : f π = 0) :
    EqOn f (fun _ => 0) (Icc 0 π) := by
  sorry

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
