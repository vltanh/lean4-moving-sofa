module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# The kernel of the tangent-displacement equation

On an open interval on which `sin (T - t)` does not vanish, the equation

`sin (T - t) * f'(t) + cos (T - t) * f(t) = A`

has the complete family `f(t) = A * cos (T - t) + C * sin (T - t)`.

The derivative calculation and constancy argument take place strictly inside the
interval. Continuity then extends the answer to both endpoints. In particular,
the final tangent interval may end at `T`: no division by `sin 0` is made there.

These lemmas assume pointwise differentiability on the open interval. Applying
them to a cap still requires deriving those hypotheses from its regularity and
from the almost-everywhere Mamikon equality; that step is not hidden here.
-/

@[expose] public section

open Real Set

namespace SofaUniqueness

/-- A real function with zero derivative inside a closed interval has equal
endpoint values. No differentiability at either endpoint is required. -/
theorem eq_endpoints_of_hasDerivAt_zero {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) : f b = f a := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    rfl
  · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) h hf hd
    have hmul := (eq_div_iff (sub_ne_zero.mpr h.ne')).mp he
    have hzero : f b - f a = 0 := by linarith
    exact sub_eq_zero.mp hzero

/-- Constancy on an open interval, proved by applying the mean value theorem
only to closed subintervals strictly inside it. -/
theorem eqOn_const_of_hasDerivAt_zero {a b t₀ : ℝ} {f : ℝ → ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) :
    EqOn f (fun _ => f t₀) (Ioo a b) := by
  have H : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y → f y = f x := by
    intro x hx y hy hxy
    have hmem : ∀ z ∈ Icc x y, z ∈ Ioo a b := by
      intro z hz
      exact ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
    apply eq_endpoints_of_hasDerivAt_zero hxy
    · intro z hz
      exact (hd z (hmem z hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact hd z (hmem z ⟨hz.1.le, hz.2.le⟩)
  intro t ht
  rcases le_total t t₀ with h | h
  · exact (H t ht t₀ ht₀ h).symm
  · exact H t₀ ht₀ t ht h

/-- An integrating factor for the tangent equality equation. Its total
real-valued definition is used only where the denominator is nonzero. -/
noncomputable def tangentInvariant (T A : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - A * cos (T - t)) / sin (T - t)

/-- The integrating factor has zero derivative wherever the tangent equation
holds and the denominator is nonzero. -/
theorem tangentInvariant_hasDerivAt_zero {T A t D : ℝ} {f : ℝ → ℝ}
    (hf : HasDerivAt f D t) (hs : sin (T - t) ≠ 0)
    (he : sin (T - t) * D + cos (T - t) * f t = A) :
    HasDerivAt (tangentInvariant T A f) 0 t := by
  have harg : HasDerivAt (fun s : ℝ => T - s) (-1) t :=
    (hasDerivAt_id t).const_sub T
  have hcos : HasDerivAt (fun s : ℝ => cos (T - s)) (sin (T - t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using
      (Real.hasDerivAt_cos (T - t)).comp t harg
  have hsin : HasDerivAt (fun s : ℝ => sin (T - s)) (-cos (T - t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_sin (T - t)).comp t harg
  have hnum : (D - A * sin (T - t)) * sin (T - t) -
      (f t - A * cos (T - t)) * (-cos (T - t)) = 0 := by
    linear_combination he - A * (Real.sin_sq_add_cos_sq (T - t))
  have hquot := (hf.sub (hcos.const_mul A)).div hsin hs
  have hd := hquot.congr_deriv (by rw [hnum, zero_div])
  simpa only [tangentInvariant] using hd

/-- Recover the function from a constant integrating factor at one point. -/
theorem tangent_eq_of_invariant_eq {T A t C : ℝ} {f : ℝ → ℝ}
    (hs : sin (T - t) ≠ 0) (he : tangentInvariant T A f t = C) :
    f t = A * cos (T - t) + C * sin (T - t) := by
  have he' : (f t - A * cos (T - t)) / sin (T - t) = C := he
  have hmul := (div_eq_iff hs).mp he'
  linarith

/-- The full kernel on an open interval. The constant `A` can later be
instantiated with the value of a support-function difference at the target. -/
theorem tangent_solution_on_Ioo {a b T A : ℝ} {f f' : ℝ → ℝ}
    (hab : a < b)
    (hs : ∀ t ∈ Ioo a b, sin (T - t) ≠ 0)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (he : ∀ t ∈ Ioo a b, sin (T - t) * f' t + cos (T - t) * f t = A) :
    ∃ C : ℝ, EqOn f (fun t => A * cos (T - t) + C * sin (T - t)) (Ioo a b) := by
  let t₀ : ℝ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := by
    dsimp only [t₀]
    constructor <;> linarith
  have hinv : ∀ t ∈ Ioo a b, HasDerivAt (tangentInvariant T A f) 0 t := by
    intro t ht
    exact tangentInvariant_hasDerivAt_zero (hd t ht) (hs t ht) (he t ht)
  have hconst := eqOn_const_of_hasDerivAt_zero ht₀ hinv
  refine ⟨tangentInvariant T A f t₀, ?_⟩
  intro t ht
  exact tangent_eq_of_invariant_eq (hs t ht) (hconst ht)

/-- Continuity extends the open-interval solution to the closed interval, even
when its tangent sine vanishes at one or both endpoints. -/
theorem tangent_solution_on_Icc {a b T A : ℝ} {f f' : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hs : ∀ t ∈ Ioo a b, sin (T - t) ≠ 0)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (he : ∀ t ∈ Ioo a b, sin (T - t) * f' t + cos (T - t) * f t = A) :
    ∃ C : ℝ, EqOn f (fun t => A * cos (T - t) + C * sin (T - t)) (Icc a b) := by
  obtain ⟨C, hC⟩ := tangent_solution_on_Ioo hab hs hd he
  refine ⟨C, ?_⟩
  have hg : Continuous (fun t : ℝ => A * cos (T - t) + C * sin (T - t)) := by
    fun_prop
  apply hC.of_subset_closure hf hg.continuousOn Ioo_subset_Icc_self
  rw [closure_Ioo hab.ne]

end SofaUniqueness
