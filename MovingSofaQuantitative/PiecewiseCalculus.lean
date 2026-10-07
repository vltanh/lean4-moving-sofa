module

public import MovingSofaStability.CapEstimate

/-!
# Finite continuous profiles with right derivatives

Uncompiled proof source. Values use the right branch at a cut. Continuity needs
matching values, but differentiability across the cut does not require matching
left and right derivatives. This is the convention needed by cap residuals.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory

namespace MovingSofaQuantitative

/-- Join two functions, assigning the cut itself to the right branch. -/
def rightJoin (a : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < a then f t else g t

theorem continuous_rightJoin {a : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hmatch : f a = g a) :
    Continuous (rightJoin a f g) := by
  have h : Continuous (fun t : ℝ => if a ≤ t then g t else f t) :=
    continuous_if_le continuous_const continuous_id hg.continuousOn hf.continuousOn
      (fun t ht => by subst t; exact hmatch.symm)
  have he : rightJoin a f g = (fun t : ℝ => if a ≤ t then g t else f t) := by
    funext t
    by_cases ht : t < a
    · simp [rightJoin, ht, not_le.mpr ht]
    · simp [rightJoin, ht, not_lt.mp ht]
  rwa [he]

/-- Right derivatives glue at the right-assigned cut; the right derivative may jump. -/
theorem rightDeriv_rightJoin {a : ℝ} {f g df dg : ℝ → ℝ}
    (hf : ∀ t, HasDerivWithinAt f (df t) (Ioi t) t)
    (hg : ∀ t, HasDerivWithinAt g (dg t) (Ioi t) t) (t : ℝ) :
    HasDerivWithinAt (rightJoin a f g) (rightJoin a df dg t) (Ioi t) t := by
  change HasDerivWithinAt (rightJoin a f g) (if t < a then df t else dg t) (Ioi t) t
  by_cases ht : t < a
  · rw [if_pos ht]
    apply (hf t).congr_of_eventuallyEq _ (by simp [rightJoin, ht])
    have hnb : Iio a ∈ 𝓝[Ioi t] t :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds ht)
    filter_upwards [hnb] with u hu
    simp only [rightJoin, if_pos hu]
  · rw [if_neg ht]
    apply (hg t).congr_of_eventuallyEq _ (by simp [rightJoin, ht])
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hua : ¬u < a := not_lt.mpr ((not_lt.mp ht).trans (le_of_lt hu))
    simp only [rightJoin, if_neg hua]

/-- Trigonometric affine pieces and their exact right derivative. -/
def trigAffine (a b c : ℝ) (t : ℝ) : ℝ := a + b * cos t + c * sin t

def trigAffineDeriv (b c : ℝ) (t : ℝ) : ℝ := -b * sin t + c * cos t

theorem continuous_trigAffine (a b c : ℝ) : Continuous (trigAffine a b c) := by
  unfold trigAffine
  fun_prop

theorem hasDerivAt_trigAffine (a b c t : ℝ) :
    HasDerivAt (trigAffine a b c) (trigAffineDeriv b c t) t := by
  convert ((hasDerivAt_const t a).add ((hasDerivAt_cos t).const_mul b)).add
    ((hasDerivAt_sin t).const_mul c) using 1 <;> simp [trigAffine, trigAffineDeriv] <;> ring

/-- Replacing finitely many endpoint values does not affect interval integrability. -/
theorem intervalIntegrable_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (he : EqOn f g (Ioo a b)) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hg).congr_fun
    (fun t ht => (he ht).symm) measurableSet_Ioo

/-- The corresponding equality of integrals ignores the two endpoints. -/
theorem intervalIntegral_eq_of_eqOn_Ioo {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (he : EqOn f g (Ioo a b)) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => he ht

end MovingSofaQuantitative
