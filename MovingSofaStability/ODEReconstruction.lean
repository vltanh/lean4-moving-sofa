module

public import MovingSofaStability.WideResidualEnergy

/-!
# Integrating the residual equations without classical differentiability

Uncompiled proof source. Convex supports have right derivatives even at normal
angles carrying atoms. The reconstruction uses the right-derivative fundamental
theorem on compact intervals avoiding the integrating factor's singularity.
Integrability of the weighted residual is an explicit hypothesis, not inferred
from the totalized value of an integral.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Right-derivative version of the tangent integrating-factor identity. -/
theorem hasDerivWithinAt_tangentQuotient {f df : ℝ → ℝ} {T t : ℝ}
    (hd : HasDerivWithinAt f (df t) (Ioi t) t) (hs : sin (T - t) ≠ 0) :
    HasDerivWithinAt (tangentQuotient T f)
      (-tangentResidual T f df t / sin (T - t)) (Ioi t) t := by
  have hu : HasDerivWithinAt (fun s : ℝ => T - s) (-1) (Ioi t) t := by
    simpa using ((hasDerivAt_id t).const_sub T).hasDerivWithinAt
  have hquot := (hd.sub (hu.cos.const_mul (f T))).div hu.sin hs
  convert hquot using 1
  · rfl
  · dsimp only [tangentResidual]
    have hweighted : f T * (sin (T - t) ^ 2 + cos (T - t) ^ 2) = f T := by
      rw [sin_sq_add_cos_sq, mul_one]
    simp only [Pi.sub_apply]
    field_simp
    linear_combination hweighted

/-- The integral of a weighted residual is the difference of the quotient values. -/
theorem tangent_quotient_integral {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    (∫ t in a..b, tangentResidual T f df t / sin (T - t)) =
      tangentQuotient T f a - tangentQuotient T f b := by
  have hcos : Continuous (fun t : ℝ => cos (T - t)) := by fun_prop
  have hsin : Continuous (fun t : ℝ => sin (T - t)) := by fun_prop
  have hcont : ContinuousOn (tangentQuotient T f) (Icc a b) :=
    (hf.sub (hcos.continuousOn.const_mul (f T))).div hsin.continuousOn hs
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (tangentQuotient T f)
        (-(tangentResidual T f df t / sin (T - t))) (Ioi t) t := by
    intro t ht
    simpa only [neg_div] using
      hasDerivWithinAt_tangentQuotient (hd t ht) (hs t ⟨ht.1.le, ht.2.le⟩)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- Solve backwards from the right endpoint on a nonsingular interval. -/
theorem tangent_reconstruct_left {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f a = f T * cos (T - a) + sin (T - a) *
      (tangentQuotient T f b + ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  have h := tangent_quotient_integral hab hf hd hs hi
  have hsa := hs a ⟨le_rfl, hab⟩
  rw [h]
  unfold tangentQuotient
  field_simp [hsa]
  ring

/-- Solve forwards from the left endpoint on a nonsingular interval. -/
theorem tangent_reconstruct_right {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f b = f T * cos (T - b) + sin (T - b) *
      (tangentQuotient T f a - ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  have h := tangent_quotient_integral hab hf hd hs hi
  have hsb := hs b ⟨hab, le_rfl⟩
  rw [h]
  unfold tangentQuotient
  field_simp [hsb]
  ring

/-- The middle residual has no integrating-factor denominator. -/
theorem corner_reconstruct {f df : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hdf : IntervalIntegrable df volume a b)
    (hshift : IntervalIntegrable (fun t => f (t + π / 2)) volume a b) :
    f a = f b - (∫ t in a..b, f (t + π / 2)) +
      ∫ t in a..b, cornerResidual f df t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hf hd hdf
  unfold cornerResidual
  rw [intervalIntegral.integral_sub hshift hdf, h]
  ring

/-- Support differences have a right derivative at every normal, not just away from atoms. -/
theorem support_difference_rightDerivative {K₀ K₁ : Set (ℝ × ℝ)}
    (h₀ : IsConvexBody K₀) (h₁ : IsConvexBody K₁) (t : ℝ) :
    HasDerivWithinAt (fun u => supp K₁ u - supp K₀ u)
      (opt_g K₁ t - opt_g K₀ t) (Ioi t) t := by
  exact ((hasDerivWithinAt_supp_right h₁ t).sub
    (hasDerivWithinAt_supp_right h₀ t)).mono Ioi_subset_Ici_self

/-- The pinned support difference still has right derivatives at all normals. -/
theorem pinned_support_rightDerivative {K₀ K₁ : Set (ℝ × ℝ)}
    (h₀ : IsConvexBody K₀) (h₁ : IsConvexBody K₁) (t : ℝ) :
    HasDerivWithinAt (pinnedDifference (fun u => supp K₁ u - supp K₀ u))
      (pinnedDerivative (fun u => supp K₁ u - supp K₀ u)
        (fun u => opt_g K₁ u - opt_g K₀ u) t) (Ioi t) t := by
  have hd := support_difference_rightDerivative h₀ h₁ t
  have hcos := ((hasDerivAt_cos t).const_mul (supp K₁ π - supp K₀ π)).hasDerivWithinAt
    (s := Ioi t)
  have he : pinnedDerivative (fun u => supp K₁ u - supp K₀ u)
      (fun u => opt_g K₁ u - opt_g K₀ u) t =
      opt_g K₁ t - opt_g K₀ t + (supp K₁ π - supp K₀ π) * -sin t := by
    simp only [pinnedDerivative]; ring
  rw [he]
  exact hd.add hcos

end MovingSofaStability
