module

public import MovingSofaStability.SharpIntegralControl

/-!
# Exact square integrals of the trigonometric evaluation kernels

Uncompiled proof source. All integrations take place on compact intervals
where the displayed denominators are nonzero. No improper integral is silently
used at pi; that endpoint is handled separately by the pinned support value.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

def cotangent (u : ℝ) : ℝ := cos u / sin u

def tailKernel (A u : ℝ) : ℝ := (A + cos u) / sin u

def tailKernelPrimitive (A u : ℝ) : ℝ :=
  -(A ^ 2 + 1) * cotangent u - 2 * A * (1 / sin u) - u

theorem hasDerivAt_cotangent {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt cotangent (-(1 / sin u) ^ 2) u := by
  convert (hasDerivAt_cos u).div (hasDerivAt_sin u) hs using 1
  · rfl
  · field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem hasDerivAt_cosecant {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (fun u => 1 / sin u) (-cos u / sin u ^ 2) u := by
  convert (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_sin u) hs using 1 <;> ring

theorem hasDerivAt_secant {u : ℝ} (hc : cos u ≠ 0) :
    HasDerivAt (fun u => 1 / cos u) (sin u / cos u ^ 2) u := by
  convert (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_cos u) hc using 1 <;> ring

theorem hasDerivAt_tailKernel (A : ℝ) {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (tailKernel A) (-(1 + A * cos u) / sin u ^ 2) u := by
  convert ((hasDerivAt_cos u).const_add A).div (hasDerivAt_sin u) hs using 1
  · rfl
  · field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem hasDerivAt_tailKernelPrimitive (A : ℝ) {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (tailKernelPrimitive A) (tailKernel A u ^ 2) u := by
  have hd := (((hasDerivAt_cotangent hs).const_mul (-(A ^ 2 + 1))).sub
    ((hasDerivAt_cosecant hs).const_mul (2 * A))).sub (hasDerivAt_id u)
  convert hd using 1
  · rfl
  · unfold tailKernel
    field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem cosecant_sq_integral {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, (1 / sin u) ^ 2) = cotangent a - cotangent b := by
  have hi : IntervalIntegrable (fun u => (1 / sin u) ^ 2) volume a b :=
    ((continuousOn_const.div continuous_sin.continuousOn hs).pow 2).intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => -cotangent u) (f' := fun u => (1 / sin u) ^ 2)
    (fun u hu => by
      rw [uIcc_of_le hab] at hu
      have hd := (hasDerivAt_cotangent (hs u hu)).neg
      rw [neg_neg] at hd
      exact hd) hi
  linarith

theorem secant_sq_integral {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ u ∈ Icc a b, cos u ≠ 0) :
    (∫ u in a..b, (1 / cos u) ^ 2) = tan b - tan a := by
  have hi : IntervalIntegrable (fun u => (1 / cos u) ^ 2) volume a b :=
    ((continuousOn_const.div continuous_cos.continuousOn hc).pow 2).intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ Icc a b, HasDerivAt tan ((1 / cos u) ^ 2) u := by
    intro u hu
    convert (hasDerivAt_sin u).div (hasDerivAt_cos u) (hc u hu) using 1
    · exact funext fun x => tan_eq_sin_div_cos x
    · field_simp [hc u hu]
      nlinarith [sin_sq_add_cos_sq u]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by simpa only [uIcc_of_le hab] using hu)) hi

theorem shifted_cosecant_sq_integral {a b T : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin (T - u) ≠ 0) :
    (∫ u in a..b, (1 / sin (T - u)) ^ 2) = cotangent (T - b) - cotangent (T - a) := by
  have hsin : ContinuousOn (fun u => sin (T - u)) (Icc a b) := by fun_prop
  have hi : IntervalIntegrable (fun u => (1 / sin (T - u)) ^ 2) volume a b :=
    ((continuousOn_const.div hsin hs).pow 2).intervalIntegrable_of_Icc hab
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro u hu
  rw [uIcc_of_le hab] at hu
  convert (hasDerivAt_cotangent (hs u hu)).comp u ((hasDerivAt_id u).const_sub T) using 1
  · rfl
  · ring

theorem tailKernel_sq_integral (A : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, tailKernel A u ^ 2) = tailKernelPrimitive A b - tailKernelPrimitive A a := by
  have hk : ContinuousOn (tailKernel A) (Icc a b) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn hs
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_tailKernelPrimitive A (hs u (by simpa only [uIcc_of_le hab] using hu)))
    ((hk.pow 2).intervalIntegrable_of_Icc hab)

/-- The fourth-arc weight integrated only as far as the evaluation point. -/
theorem last_kernel_norm {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    sin t ^ 2 * (∫ u in (π / 2)..t, (1 / sin u) ^ 2) = -sin t * cos t := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  rw [cosecant_sq_integral ht.1 hs]
  simp only [cotangent, cos_pi_div_two, sin_pi_div_two, zero_div, zero_sub]
  field_simp [hs t ⟨ht.1, le_rfl⟩]

end MovingSofaStability
