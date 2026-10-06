module

public import MovingSofaStability.TrigKernelIntegrals

/-!
# Exact four-arc reconstruction

Uncompiled proof source. The middle interval is coupled to the last interval.
A product derivative combines these contributions before estimating them. This
avoids both Fubini and the loss from estimating the two occurrences of f(T)
separately.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory

namespace MovingSofaStability

section Reconstruction

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (h : FourResidualData φ f df)

theorem sharp_last_formula {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    f t = -sin t * (∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u) := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin (π - u) ≠ 0 := by
    intro u hu
    rw [sin_pi_sub]
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  have hr := intervalIntegrable_subinterval h.last le_rfl ht.1 ht.2.le
  have hi := residual_div_sin_integrable ht.1 hr hs
  have he := tangent_reconstruct_right ht.1 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans ht.2⟩) hs hi
  have hq : tangentQuotient π f (π / 2) = 0 := by
    simp [tangentQuotient, h.top_zero, h.left_zero]
  rw [h.left_zero, zero_mul, zero_add, hq, zero_sub, sin_pi_sub] at he
  have hI : (∫ u in (π / 2)..t, tangentResidual π f df u / sin (π - u)) =
      ∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [sin_pi_sub]
    ring
  rw [hI] at he
  nlinarith only [he]

theorem sharp_third_formula {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    f t = -(cos t / cos φ) * f (π - φ) + sin (π - φ - t) *
      (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
  have hpi := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hc : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1, ht.1])).ne'
  have hr := intervalIntegrable_subinterval h.third ht.1 ht.2 le_rfl
  have hi := residual_div_sin_integrable ht.2 hr hs
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hs hi
  have hq : tangentQuotient (π - φ) f (π / 2) = -f (π - φ) * sin φ / cos φ := by
    simp only [tangentQuotient, h.top_zero, zero_sub,
      show π - φ - π / 2 = π / 2 - φ by ring, cos_pi_div_two_sub, sin_pi_div_two_sub]
    ring
  have hcoef : cos (π - φ - t) - sin (π - φ - t) * (sin φ / cos φ) = -cos t / cos φ := by
    have hh : cos (π - φ - t) * cos φ - sin (π - φ - t) * sin φ = -cos t := by
      rw [← cos_add, show π - φ - t + φ = π - t by ring, cos_pi_sub]
    field_simp [hc]
    exact hh
  have hI : (∫ u in t..(π / 2), tangentResidual (π - φ) f df u / sin (π - φ - u)) =
      ∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u := by
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [hq, hI] at he
  calc
    f t = f (π - φ) * (cos (π - φ - t) - sin (π - φ - t) * (sin φ / cos φ)) +
        sin (π - φ - t) *
          (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
      rw [he]
      ring
    _ = _ := by rw [hcoef]; ring

theorem sharp_first_formula {t : ℝ} (ht : t ∈ Icc 0 φ) :
    f t = cos t * ((1 / cos φ) * f φ +
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hs : ∀ u ∈ Icc t φ, sin (π / 2 - u) ≠ 0 := by
    intro u hu
    rw [sin_pi_div_two_sub]
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1, pi_pos], by linarith [hu.2, pi_pos]⟩).ne'
  have hr := intervalIntegrable_subinterval h.first ht.1 ht.2 le_rfl
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2, pi_pos]⟩)
    hs (residual_div_sin_integrable ht.2 hr hs)
  simp only [tangentQuotient, h.top_zero, zero_mul, zero_add, sub_zero, sin_pi_div_two_sub] at he
  have hI : (∫ u in t..φ, tangentResidual (π / 2) f df u / sin (π / 2 - u)) =
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [sin_pi_div_two_sub]
    ring
  rw [hI] at he
  simpa only [div_eq_mul_inv, one_div, mul_comm (f φ)] using he

/-- Product integration replaces a double integral. The reference endpoint
f(pi) is zero, so its tangent residual is cot(u)*f(u)-f'(u). -/
theorem tail_product_integral (A : ℝ) {a b : ℝ}
    (ha : π / 2 ≤ a) (hab : a ≤ b) (hb : b < π) :
    (∫ u in a..b, f u) = tailKernel A a * f a - tailKernel A b * f b -
      ∫ u in a..b, tailKernel A u * tangentResidual π f df u := by
  have hs : ∀ u ∈ Icc a b, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hb)).ne'
  have hk : ContinuousOn (tailKernel A) (Icc a b) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn hs
  have hr := intervalIntegrable_subinterval h.last ha hab hb.le
  have hkr : IntervalIntegrable (fun u => tailKernel A u * tangentResidual π f df u) volume a b := by
    simpa only [mul_comm] using hr.mul_continuousOn (by simpa only [uIcc_of_le hab] using hk)
  have hf := h.continuous.intervalIntegrable a b
  have hd : ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => tailKernel A u * f u)
      (-f u - tailKernel A u * tangentResidual π f df u) (Ioi u) u := by
    intro u hu
    have hsu := hs u ⟨hu.1.le, hu.2.le⟩
    have hdu := (hasDerivAt_tailKernel A hsu).hasDerivWithinAt.mul
      (h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans hb⟩)
    convert hdu using 1
    rw [tangentResidual_left h.left_zero]
    unfold tailKernel
    field_simp [hsu]
    linear_combination -(f u) * sin_sq_add_cos_sq u
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hk.mul h.continuous.continuousOn) hd (hf.neg.sub hkr)
  rw [intervalIntegral.integral_sub hf.neg hkr, intervalIntegral.integral_neg] at he
  linarith

/-- The common r4 kernel is combined before taking any norm. -/
theorem sharp_middle_formula {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    f t = (∫ u in t..(π / 2 - φ), tangentResidual (π / 2) (fun x => 0) (fun x => 0) u) +
      (∫ u in t..(π / 2 - φ), cornerResidual f df u) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) +
      (1 / cos φ - sin t) * (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
      (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hcφ : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hp0 (by linarith)).ne'
  have hct : cos t ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩).ne'
  have hr := intervalIntegrable_subinterval h.middle ht.1 ht.2 le_rfl
  have hshift : IntervalIntegrable (fun u => f (u + π / 2)) volume t (π / 2 - φ) :=
    (h.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hdf : IntervalIntegrable df volume t (π / 2 - φ) := by
    have he := hshift.sub hr
    simpa only [cornerResidual, sub_sub_cancel] using he
  have hrec := corner_reconstruct ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hdf hshift
  have hthird := sharp_third_formula hφ h ⟨le_rfl, by linarith : π / 2 - φ ≤ π / 2⟩
  have hlast := sharp_last_formula h ⟨by linarith [ht.1], by linarith [ht.2] :
    π / 2 + t ∈ Ico (π / 2) π⟩
  have htail := tail_product_integral h (1 / cos φ)
    (a := π / 2 + t) (b := π - φ) (by linarith [ht.1]) (by linarith [ht.2]) (by linarith)
  have hT : tailKernel (1 / cos φ) (π - φ) = tan φ := by
    simp only [tailKernel, sin_pi_sub, cos_pi_sub, tan_eq_sin_div_cos]
    field_simp [hcφ, hsφ]
    nlinarith [sin_sq_add_cos_sq φ]
  have hstart : tailKernel (1 / cos φ) (π / 2 + t) = (1 / cos φ - sin t) / cos t := by
    simp [tailKernel, sin_add, cos_add]
  have hIshift : (∫ u in t..(π / 2 - φ), f (u + π / 2)) =
      ∫ u in (π / 2 + t)..(π - φ), f u := by
    rw [intervalIntegral.integral_comp_add_right f (π / 2)]
    congr 1 <;> ring
  simp only [show π - φ - (π / 2 - φ) = π / 2 by ring,
    sin_pi_div_two, cos_pi_div_two_sub, one_mul, tan_eq_sin_div_cos] at hthird
  simp only [sin_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul, add_zero] at hlast
  rw [hIshift, htail, hT, hstart, hthird, hlast] at hrec
  simp only [tangentResidual, zero_mul, sub_zero, zero_sub, zero_div,
    intervalIntegral.integral_zero, zero_add] at ⊢
  rw [tan_eq_sin_div_cos] at hrec
  convert hrec using 1 <;> field_simp [hct] <;> ring

end Reconstruction
end MovingSofaStability
