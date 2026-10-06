module

public import MovingSofaStability.SupportDistance

/-!
# Euclidean cap-distance certificate

The upper-semicircle coercivity estimate is extended to all directions using the
cap's two bottom endpoints, then converted to actual Euclidean Hausdorff
witnesses. The coefficient 80 is non-sharp.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- On the lower-right semicircle a cap is supported by its right bottom endpoint. -/
theorem cap_lower_right_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : 0 ≤ cos t) : supp K t = supp K 0 * cos t := by
  apply supp_eq_of_mem hK.2.1.2.1
  · intro p hp
    have hx := (opt_cap_fst_le hK hp).2
    have hy := (inj_cap_strip hK hp).1
    have hxc := mul_le_mul_of_nonneg_right hx hc
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hs
    simp only [dot, uvec]
    linarith
  · exact opt_cap_A_mem hK
  · simp [dot, uvec]

/-- The lower-left counterpart uses the left bottom endpoint. -/
theorem cap_lower_left_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : cos t ≤ 0) : supp K t = -supp K π * cos t := by
  apply supp_eq_of_mem hK.2.1.2.1
  · intro p hp
    have hx := (opt_cap_fst_le hK hp).1
    have hy := (inj_cap_strip hK hp).1
    have hxc := mul_le_mul_of_nonpos_right hx hc
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hs
    simp only [dot, uvec]
    linarith
  · exact opt_cap_C_mem hK
  · simp [dot, uvec]

/-- Every unit normal with nonnegative ordinate has a representative in [0,pi]. -/
theorem upper_normal_representative (t : ℝ) (hs : 0 ≤ sin t) :
    ∃ s ∈ Icc (0 : ℝ) π, uvec s = uvec t ∧ cos s = cos t := by
  let s := arccos (cos t)
  have hsc : cos s = cos t := cos_arccos (neg_one_le_cos t) (cos_le_one t)
  have hsi : s ∈ Icc (0 : ℝ) π := ⟨arccos_nonneg _, arccos_le_pi _⟩
  have hss : sin s = sin t := by
    have hs0 := sin_nonneg_of_nonneg_of_le_pi hsi.1 hsi.2
    have h1 := sin_sq_add_cos_sq s
    have h2 := sin_sq_add_cos_sq t
    rw [hsc] at h1
    nlinarith
  refine ⟨s, hsi, ?_, hsc⟩
  ext <;> simp only [uvec, hsc, hss]

/-- No periodic-supremum assumption is needed to extend the cap support bound. -/
theorem capDifference_bound_all {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) :
    ∀ t, |capDifference K₀ K₁ t| ≤ R := by
  intro t
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsi, hu, hc⟩ := upper_normal_representative t hs
    have h0 : supp K₀ s = supp K₀ t := by simp only [supp, hu]
    have h1 : supp K₁ s = supp K₁ t := by simp only [supp, hu]
    have hd : capDifference K₀ K₁ s = capDifference K₀ K₁ t := by
      simp only [capDifference, pinnedDifference, h0, h1, hc]
    rw [← hd]
    exact hupper s hsi
  have hs' : sin t ≤ 0 := (not_le.mp hs).le
  by_cases hc : 0 ≤ cos t
  · have he : capDifference K₀ K₁ t = capDifference K₀ K₁ 0 * cos t := by
      simp only [capDifference, pinnedDifference,
        cap_lower_right_support h₀ hs' hc, cap_lower_right_support h₁ hs' hc, cos_zero]
      ring
    rw [he, abs_mul]
    have h0 := hupper 0 ⟨le_rfl, pi_pos.le⟩
    exact (mul_le_mul h0 (abs_cos_le_one t) (abs_nonneg _) hR).trans_eq (mul_one R)
  · have he : capDifference K₀ K₁ t = 0 := by
      simp only [capDifference, pinnedDifference,
        cap_lower_left_support h₀ hs' (not_le.mp hc).le,
        cap_lower_left_support h₁ hs' (not_le.mp hc).le]
      ring
    simpa only [he, abs_zero] using hR

/-- The reference is shifted left by the competing cap's left-support error. -/
def capReferenceShift (K₀ K₁ : Set Point) : Point := (-(supp K₁ π - supp K₀ π), 0)

def shiftedReferenceCap (K₀ K₁ : Set Point) : Set Point :=
  (fun p => p + capReferenceShift K₀ K₁) '' K₀

theorem capDifference_eq_shifted_support {K₀ K₁ : Set Point}
    (h₀ : IsConvexBody K₀) (t : ℝ) :
    capDifference K₀ K₁ t = supp K₁ t - supp (shiftedReferenceCap K₀ K₁) t := by
  unfold shiftedReferenceCap
  rw [supp_translate K₀ _ t h₀.2.1 h₀.1]
  simp only [capDifference, pinnedDifference, capReferenceShift, dot, uvec]
  ring

/-- Upper support control yields Euclidean Hausdorff control after the explicit translation. -/
theorem cap_euclideanClose_of_upper_support {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) :
    EuclideanClose R K₁ (shiftedReferenceCap K₀ K₁) := by
  apply euclideanClose_of_support_bound h₁.2.1
    (convexBody_translate h₀.2.1 (capReferenceShift K₀ K₁)) hR
  intro t
  change |supp K₁ t - supp (shiftedReferenceCap K₀ K₁) t| ≤ R
  rw [← capDifference_eq_shifted_support h₀.2.1 t]
  exact capDifference_bound_all h₀ h₁ hR hupper t

/-- Fully assembled non-sharp cap-distance theorem on the nonsmooth Q domain. -/
theorem wide_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose (80 * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) := by
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 x.2.1
    (by positivity)
  intro t ht
  exact wide_cap_support_bound hP hbox x ht

/-- The area-deficit corollary on the existing injective class. -/
theorem ki_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose (80 * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) := by
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 hK.1
    (by positivity)
  intro t ht
  exact ki_cap_support_bound hP hbox hK ht

/-- No translation remains when the reference and competitor have the same left support. -/
theorem shiftedReferenceCap_eq_of_left_support {K₀ K₁ : Set Point}
    (h : supp K₁ π = supp K₀ π) : shiftedReferenceCap K₀ K₁ = K₀ := by
  simp [shiftedReferenceCap, capReferenceShift, h, Prod.mk_zero_zero]

end MovingSofaStability
