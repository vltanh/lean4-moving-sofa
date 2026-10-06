module

public import MovingSofaStability.SharpEvaluation
public import MovingSofaStability.CapDistance

/-!
# The improved Euclidean cap-distance certificate

The actual Mamikon residuals satisfy the analytic hypotheses, and their square
integrals are identified before applying the sharp four-arc estimate. No
kernel-reconstruction premise remains in these theorems.

The old coefficient-80 declarations remain for compatibility. These stronger
entry points have the same domains and the same pinned horizontal translation.
The coefficient is not asserted optimal over feasible caps or free translations.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The improved residual estimate for any two normalized, possibly nonsmooth caps. -/
theorem sharp_capDifference_le_energy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference K₀.1 K₁.1 t| ≤ (2 / cos φ) * sqrt (capResidualEnergy φ K₀ K₁) := by
  have he := sharp_four_arc_coercivity hφ (capDifference_data hφ K₀ K₁ h₀ h₁) ht
  rwa [fourResidualEnergy_eq_capEnergy hφ K₀ K₁] at he

/-- The original Q deficit controls the cap with coefficient 2 sec(phi). -/
theorem sharp_wide_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap x.1.1.1 t| ≤
      (2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num) (cap_angle_parameters hφ).1.le
  have he := sharp_capDifference_le_energy hφ (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1 ht
  exact he.trans (mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (wide_capResidualEnergy_le_deficit hP hbox x)) hc)

/-- The sharper sofa-area-deficit estimate on the original injective class. -/
theorem sharp_ki_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap K t| ≤ (2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  have he := sharp_wide_cap_support_bound hP hbox (toWideTriple (kiExtensionTriple hbox.1 hK)) ht
  have hA := theorem8_2_4 hbox.1 hK
  have hdef : area (gerverSofa P) - wideUpperQ P.φ (toWideTriple (kiExtensionTriple hbox.1 hK)) ≤
      area (gerverSofa P) - sofaArea (π / 2) K := by
    change area (gerverSofa P) - upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ _
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdef) hc)

/-- Actual Euclidean cap distance on the enlarged nonsmooth triple domain. -/
theorem sharp_wide_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 x.2.1
    (mul_nonneg hc (sqrt_nonneg _))
  intro t ht
  exact sharp_wide_cap_support_bound hP hbox x ht

/-- Actual Euclidean cap distance from the original sofa-area deficit. -/
theorem sharp_ki_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 hK.1
    (mul_nonneg hc (sqrt_nonneg _))
  intro t ht
  exact sharp_ki_cap_support_bound hP hbox hK ht

/-- A rational coefficient, justified by inequalities rather than a decimal fit. -/
theorem wide_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  (sharp_wide_cap_distance_bound hP hbox x).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

theorem ki_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) :=
  (sharp_ki_cap_distance_bound hP hbox hK).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

end MovingSofaStability
