module

public import MovingSofaQuantitative.ComparisonPairing
public import MovingSofaQuantitative.Targets

/-!
# Centered cap coercivity

Uncompiled proof source. The three final statements use actual cap residuals,
the integrated wide-domain Q deficit, and the original Ki area deficit.
The endpoint comparison profile discharges the analytic centered estimate;
no kernel identity or centered-coercivity premise is left in the statements.
The old left-pinned theorem and normalization remain unchanged.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

/-- The support form of the centered estimate for two actual right-angle caps. -/
theorem centered_cap_support_bound {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |centeredCapDifference K₀.1 K₁.1 t| ≤
      (1 / cos φ) * sqrt (capResidualEnergy φ K₀ K₁) := by
  obtain ⟨hd, he⟩ := capDifference_data hφ K₀ K₁ h₀ h₁
  have hb := centered_four_arc_bound hφ hd ht
  rw [he] at hb
  simpa only [centeredCapDifference, centerFunction_eq_pinned, capDifference] using hb

/-- Exact target G.1: Euclidean cap distance from the cap's actual residual energy. -/
theorem centered_energy : Targets.CenteredEnergy := by
  intro φ hφ K₀ K₁ h₀ h₁
  exact cap_close_of_centered_support h₀ h₁
    (fun _ ht => centered_cap_support_bound hφ K₀ K₁ h₀ h₁ ht)

/-- The corresponding support bound from the full enlarged-domain Q deficit. -/
theorem centered_wide_support_bound {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ)
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |centeredCapDifference P.cap x.1.1.1 t| ≤
      (1 / cos P.φ) * sqrt (qDeficit P x) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hc : 0 < cos P.φ := (cap_angle_parameters hφ).1
  refine (centered_cap_support_bound hφ (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1 ht).trans ?_
  exact mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (wide_capResidualEnergy_le_deficit hP hbox x)) (by positivity)

/-- Exact target G.1: midpoint-aligned Euclidean cap distance from M-Q. -/
theorem centered_cap : Targets.CenteredCap := by
  intro P hP hbox x
  exact cap_close_of_centered_support (wideGerverTriple hP hbox).2.1 x.2.1
    (fun _ ht => centered_wide_support_bound hP hbox x ht)

/-- The Ki support estimate uses the sofa area belonging to that cap. -/
theorem centered_ki_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |centeredCapDifference P.cap K t| ≤
      (1 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
  have hc := (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1
  refine (centered_wide_support_bound hP hbox
    (toWideTriple (kiExtensionTriple hbox.1 hK)) ht).trans ?_
  unfold qDeficit
  gcongr
  exact theorem8_2_4 hbox.1 hK

/-- Exact target G.1: the original injective class with its own area deficit. -/
theorem centered_ki : Targets.CenteredKi := by
  intro P hP hbox K hK
  exact cap_close_of_centered_support (wideGerverTriple hP hbox).2.1 hK.1
    (fun _ ht => centered_ki_support_bound hP hbox hK ht)

/-- A rational coefficient with no floating-point conversion. -/
theorem centered_cap_1001 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((1001 / 1000) * sqrt (qDeficit P x))
      x.1.1.1 (centeredReference P.cap x.1.1.1) := by
  exact (centered_cap P hP hbox x).mono (mul_le_mul_of_nonneg_right
    ((sec_phi_rational_bound hbox.1).1.trans (sec_phi_rational_bound hbox.1).2.le)
    (sqrt_nonneg _))

/-- The zero-deficit corollary is actual cap equality at midpoint alignment. -/
theorem centered_zero_deficit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (hz : qDeficit P x = 0) :
    x.1.1.1 = centeredReference P.cap x.1.1.1 := by
  have h := centered_cap P hP hbox x
  rw [hz, sqrt_zero, mul_zero] at h
  exact h.eq_of_zero

end MovingSofaQuantitative
