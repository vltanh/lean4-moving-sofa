module

public import MovingSofaQuantitative.ComparisonProfile
public import MovingSofaQuantitative.ProjectionAlgebra

/-!
# Endpoint representation and centered four-arc coercivity

Uncompiled proof source. The pairing with the comparison profile is proved
from the EXISTING reconstruction at zero. Its energy is obtained by pairing
it with itself. Applying the existing pinned estimate to every `f-a*C` then
proves the centered estimate. No covariance-integral assumption remains.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

/-- The endpoint evaluation as an explicit sum of the actual residual integrals. -/
def endpointResidualIntegral (φ : ℝ) (f df : ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..φ, (1 / cos u) * tangentResidual (π / 2) f df u) +
  (1 / cos φ) * (∫ u in φ..(π / 2 - φ), cornerResidual f df u) +
  (1 / cos φ) * (∫ u in (π / 2 - φ)..(π / 2),
    (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) +
  ((1 / cos φ) * (1 / cos φ - sin φ)) *
    (∫ u in (π / 2)..(π / 2 + φ), (1 / sin u) * tangentResidual π f df u) +
  (1 / cos φ) * (∫ u in (π / 2 + φ)..(π - φ),
    tailKernel (1 / cos φ) u * tangentResidual π f df u)

/-- This is a direct specialization of the integrated first/middle formulas. -/
theorem endpointResidualIntegral_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) :
    endpointResidualIntegral φ f df = f 0 := by
  have h0 := sharp_first_formula hφ hf (t := 0) ⟨le_rfl, hφ.1.le⟩
  have h1 := sharp_middle_formula hφ hf (t := φ)
    ⟨le_rfl, by linarith [hφ.2]⟩
  rw [cos_zero, one_mul, h1] at h0
  unfold endpointResidualIntegral
  linear_combination -h0

/-- The concrete comparison profile represents endpoint evaluation in the
four residual integrals. The final arc after pi-phi contributes zero. -/
theorem residualPair_comparison {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) :
    residualPair φ f df (comparisonProfile φ) (comparisonDerivative φ) = f 0 := by
  have hC := comparisonProfile_data hφ
  have h01 : (0 : ℝ) ≤ φ := hφ.1.le
  have h12 : φ ≤ π / 2 - φ := by linarith [hφ.2]
  have h23 : π / 2 - φ ≤ π / 2 := by linarith [hφ.1]
  have h34 : π / 2 ≤ π / 2 + φ := by linarith [hφ.1]
  have h45 : π / 2 + φ ≤ π - φ := by linarith [hφ.2]
  have h56 : π - φ ≤ π := by linarith [hφ.1]
  have h1 : (∫ u in (0 : ℝ)..φ, tangentResidual (π / 2) f df u *
      tangentResidual (π / 2) (comparisonProfile φ) (comparisonDerivative φ) u) =
      ∫ u in (0 : ℝ)..φ, (1 / cos u) * tangentResidual (π / 2) f df u := by
    apply intervalIntegral_eq_of_eqOn_Ioo h01
    intro u hu
    rw [comparison_first hφ hu]
    ring
  have h2 : (∫ u in φ..(π / 2 - φ), cornerResidual f df u *
      cornerResidual (comparisonProfile φ) (comparisonDerivative φ) u) =
      (1 / cos φ) * ∫ u in φ..(π / 2 - φ), cornerResidual f df u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral_eq_of_eqOn_Ioo h12
    intro u hu
    rw [comparison_middle hφ hu]
    ring
  have h3 : (∫ u in (π / 2 - φ)..(π / 2), tangentResidual (π - φ) f df u *
      tangentResidual (π - φ) (comparisonProfile φ) (comparisonDerivative φ) u) =
      (1 / cos φ) * ∫ u in (π / 2 - φ)..(π / 2),
        (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral_eq_of_eqOn_Ioo h23
    intro u hu
    rw [comparison_third hφ hu]
    ring
  let F := fun u => tangentResidual π f df u *
    tangentResidual π (comparisonProfile φ) (comparisonDerivative φ) u
  have hi : IntervalIntegrable F volume (π / 2) π :=
    intervalIntegrable_product_of_squares (by linarith [pi_pos])
      hf.last hC.last hf.last_sq hC.last_sq
  have ia := intervalIntegrable_subinterval hi le_rfl h34 (h45.trans h56)
  have ib := intervalIntegrable_subinterval hi h34 h45 h56
  have ic := intervalIntegrable_subinterval hi (h34.trans h45) h56 le_rfl
  have hsplit : (∫ u in (π / 2)..π, F u) =
      (∫ u in (π / 2)..(π / 2 + φ), F u) +
      (∫ u in (π / 2 + φ)..(π - φ), F u) + (∫ u in (π - φ)..π, F u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals ia ib,
      intervalIntegral.integral_add_adjacent_intervals (ia.trans ib) ic]
  have h4a : (∫ u in (π / 2)..(π / 2 + φ), F u) =
      ((1 / cos φ) * (1 / cos φ - sin φ)) *
        ∫ u in (π / 2)..(π / 2 + φ), (1 / sin u) * tangentResidual π f df u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral_eq_of_eqOn_Ioo h34
    intro u hu
    dsimp [F]
    rw [comparison_last_left hφ hu]
    ring
  have h4b : (∫ u in (π / 2 + φ)..(π - φ), F u) =
      (1 / cos φ) * ∫ u in (π / 2 + φ)..(π - φ),
        tailKernel (1 / cos φ) u * tangentResidual π f df u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral_eq_of_eqOn_Ioo h45
    intro u hu
    dsimp [F]
    rw [comparison_last_middle hφ hu]
    ring
  have h4c : (∫ u in (π - φ)..π, F u) = 0 := by
    calc
      _ = ∫ u in (π - φ)..π, (0 : ℝ) := by
        apply intervalIntegral_eq_of_eqOn_Ioo h56
        intro u hu
        dsimp [F]
        rw [comparison_last_right hφ hu, mul_zero]
      _ = 0 := by simp
  unfold residualPair
  rw [h1, h2, h3]
  change _ + (∫ u in (π / 2)..π, F u) = _
  rw [hsplit, h4a, h4b, h4c]
  have he := endpointResidualIntegral_eq hφ hf
  unfold endpointResidualIntegral at he
  linear_combination he

/-- The comparison energy is exact; no numerical quadrature is used. -/
theorem comparisonProfile_energy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    fourResidualEnergy φ (comparisonProfile φ) (comparisonDerivative φ) = (1 / cos φ) ^ 2 := by
  have he := residualPair_comparison hφ (comparisonProfile_data hφ)
  rw [residualPair_self, comparisonProfile_zero hφ] at he
  linarith

/-- Centered four-arc coercivity, instantiated for actual residual data. -/
theorem centered_four_arc_bound {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t - (f 0 / 2) * cos t| ≤ (1 / cos φ) * sqrt (fourResidualEnergy φ f df) := by
  have hC := comparisonProfile_data hφ
  have hCf := sharp_green_control hφ hC ht
  have hn := hCf.kernel_nonneg
  have hdet : greenCovariance φ t ^ 2 ≤
      greenNormSquared φ t * (2 * (1 / cos φ) ^ 2) := by
    have he := hCf.bound
    rwa [comparisonProfile_energy hφ, comparisonProfile_eq_covariance hφ] at he
  have hy : f 0 ^ 2 ≤ (2 * (1 / cos φ) ^ 2) * (2 * fourResidualEnergy φ f df) := by
    have he := (sharp_green_control hφ hf (t := 0) ⟨le_rfl, pi_pos.le⟩).bound
    simpa only [greenNormSquared, if_pos hφ.1.le, cos_zero, tan_zero, one_pow,
      mul_one, one_mul, sub_zero] using he
  apply centered_evaluation_of_comparison hφ (fourResidualEnergy_nonneg' hφ f df) hn hdet hy
  intro a
  have he := (sharp_green_control hφ (fourResidualData_sub_smul hφ hf hC a) ht).bound
  rw [fourResidualEnergy_sub_smul hφ hf hC a, residualPair_comparison hφ hf,
    comparisonProfile_energy hφ, comparisonProfile_eq_covariance hφ] at he
  nlinarith only [he]

end MovingSofaQuantitative
