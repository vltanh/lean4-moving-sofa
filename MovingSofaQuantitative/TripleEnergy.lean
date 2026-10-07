module

public import MovingSofaQuantitative.AuxiliaryData
public import MovingSofaQuantitative.KernelGram

/-!
# Full-Q energy of an actual feasible triple

Uncompiled proof source. All functions, residual vectors, auxiliary energies,
and endpoint errors are constructed from the input wide triple. The resulting
rank-two budget is valid before assuming zero first variation. The remaining
operator and endpoint-slack estimates can consume this theorem directly.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

def criticalLeft (P : GerverParams) : ℝ := π / 2 - P.θ
def criticalRight (P : GerverParams) : ℝ := π / 2 + P.θ

def penaltyWeightB (P : GerverParams) : ℝ := tan (criticalLeft P) - tan P.φ

def penaltyWeightD (P : GerverParams) : ℝ :=
  cos (π - P.φ - criticalRight P) / sin (π - P.φ - criticalRight P) - tan P.φ

theorem critical_arc_order {P : GerverParams} (hP : P.IsSolution) :
    0 < P.φ ∧ P.φ < criticalLeft P ∧ criticalLeft P < π / 2 - P.φ ∧
      π / 2 - P.φ < π / 2 ∧ π / 2 < criticalRight P ∧
      criticalRight P < π - P.φ ∧ π - P.φ < π := by
  have hp := gm_φ_pos hP
  have hpt := gm_φ_lt_θ hP
  have ht := gm_θ_lt_c hP
  unfold criticalLeft criticalRight
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [pi_pos]

theorem penaltyWeights_pos {P : GerverParams} (hP : P.IsSolution) :
    0 < penaltyWeightB P ∧ 0 < penaltyWeightD P := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hc0 : 0 < criticalLeft P := hp.trans hpc
  have hcv : criticalLeft P < π / 2 := hcb.trans hb
  have hcp := cos_pos_of_mem_Ioo (show P.φ ∈ Ioo (-(π / 2)) (π / 2) by
    exact ⟨by linarith [pi_pos], hpc.trans hcv⟩)
  have hcc := cos_pos_of_mem_Ioo (show criticalLeft P ∈ Ioo (-(π / 2)) (π / 2) by
    exact ⟨by linarith [pi_pos], hcv⟩)
  have hsc := sin_pos_of_pos_of_lt_pi (sub_pos.mpr hpc)
    (show criticalLeft P - P.φ < π by linarith [pi_pos])
  have hz0 : 0 < π - P.φ - criticalRight P := sub_pos.mpr hdT
  have hz1 : π - P.φ - criticalRight P < π / 2 := by linarith
  have hsz := sin_pos_of_pos_of_lt_pi hz0 (by linarith [pi_pos])
  have hct := cos_pos_of_mem_Ioo (show criticalLeft P ∈ Ioo (-(π / 2)) (π / 2) by
    exact ⟨by linarith [pi_pos], hcv⟩)
  constructor
  · have he : penaltyWeightB P = sin (criticalLeft P - P.φ) /
        (cos (criticalLeft P) * cos P.φ) := by
      unfold penaltyWeightB
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, sin_sub]
      field_simp
      ring
    rw [he]
    positivity
  · have he : penaltyWeightD P = cos (π - criticalRight P) /
        (sin (π - P.φ - criticalRight P) * cos P.φ) := by
      unfold penaltyWeightD
      rw [tan_eq_sin_div_cos, show π - criticalRight P =
        (π - P.φ - criticalRight P) + P.φ by ring, cos_add]
      field_simp
      ring
    rw [he]
    have hec : π - criticalRight P = criticalLeft P := by
      unfold criticalLeft criticalRight
      ring
    rw [hec]
    positivity

/-- The two scalar endpoint functionals of the cap profile. -/
def endpointB (P : GerverParams) (f : ℝ → ℝ) : ℝ :=
  f P.φ / cos P.φ - f (criticalLeft P) / cos (criticalLeft P)

def endpointD (P : GerverParams) (f : ℝ → ℝ) : ℝ :=
  f (criticalRight P) / sin (π - P.φ - criticalRight P) - penaltyWeightD P * f (π - P.φ)

/-- The reference cap and the input cap provide genuine four-arc data. -/
def tripleResidualData {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    FourResidualData P.φ (capDifference P.cap x.1.1.1) (capDifferenceDeriv P.cap x.1.1.1) :=
  (capDifference_data (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1).1

def tripleResidualVector {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ResidualHilbert P.φ :=
  residualVector (gm_φ_mem_Ioo hP hbox) (tripleResidualData hP hbox x)

theorem tripleResidualVector_norm_sq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    ‖tripleResidualVector hP hbox x‖ ^ 2 =
      2 * capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 := by
  rw [tripleResidualVector, residualVector_norm_sq]
  congr 1
  exact (capDifference_data (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1).2

/-- The right auxiliary energy controls the first penalty, with the actual
nonnegative wall slack at the beginning of the active interval. -/
theorem triple_right_penalty {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    (endpointB P (capDifference P.cap x.1.1.1) -
      rightWallSlack x (criticalLeft P) / cos (criticalLeft P)) ^ 2 / penaltyWeightB P ≤
      2 * rightResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1 := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  let B₀ := (wideGerverTriple hP hbox).1.2.1
  let B₁ := x.1.2.1
  let a := supp x.1.1.1 π - supp P.cap π
  obtain ⟨hi, hi2, he⟩ := auxiliaryResidual_data B₀ B₁ a
    (a := P.φ) (b := π / 2) (T := π / 2)
    (by linarith) (by linarith [pi_pos]) (by linarith [pi_pos]) le_rfl
  have hcontact := auxiliaryProfile_contacts hP hbox x
  have hprofile := rightProfile_on_active hP hbox x
    (t := criticalLeft P) ⟨le_rfl, by linarith⟩
  have hbound : arcSquare P.φ (criticalLeft P)
      (tangentResidual (π / 2) (auxiliaryDifference B₀.1 B₁.1 a)
        (auxiliaryDerivative B₀.1 B₁.1 a)) ≤
      2 * rightResidualEnergy P.φ B₀ B₁ := by
    have hm := arcSquare_mono hi2 le_rfl hpc.le (by linarith)
    rw [he] at hm
    simpa only [rightResidualEnergy, show π + π / 2 = 3 * π / 2 by ring] using hm
  exact right_auxiliary_penalty hp hpc (by linarith)
    (auxiliaryDifference_continuous B₀ B₁ a)
    (fun t _ => auxiliaryDifference_rightDeriv B₀ B₁ a t)
    hcontact.1 hcontact.2.2.1 hprofile
    (intervalIntegrable_subinterval hi le_rfl hpc.le (by linarith))
    (intervalIntegrable_subinterval hi2 le_rfl hpc.le (by linarith)) hbound (penaltyWeights_pos hP).1

/-- The left penalty carries the opposite signed endpoint correction. -/
theorem triple_left_penalty {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    (endpointD P (capDifference P.cap x.1.1.1) +
      leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P)) ^ 2 / penaltyWeightD P ≤
      2 * leftResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2 := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  let D₀ := (wideGerverTriple hP hbox).1.2.2
  let D₁ := x.1.2.2
  let a := supp x.1.1.1 π - supp P.cap π
  obtain ⟨hi, hi2, he⟩ := auxiliaryResidual_data D₀ D₁ a
    (a := π / 2) (b := π - P.φ) (T := π - P.φ)
    (by linarith) (by linarith [pi_pos]) (by linarith [pi_pos]) le_rfl
  have hcontact := auxiliaryProfile_contacts hP hbox x
  have hprofile := leftProfile_on_active hP hbox x
    (t := criticalRight P) ⟨by linarith, le_rfl⟩
  have hbound : arcSquare (π / 2) (criticalRight P)
      (tangentResidual (π - P.φ) (auxiliaryDifference D₀.1 D₁.1 a)
        (auxiliaryDerivative D₀.1 D₁.1 a)) ≤
      2 * leftResidualEnergy P.φ D₀ D₁ := by
    have hm := arcSquare_mono hi2 le_rfl hvd.le hdT.le
    rw [he] at hm
    simpa only [leftResidualEnergy, show π + π / 2 = 3 * π / 2 by ring,
      show π + (π - P.φ) = 3 * π / 2 + (π / 2 - P.φ) by ring] using hm
  exact left_auxiliary_penalty hp (by linarith) hvd hdT
    (auxiliaryDifference_continuous D₀ D₁ a)
    (fun t _ => auxiliaryDifference_rightDeriv D₀ D₁ a t)
    hcontact.2.1 hcontact.2.2.2 hprofile
    (intervalIntegrable_subinterval hi le_rfl hvd.le hdT.le)
    (intervalIntegrable_subinterval hi2 le_rfl hvd.le hdT.le) hbound (penaltyWeights_pos hP).2

/-- The full-Q budget for actual cap residuals and the two endpoint penalties. -/
theorem feasible_triple_endpoint_energy {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    ‖tripleResidualVector hP hbox x‖ ^ 2 +
      (endpointB P (capDifference P.cap x.1.1.1) -
        rightWallSlack x (criticalLeft P) / cos (criticalLeft P)) ^ 2 / penaltyWeightB P +
      (endpointD P (capDifference P.cap x.1.1.1) +
        leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P)) ^ 2 / penaltyWeightD P ≤
      2 * qDeficit P x := by
  rw [tripleResidualVector_norm_sq]
  have hidentity := wide_deficit_eq_slack_add_integrals hP hbox x
  have hL : 0 ≤ wideDualSlack hP hbox x :=
    neg_nonneg.mpr (gerver_wide_firstVariation_nonpos hP hbox x)
  have hB := triple_right_penalty hP hbox x
  have hD := triple_left_penalty hP hbox x
  change area (gerverSofa P) - wideUpperQ P.φ x = _ at hidentity
  unfold wideResidualEnergy at hidentity
  unfold qDeficit
  linarith

end MovingSofaQuantitative
