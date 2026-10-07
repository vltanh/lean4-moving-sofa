module

public import MovingSofaQuantitative.Certificates.CriticalExpression
public import MovingSofaQuantitative.EndpointSlacks

/-!
# From an accepted scalar certificate to the actual full-Q theorem

Uncompiled proof source. The transfer below discharges the model-identification,
parameter-domain and zero-cosine cases. Its one numerical input is an explicit
closed Boolean check, not an assumed inequality on an arbitrary Hilbert kernel.
The acceptance theorem itself is kept in a separate file.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

namespace CE := Certificates.CriticalExpression
namespace KE := Certificates.KernelExpression

/-- The four real variables interpreted by the continuum certificate. -/
def operatorEnvironment (P : GerverParams) (t u : UpperAngle) : Fin 4 → ℝ :=
  ![P.φ, P.θ, t.1, u.1]

theorem operatorEnvironment_inBox {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) : Certificates.InBox CE.rootBox (operatorEnvironment P t u) := by
  have hb := GerverParams.romik_bounds hP hbox
  have hpi := Certificates.Interval.contains_pi
  intro i
  fin_cases i
  · simpa only [CE.rootBox, operatorEnvironment, Matrix.cons_val_zero,
      Certificates.Interval.Contains] using hb.φ_mem
  · simpa only [CE.rootBox, operatorEnvironment, Matrix.cons_val_one,
      Certificates.Interval.Contains] using hb.θ_mem
  · exact ⟨t.2.1, t.2.2.trans hpi.2⟩
  · exact ⟨u.2.1, u.2.2.trans hpi.2⟩

def centeredCorrectedSquare {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t : UpperAngle) : ℝ :=
  correctedSquare (penaltyWeightB P) (penaltyWeightD P)
    (penaltyKernelB hP hbox).vector (penaltyKernelD hP hbox).vector
    (centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) t)

def centeredSlackSensitivity {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t : UpperAngle) : ℝ :=
  let B := (penaltyKernelB hP hbox).vector
  let D := (penaltyKernelD hP hbox).vector
  let k := centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) t
  |inverseCoefficient1 (penaltyWeightB P) (penaltyWeightD P) B D k / cos (criticalLeft P)| +
    |inverseCoefficient2 (penaltyWeightB P) (penaltyWeightD P) B D k /
      sin (π - P.φ - criticalRight P)|

theorem pointT_model_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    CE.pointT.value.realValue (operatorEnvironment P t u) = centeredCorrectedSquare hP hbox t := by
  rw [CE.Coordinates.value_real]
  unfold CE.pointT
  rw [CE.model_real]
  change (criticalCoordinates P.φ P.θ (realPairs (centeredCombination t))).value = _
  rw [criticalCoordinates_correct hP hbox, GramCoordinates.ofVectors_value,
    centeredCombination_vector]
  rfl

theorem pointU_model_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    CE.pointU.value.realValue (operatorEnvironment P t u) = centeredCorrectedSquare hP hbox u := by
  rw [CE.Coordinates.value_real]
  unfold CE.pointU
  rw [CE.model_real]
  change (criticalCoordinates P.φ P.θ (realPairs (centeredCombination u))).value = _
  rw [criticalCoordinates_correct hP hbox, GramCoordinates.ofVectors_value,
    centeredCombination_vector]
  rfl

theorem pair_model_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    2 * CE.pairModel.value.realValue (operatorEnvironment P t u) = correctedPairSquare hP hbox t u := by
  rw [CE.Coordinates.value_real]
  unfold CE.pairModel
  rw [CE.model_real]
  change 2 * (criticalCoordinates P.φ P.θ (realPairs (pairCombination t u))).value = _
  rw [criticalCoordinates_correct hP hbox, GramCoordinates.ofVectors_value,
    pairCombination_vector]
  simp only [correctedSquare, correctedInner, real_inner_self_eq_norm_sq, correctedPairSquare]

theorem sensitivityT_model_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    CE.sensT.realValue (operatorEnvironment P t u) = centeredSlackSensitivity hP hbox t := by
  unfold CE.sensT CE.sensitivity
  simp only [Certificates.BranchExpr.realValue, KE.bdiv, KE.lift,
    KE.sub, KE.halfPi, KE.div, KE.rat, Certificates.TrigExpr.realValue,
    CE.Coordinates.a₁_real, CE.Coordinates.a₂_real]
  unfold CE.pointT
  rw [CE.model_real]
  change |(criticalCoordinates P.φ P.θ (realPairs (centeredCombination t))).a₁ /
      cos (criticalLeft P)| +
    |(criticalCoordinates P.φ P.θ (realPairs (centeredCombination t))).a₂ /
      sin (π - P.φ - criticalRight P)| = _
  rw [criticalCoordinates_correct hP hbox, GramCoordinates.ofVectors_a₁,
    GramCoordinates.ofVectors_a₂, centeredCombination_vector]
  rfl

theorem sensitivityU_model_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    CE.sensU.realValue (operatorEnvironment P t u) = centeredSlackSensitivity hP hbox u := by
  unfold CE.sensU CE.sensitivity
  simp only [Certificates.BranchExpr.realValue, KE.bdiv, KE.lift,
    KE.sub, KE.halfPi, KE.div, KE.rat, Certificates.TrigExpr.realValue,
    CE.Coordinates.a₁_real, CE.Coordinates.a₂_real]
  unfold CE.pointU
  rw [CE.model_real]
  change |(criticalCoordinates P.φ P.θ (realPairs (centeredCombination u))).a₁ /
      cos (criticalLeft P)| +
    |(criticalCoordinates P.φ P.θ (realPairs (centeredCombination u))).a₂ /
      sin (π - P.φ - criticalRight P)| = _
  rw [criticalCoordinates_correct hP hbox, GramCoordinates.ofVectors_a₁,
    GramCoordinates.ofVectors_a₂, centeredCombination_vector]
  rfl

/-- Linearity of the inverse coefficients makes point sensitivities sufficient
for the pair sensitivity, also at a zero cosine. -/
theorem pairSlackSensitivity_le_centered {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (t u : UpperAngle) :
    pairSlackSensitivity hP hbox t u ≤
      |cos u| * centeredSlackSensitivity hP hbox t +
      |cos t| * centeredSlackSensitivity hP hbox u := by
  let B := (penaltyKernelB hP hbox).vector
  let D := (penaltyKernelD hP hbox).vector
  let kt := centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) t
  let ku := centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) u
  let a₁ := inverseCoefficient1 (penaltyWeightB P) (penaltyWeightD P) B D
  let a₂ := inverseCoefficient2 (penaltyWeightB P) (penaltyWeightD P) B D
  have h1 := abs_add_le
    (cos u * (a₁ kt / cos (criticalLeft P)))
    ((-cos t) * (a₁ ku / cos (criticalLeft P)))
  have h2 := abs_add_le
    (cos u * (a₂ kt / sin (π - P.φ - criticalRight P)))
    ((-cos t) * (a₂ ku / sin (π - P.φ - criticalRight P)))
  unfold pairSlackSensitivity
  rw [pairEvaluationVector_centered hP hbox t u]
  simp only [inverseCoefficient1_add, inverseCoefficient2_add,
    inverseCoefficient1_smul, inverseCoefficient2_smul, add_div,
    mul_div_assoc, abs_mul, abs_neg] at h1 h2 ⊢
  unfold centeredSlackSensitivity
  dsimp only [B, D, kt, ku, a₁, a₂] at h1 h2
  nlinarith only [h1, h2]

/-- A certified entire-box scalar statement proves the concrete continuum
operator required by the actual feasible-triple energy estimate. -/
theorem operator_of_model_certificate
    (hcert : ∀ x, Certificates.InBox CE.rootBox x → CE.LeafProperty x)
    {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CriticalOperatorBound hP hbox := by
  intro t u
  have h := hcert (operatorEnvironment P t u) (operatorEnvironment_inBox hP hbox t u)
  rcases h with ⟨hsT, hsU, hdiag | hpair⟩
  · rw [pointT_model_correct hP hbox, pointU_model_correct hP hbox] at hdiag
    rw [sensitivityT_model_correct hP hbox, sensitivityU_model_correct hP hbox] at hsT hsU
    constructor
    · have hp := corrected_pair_of_diagonal (penaltyWeights_pos hP).1 (penaltyWeights_pos hP).2
        (penaltyKernelB hP hbox).vector (penaltyKernelD hP hbox).vector
        (centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) t)
        (centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) u)
        hdiag.1.le hdiag.2.le (cos u) (-cos t)
      rw [← pairEvaluationVector_centered hP hbox t u] at hp
      simpa only [correctedSquare, correctedInner, real_inner_self_eq_norm_sq,
        correctedPairSquare, abs_neg, add_comm] using hp
    · have hp := pairSlackSensitivity_le_centered hP hbox t u
      have ht := mul_le_mul_of_nonneg_left hsT.le (abs_nonneg (cos u))
      have hu := mul_le_mul_of_nonneg_left hsU.le (abs_nonneg (cos t))
      nlinarith only [hp, ht, hu]
  · rw [pair_model_correct hP hbox] at hpair
    rw [sensitivityT_model_correct hP hbox, sensitivityU_model_correct hP hbox] at hsT hsU
    refine ⟨hpair.le, ?_⟩
    have hp := pairSlackSensitivity_le_centered hP hbox t u
    have ht := mul_le_mul_of_nonneg_left hsT.le (abs_nonneg (cos u))
    have hu := mul_le_mul_of_nonneg_left hsU.le (abs_nonneg (cos t))
    nlinarith only [hp, ht, hu]

/-- A closed checker invocation is the sole numerical argument of this transfer. -/
theorem operator_of_closed_check (depth : ℕ) (hcheck : CE.closedCheck depth = true)
    {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CriticalOperatorBound hP hbox :=
  operator_of_model_certificate (CE.closedCheck_sound depth hcheck) hP hbox

end MovingSofaQuantitative
