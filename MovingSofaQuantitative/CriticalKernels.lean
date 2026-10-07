module

public import MovingSofaQuantitative.TripleEnergy

/-!
# The actual two-penalty kernel model

Uncompiled proof source. The representers below are constructed from the exact
evaluation kernels, and their pairings are proved to be the endpoint functionals
of the actual input cap. Consequently the augmented energy theorem is about
feasible wide triples, not an independently postulated quadratic form.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

abbrev UpperAngle := {t : ℝ // t ∈ Icc 0 π}

/-- Four distinguished angles of the endpoint penalties. -/
def anglePhi {P : GerverParams} (hP : P.IsSolution) : UpperAngle :=
  ⟨P.φ, ⟨(gm_φ_pos hP).le, by linarith [gm_φ_lt_θ hP, gm_θ_lt_c hP, pi_pos]⟩⟩

def angleCriticalLeft {P : GerverParams} (hP : P.IsSolution) : UpperAngle :=
  ⟨criticalLeft P, by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := critical_arc_order hP
    exact ⟨by linarith, by linarith [pi_pos]⟩⟩

def angleCriticalRight {P : GerverParams} (hP : P.IsSolution) : UpperAngle :=
  ⟨criticalRight P, by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := critical_arc_order hP
    exact ⟨by linarith [pi_pos], by linarith⟩⟩

def angleLastCut {P : GerverParams} (hP : P.IsSolution) : UpperAngle :=
  ⟨π - P.φ, by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := critical_arc_order hP
    exact ⟨by linarith [pi_pos], h7.le⟩⟩

def penaltyKernelB {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : FourKernel P.φ :=
  ((evaluationKernel (gm_φ_mem_Ioo hP hbox) (anglePhi hP)).scale (1 / cos P.φ)).add
    ((evaluationKernel (gm_φ_mem_Ioo hP hbox) (angleCriticalLeft hP)).scale
      (-(1 / cos (criticalLeft P))))

def penaltyKernelD {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : FourKernel P.φ :=
  ((evaluationKernel (gm_φ_mem_Ioo hP hbox) (angleCriticalRight hP)).scale
    (1 / sin (π - P.φ - criticalRight P))).add
    ((evaluationKernel (gm_φ_mem_Ioo hP hbox) (angleLastCut hP)).scale (-penaltyWeightD P))

theorem penaltyKernelB_pairing {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {f df : ℝ → ℝ} (hf : FourResidualData P.φ f df) :
    (penaltyKernelB hP hbox).pairing f df = endpointB P f := by
  unfold penaltyKernelB
  rw [FourKernel.pairing_add _ _ (gm_φ_mem_Ioo hP hbox) hf]
  simp only [FourKernel.pairing_scale, evaluationKernel_pairing _ hf,
    anglePhi, angleCriticalLeft, endpointB]
  ring

theorem penaltyKernelD_pairing {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {f df : ℝ → ℝ} (hf : FourResidualData P.φ f df) :
    (penaltyKernelD hP hbox).pairing f df = endpointD P f := by
  unfold penaltyKernelD
  rw [FourKernel.pairing_add _ _ (gm_φ_mem_Ioo hP hbox) hf]
  simp only [FourKernel.pairing_scale, evaluationKernel_pairing _ hf,
    angleCriticalRight, angleLastCut, endpointD]
  ring

/-- The continuum two-evaluation obstruction, before division by its weights. -/
def pairEvaluationKernel {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) : FourKernel P.φ :=
  ((evaluationKernel (gm_φ_mem_Ioo hP hbox) t).scale (cos u)).add
    ((evaluationKernel (gm_φ_mem_Ioo hP hbox) u).scale (-cos t))

theorem pairEvaluationKernel_pairing {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {f df : ℝ → ℝ} (hf : FourResidualData P.φ f df) (t u : UpperAngle) :
    (pairEvaluationKernel hP hbox t u).pairing f df = f t * cos u - f u * cos t := by
  unfold pairEvaluationKernel
  rw [FourKernel.pairing_add _ _ (gm_φ_mem_Ioo hP hbox) hf]
  simp only [FourKernel.pairing_scale, evaluationKernel_pairing _ hf]
  ring

/-- No geometric hypothesis is hidden in the Hilbert-space adapter. -/
theorem actual_augmented_energy_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    augmentedEnergy (penaltyWeightB P) (penaltyWeightD P)
      (rightWallSlack x (criticalLeft P) / cos (criticalLeft P))
      (-(leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P)))
      (penaltyKernelB hP hbox).vector (penaltyKernelD hP hbox).vector
      (tripleResidualVector hP hbox x) ≤ 2 * qDeficit P x := by
  have hB : ⟪(penaltyKernelB hP hbox).vector, tripleResidualVector hP hbox x⟫_ℝ =
      endpointB P (capDifference P.cap x.1.1.1) := by
    rw [tripleResidualVector, FourKernel.inner_vector_residual, penaltyKernelB_pairing]
  have hD : ⟪(penaltyKernelD hP hbox).vector, tripleResidualVector hP hbox x⟫_ℝ =
      endpointD P (capDifference P.cap x.1.1.1) := by
    rw [tripleResidualVector, FourKernel.inner_vector_residual, penaltyKernelD_pairing]
  unfold augmentedEnergy
  rw [hB, hD, sub_neg_eq_add]
  exact feasible_triple_endpoint_energy hP hbox x

/-- The squared corrected evaluation norm that the finite certificate bounds. -/
def correctedPairSquare {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) : ℝ :=
  let vB := (penaltyKernelB hP hbox).vector
  let vD := (penaltyKernelD hP hbox).vector
  let k := (pairEvaluationKernel hP hbox t u).vector
  2 * (‖k‖ ^ 2 - inverseCoefficient1 (penaltyWeightB P) (penaltyWeightD P) vB vD k * ⟪k, vB⟫_ℝ -
    inverseCoefficient2 (penaltyWeightB P) (penaltyWeightD P) vB vD k * ⟪k, vD⟫_ℝ)

def pairSlackSensitivity {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) : ℝ :=
  let vB := (penaltyKernelB hP hbox).vector
  let vD := (penaltyKernelD hP hbox).vector
  let k := (pairEvaluationKernel hP hbox t u).vector
  |inverseCoefficient1 (penaltyWeightB P) (penaltyWeightD P) vB vD k / cos (criticalLeft P)| +
    |inverseCoefficient2 (penaltyWeightB P) (penaltyWeightD P) vB vD k /
      sin (π - P.φ - criticalRight P)|

/-- Concrete certificate specification: all entries are the actual continuum
kernel integrals defined above. A proof must cover every pair of angles. -/
def CriticalOperatorBound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : Prop :=
  ∀ t u : UpperAngle,
    correctedPairSquare hP hbox t u ≤ ((93 / 100) * (|cos t| + |cos u|)) ^ 2 ∧
      pairSlackSensitivity hP hbox t u ≤ (1 / 2) * (|cos t| + |cos u|)

/-- The point-pair estimate before applying the exact quotient formula.
Only the two independent numerical/endpoint ingredients remain explicit. -/
theorem actual_pair_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hoperator : CriticalOperatorBound hP hbox) (x : WideTriple P.φ)
    {σ : ℝ} (hσ : 0 ≤ σ)
    (hB : |rightWallSlack x (criticalLeft P)| ≤ σ)
    (hD : |leftWallSlack x (criticalRight P)| ≤ σ)
    (t u : UpperAngle) :
    |capDifference P.cap x.1.1.1 t * cos u - capDifference P.cap x.1.1.1 u * cos t| ≤
      ((93 / 100) * sqrt (qDeficit P x) + σ / 2) * (|cos t| + |cos u|) := by
  let vB := (penaltyKernelB hP hbox).vector
  let vD := (penaltyKernelD hP hbox).vector
  let k := (pairEvaluationKernel hP hbox t u).vector
  let aB := inverseCoefficient1 (penaltyWeightB P) (penaltyWeightD P) vB vD k
  let aD := inverseCoefficient2 (penaltyWeightB P) (penaltyWeightD P) vB vD k
  have hΔ : 0 ≤ qDeficit P x := by
    unfold qDeficit
    have h := wideUpperQ_le_gerver hP hbox x
    rw [wideGerver_value] at h
    linarith
  have hraw := rank_two_full_energy_bound (penaltyWeights_pos hP).1 (penaltyWeights_pos hP).2 hΔ
    vB vD k (tripleResidualVector hP hbox x)
    (rightWallSlack x (criticalLeft P) / cos (criticalLeft P))
    (-(leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P)))
    (actual_augmented_energy_bound hP hbox x)
  have hpair : ⟪k, tripleResidualVector hP hbox x⟫_ℝ =
      capDifference P.cap x.1.1.1 t * cos u - capDifference P.cap x.1.1.1 u * cos t := by
    rw [tripleResidualVector, FourKernel.inner_vector_residual, pairEvaluationKernel_pairing]
  have hroot : sqrt (correctedPairSquare hP hbox t u) ≤
      (93 / 100) * (|cos t| + |cos u|) := by
    apply (sqrt_le_left (by positivity)).2
    exact (hoperator t u).1
  have herr : |aB * (rightWallSlack x (criticalLeft P) / cos (criticalLeft P)) +
      aD * (-(leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P)))| ≤
      pairSlackSensitivity hP hbox t u * σ := by
    have hb := mul_le_mul_of_nonneg_left hB (abs_nonneg (aB / cos (criticalLeft P)))
    have hd := mul_le_mul_of_nonneg_left hD (abs_nonneg (aD / sin (π - P.φ - criticalRight P)))
    have he := abs_add_le (aB * (rightWallSlack x (criticalLeft P) / cos (criticalLeft P)))
      (aD * (-(leftWallSlack x (criticalRight P) / sin (π - P.φ - criticalRight P))))
    simp only [abs_mul, abs_neg, abs_div] at he hb hd
    unfold pairSlackSensitivity
    dsimp only
    nlinarith only [he, hb, hd]
  rw [hpair] at hraw
  have hr := mul_le_mul_of_nonneg_right hroot (sqrt_nonneg (qDeficit P x))
  have he := mul_le_mul_of_nonneg_right (hoperator t u).2 hσ
  change |capDifference P.cap x.1.1.1 t * cos u - capDifference P.cap x.1.1.1 u * cos t| ≤
    sqrt (correctedPairSquare hP hbox t u) * sqrt (qDeficit P x) + _ at hraw
  nlinarith only [hraw, herr, hr, he]

end MovingSofaQuantitative
