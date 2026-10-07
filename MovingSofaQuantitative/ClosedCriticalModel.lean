module

public import MovingSofaQuantitative.Certificates.KernelExpression
public import MovingSofaQuantitative.CorrectedGramGeometry

/-!
# Finite scalar coordinates of the actual two-penalty operator

Uncompiled proof source. Each scalar Gram entry is connected to the real
Hilbert vectors by StableGram and the finite-combination lemma below. These
coordinates do not replace the domain of feasible triples by a finite mesh.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

open Certificates.KernelExpression (realCombinationGram)

/-- Finite linear combination of continuum evaluation kernels. -/
def combinationKernel {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ks : List (UpperAngle × ℝ)) : FourKernel φ :=
  FourKernel.sum (ks.map fun k => (evaluationKernel hφ k.1).scale k.2)

def realPairs (ks : List (UpperAngle × ℝ)) : List (ℝ × ℝ) :=
  ks.map fun k => (k.1.1, k.2)

theorem combinationKernel_gram {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ks ls : List (UpperAngle × ℝ)) :
    (combinationKernel hφ ks).gram (combinationKernel hφ ls) =
      realCombinationGram φ (realPairs ks) (realPairs ls) := by
  simp only [combinationKernel, FourKernel.gram_sum_left, FourKernel.gram_sum_right,
    FourKernel.gram_scale_left, FourKernel.gram_scale_right, List.map_map,
    realCombinationGram, realPairs, stableEvaluationGram_correct hφ]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  ring

/-- A scalar record suitable for interval evaluation. -/
structure GramCoordinates where
  d₁ : ℝ
  d₂ : ℝ
  g₁₁ : ℝ
  g₁₂ : ℝ
  g₂₂ : ℝ
  k₀ : ℝ
  k₁ : ℝ
  k₂ : ℝ

namespace GramCoordinates

def s₁₁ (m : GramCoordinates) : ℝ := m.d₁ + m.g₁₁
def s₂₂ (m : GramCoordinates) : ℝ := m.d₂ + m.g₂₂
def det (m : GramCoordinates) : ℝ := m.s₁₁ * m.s₂₂ - m.g₁₂ ^ 2

def a₁ (m : GramCoordinates) : ℝ := (m.s₂₂ * m.k₁ - m.g₁₂ * m.k₂) / m.det
def a₂ (m : GramCoordinates) : ℝ := (m.s₁₁ * m.k₂ - m.g₁₂ * m.k₁) / m.det

def value (m : GramCoordinates) : ℝ := m.k₀ - m.a₁ * m.k₁ - m.a₂ * m.k₂

/-- Exact closed scalar form used by the checker. -/
theorem value_formula (m : GramCoordinates) :
    m.value = m.k₀ -
      (m.s₂₂ * m.k₁ ^ 2 - 2 * m.g₁₂ * m.k₁ * m.k₂ + m.s₁₁ * m.k₂ ^ 2) / m.det := by
  unfold value a₁ a₂
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ofVectors (d₁ d₂ : ℝ) (v₁ v₂ k : E) : GramCoordinates :=
  ⟨d₁, d₂, ‖v₁‖ ^ 2, ⟪v₁, v₂⟫_ℝ, ‖v₂‖ ^ 2, ‖k‖ ^ 2,
    ⟪k, v₁⟫_ℝ, ⟪k, v₂⟫_ℝ⟩

theorem ofVectors_a₁ (d₁ d₂ : ℝ) (v₁ v₂ k : E) :
    (ofVectors d₁ d₂ v₁ v₂ k).a₁ = inverseCoefficient1 d₁ d₂ v₁ v₂ k := rfl

theorem ofVectors_a₂ (d₁ d₂ : ℝ) (v₁ v₂ k : E) :
    (ofVectors d₁ d₂ v₁ v₂ k).a₂ = inverseCoefficient2 d₁ d₂ v₁ v₂ k := rfl

theorem ofVectors_value (d₁ d₂ : ℝ) (v₁ v₂ k : E) :
    (ofVectors d₁ d₂ v₁ v₂ k).value = correctedSquare d₁ d₂ v₁ v₂ k := by
  simp only [value, ofVectors_a₁, ofVectors_a₂, correctedSquare, correctedInner,
    real_inner_self_eq_norm_sq, ofVectors]

theorem ofVectors_det_pos {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (v₁ v₂ k : E) :
    0 < (ofVectors d₁ d₂ v₁ v₂ k).det := gramDet_pos h₁ h₂ v₁ v₂

end GramCoordinates

/-- The numerical parameterization of the two auxiliary endpoint weights. -/
def scalarWeightB (φ θ : ℝ) : ℝ := tan (π / 2 - θ) - tan φ

def scalarWeightD (φ θ : ℝ) : ℝ :=
  cos (π - φ - (π / 2 + θ)) / sin (π - φ - (π / 2 + θ)) - tan φ

def scalarB (φ θ : ℝ) : List (ℝ × ℝ) :=
  [(φ, 1 / cos φ), (π / 2 - θ, -(1 / cos (π / 2 - θ)))]

def scalarD (φ θ : ℝ) : List (ℝ × ℝ) :=
  [(π / 2 + θ, 1 / sin (π - φ - (π / 2 + θ))), (π - φ, -scalarWeightD φ θ)]

/-- All entries are finite sums of exact stable continuum primitives. -/
def criticalCoordinates (φ θ : ℝ) (ks : List (ℝ × ℝ)) : GramCoordinates :=
  let B := scalarB φ θ
  let D := scalarD φ θ
  ⟨scalarWeightB φ θ, scalarWeightD φ θ,
    realCombinationGram φ B B, realCombinationGram φ B D, realCombinationGram φ D D,
    realCombinationGram φ ks ks, realCombinationGram φ ks B, realCombinationGram φ ks D⟩

def penaltyCombinationB {P : GerverParams} (hP : P.IsSolution) : List (UpperAngle × ℝ) :=
  [(anglePhi hP, 1 / cos P.φ),
   (angleCriticalLeft hP, -(1 / cos (criticalLeft P)))]

def penaltyCombinationD {P : GerverParams} (hP : P.IsSolution) : List (UpperAngle × ℝ) :=
  [(angleCriticalRight hP, 1 / sin (π - P.φ - criticalRight P)),
   (angleLastCut hP, -penaltyWeightD P)]

private theorem scalarB_realPairs {P : GerverParams} (hP : P.IsSolution) :
    scalarB P.φ P.θ = realPairs (penaltyCombinationB hP) := rfl

private theorem scalarD_realPairs {P : GerverParams} (hP : P.IsSolution) :
    scalarD P.φ P.θ = realPairs (penaltyCombinationD hP) := rfl

theorem penaltyCombinationB_vector {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (combinationKernel (GerverParams.gm_φ_mem_Ioo hP hbox) (penaltyCombinationB hP)).vector =
      (penaltyKernelB hP hbox).vector := by
  simp only [combinationKernel, penaltyCombinationB, penaltyKernelB,
    List.map_cons, List.map_nil, FourKernel.sum, FourKernel.vector_add,
    FourKernel.vector_zero, add_zero]

theorem penaltyCombinationD_vector {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (combinationKernel (GerverParams.gm_φ_mem_Ioo hP hbox) (penaltyCombinationD hP)).vector =
      (penaltyKernelD hP hbox).vector := by
  simp only [combinationKernel, penaltyCombinationD, penaltyKernelD,
    List.map_cons, List.map_nil, FourKernel.sum, FourKernel.vector_add,
    FourKernel.vector_zero, add_zero]

/-- Exact identification of the finite scalar model with the actual operator.
The domain parameters and all angle membership proofs come from the reference. -/
theorem criticalCoordinates_correct {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (ks : List (UpperAngle × ℝ)) :
    criticalCoordinates P.φ P.θ (realPairs ks) =
      GramCoordinates.ofVectors (penaltyWeightB P) (penaltyWeightD P)
        (penaltyKernelB hP hbox).vector (penaltyKernelD hP hbox).vector
        (combinationKernel (GerverParams.gm_φ_mem_Ioo hP hbox) ks).vector := by
  let hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  unfold criticalCoordinates
  rw [scalarB_realPairs hP, scalarD_realPairs hP]
  simp only [← combinationKernel_gram hφ, ← FourKernel.inner_vectors,
    penaltyCombinationB_vector hP hbox, penaltyCombinationD_vector hP hbox,
    real_inner_self_eq_norm_sq]
  rfl

/-- Centering each kernel does not alter the two-point quotient obstruction. -/
def centeredEvaluationVector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (t : UpperAngle) :
    ResidualHilbert φ :=
  (evaluationKernel hφ t).vector - (cos t / 2) •
    (evaluationKernel hφ ⟨0, ⟨le_rfl, pi_pos.le⟩⟩).vector

def centeredCombination (t : UpperAngle) : List (UpperAngle × ℝ) :=
  [(t, 1), (⟨0, ⟨le_rfl, pi_pos.le⟩⟩, -(cos t / 2))]

def pairCombination (t u : UpperAngle) : List (UpperAngle × ℝ) :=
  [(t, cos u), (u, -cos t)]

theorem centeredCombination_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (t : UpperAngle) :
    (combinationKernel hφ (centeredCombination t)).vector = centeredEvaluationVector hφ t := by
  simp only [combinationKernel, centeredCombination, List.map_cons, List.map_nil,
    FourKernel.sum, FourKernel.vector_add, FourKernel.vector_scale,
    FourKernel.vector_zero, add_zero, one_smul, centeredEvaluationVector,
    neg_smul, sub_eq_add_neg]

theorem pairCombination_vector {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    (combinationKernel (GerverParams.gm_φ_mem_Ioo hP hbox) (pairCombination t u)).vector =
      (pairEvaluationKernel hP hbox t u).vector := by
  simp only [combinationKernel, pairCombination, pairEvaluationKernel, List.map_cons,
    List.map_nil, FourKernel.sum, FourKernel.vector_add, FourKernel.vector_zero, add_zero]

theorem pairEvaluationVector_centered {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (t u : UpperAngle) :
    (pairEvaluationKernel hP hbox t u).vector =
      cos u • centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) t +
      (-cos t) • centeredEvaluationVector (GerverParams.gm_φ_mem_Ioo hP hbox) u := by
  simp only [pairEvaluationKernel, FourKernel.vector_add, FourKernel.vector_scale,
    centeredEvaluationVector, smul_sub, smul_smul, neg_smul]
  have hcoef : cos u * (cos t / 2) = cos t * (cos u / 2) := by ring
  rw [hcoef]
  abel

end MovingSofaQuantitative
