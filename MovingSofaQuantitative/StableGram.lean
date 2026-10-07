module

public import MovingSofaQuantitative.EvaluationPieces
public import MovingSofaQuantitative.CriticalKernels

/-!
# Stable scalar Gram entries, including the terminal normal

Uncompiled proof source. A last-arc self/cross integral is replaced by its exact
closed form before interval evaluation. In particular the evaluator need not
bound csc(pi), and it never accepts an improper integral times a vanishing
coefficient. All other entries use finite primitive sums on compact overlaps.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped RealInnerProductSpace
open MovingSofaStability MovingSofaOptimality

namespace MovingSofaQuantitative

private theorem top_not_first {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    ¬π / 2 ≤ φ := by linarith [hφ.2, pi_pos]

private theorem top_not_middle {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    ¬π / 2 ≤ π / 2 - φ := by linarith [hφ.1]

/-- A point-supported atom is zero in L2, regardless of its assigned value. -/
theorem kernelAtom_singleton_vector (φ : ℝ) (j : Fin 4) (a : ℝ)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc a a)) :
    (kernelAtom φ j a a k hk).vector = 0 := by
  rw [← FourKernel.vector_zero]
  apply FourKernel.vector_eq_of_ae
  intro i
  filter_upwards [ae_neq a] with u hu
  have hout : u ∉ Icc a a := by simpa only [Icc_self, mem_singleton_iff] using hu
  simp [kernelAtom, FourKernel.zero, hout]

/-- The top support difference is pinned to zero. Its kernel is also zero in
the full ambient residual Hilbert space, not just on realized residuals. -/
theorem evaluationKernel_top_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (evaluationKernel hφ ⟨π / 2, by constructor <;> linarith [pi_pos]⟩).vector = 0 := by
  unfold evaluationKernel
  simp only [top_not_first hφ, top_not_middle hφ, ↓reduceDIte, le_refl]
  unfold thirdEvaluationKernel
  simp only [FourKernel.vector_add, FourKernel.vector_scale, cos_pi_div_two,
    zero_div, zero_mul, zero_smul, add_zero]
  rw [kernelAtom_singleton_vector, smul_zero]

/-- The terminal endpoint has no residual kernel. -/
theorem evaluationKernel_pi_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (evaluationKernel hφ ⟨π, ⟨pi_pos.le, le_rfl⟩⟩).vector = 0 := by
  have h1 : ¬π ≤ φ := by linarith [hφ.2, pi_pos]
  have h2 : ¬π ≤ π / 2 - φ := by linarith [hφ.1, pi_pos]
  have h3 : ¬π ≤ π / 2 := by linarith [pi_pos]
  simp [evaluationKernel, h1, h2, h3]

/-- On the closed-left, open-right last arc the last-kernel formula is valid
also at pi/2, where both constructions represent the zero vector. -/
theorem evaluationKernel_last_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t : UpperAngle) (ht : t.1 ∈ Ico (π / 2) π) :
    (evaluationKernel hφ t).vector = (lastEvaluationKernel (φ := φ) ht).vector := by
  rcases ht.1.eq_or_lt with he | he
  · have ht' : t.1 = π / 2 := he.symm
    have hsub : t = ⟨π / 2, by constructor <;> linarith [pi_pos]⟩ := Subtype.ext ht'
    subst t
    rw [evaluationKernel_top_vector]
    unfold lastEvaluationKernel
    rw [FourKernel.vector_scale, kernelAtom_singleton_vector, smul_zero]
  · have h1 : ¬t.1 ≤ φ := by linarith [hφ.2, pi_pos]
    have h2 : ¬t.1 ≤ π / 2 - φ := by linarith [hφ.1]
    have h3 : ¬t.1 ≤ π / 2 := not_le.mpr he
    simp only [evaluationKernel, h1, h2, h3, ht.2, ↓reduceDIte]

/-- A stable exact formula for two last-arc evaluations. -/
theorem evaluationKernel_gram_last {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t u : UpperAngle) (ht : π / 2 ≤ t.1) (hu : π / 2 ≤ u.1) :
    (evaluationKernel hφ t).gram (evaluationKernel hφ u) =
      -sin (max t.1 u.1) * cos (min t.1 u.1) := by
  by_cases htπ : t.1 = π
  · have hsub : t = ⟨π, ⟨pi_pos.le, le_rfl⟩⟩ := Subtype.ext htπ
    subst t
    rw [← FourKernel.inner_vectors, evaluationKernel_pi_vector, inner_zero_left]
    simp [max_eq_left u.2.2]
  by_cases huπ : u.1 = π
  · have hsub : u = ⟨π, ⟨pi_pos.le, le_rfl⟩⟩ := Subtype.ext huπ
    subst u
    rw [← FourKernel.inner_vectors, evaluationKernel_pi_vector, inner_zero_right]
    simp [max_eq_right t.2.2]
  have ht' : t.1 ∈ Ico (π / 2) π := ⟨ht, lt_of_le_of_ne t.2.2 htπ⟩
  have hu' : u.1 ∈ Ico (π / 2) π := ⟨hu, lt_of_le_of_ne u.2.2 huπ⟩
  rw [← FourKernel.inner_vectors, evaluationKernel_last_vector hφ t ht',
    evaluationKernel_last_vector hφ u hu', FourKernel.inner_vectors]
  unfold lastEvaluationKernel
  rw [FourKernel.gram_scale_left, FourKernel.gram_scale_right]
  rw [kernelAtom_gram_interval 3 (π / 2) t.1 (π / 2) u.1
    le_rfl t.2.2 le_rfl u.2.2]
  have hmin : π / 2 ≤ min t.1 u.1 := le_min ht hu
  have hsin : ∀ v ∈ Icc (π / 2) (min t.1 u.1), sin v ≠ 0 := by
    intro v hv
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hv.1, pi_pos])
      (hv.2.trans_lt ((min_le_left _ _).trans_lt ht'.2))).ne'
  simp only [max_self, dif_pos hmin]
  have hI : (∫ v in (π / 2)..(min t.1 u.1), (1 / sin v) * (1 / sin v)) =
      cotangent (π / 2) - cotangent (min t.1 u.1) := by
    simpa only [pow_two] using cosecant_sq_integral hmin hsin
  rw [hI]
  simp only [cotangent, cos_pi_div_two, sin_pi_div_two, zero_div, zero_sub]
  have hn := hsin (min t.1 u.1) ⟨hmin, le_rfl⟩
  rcases le_total t.1 u.1 with htu | hut
  · rw [min_eq_left htu, max_eq_right htu] at *
    field_simp [hn]
    ring
  · rw [min_eq_right hut, max_eq_left hut] at *
    field_simp [hn]
    ring

/-- Stable primitive-based evaluation for numerical certificates. -/
def stableEvaluationGram (φ t u : ℝ) : ℝ :=
  if π / 2 ≤ t ∧ π / 2 ≤ u then -sin (max t u) * cos (min t u)
  else evaluationPieceGram φ t u

theorem stableEvaluationGram_correct {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t u : UpperAngle) :
    stableEvaluationGram φ t u = (evaluationKernel hφ t).gram (evaluationKernel hφ u) := by
  unfold stableEvaluationGram
  split_ifs with hlast
  · exact (evaluationKernel_gram_last hφ t u hlast.1 hlast.2).symm
  · exact (evaluationGram_eq_pieceSum hφ t u).symm

/-- Symmetry is proved from the continuum Gram entry, not imposed on data. -/
theorem stableEvaluationGram_symm {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t u : UpperAngle) : stableEvaluationGram φ t u = stableEvaluationGram φ u t := by
  rw [stableEvaluationGram_correct hφ, stableEvaluationGram_correct hφ,
    FourKernel.gram_symm]

end MovingSofaQuantitative
