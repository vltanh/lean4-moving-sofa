module

public import MovingSofaQuantitative.KernelPieceModel

/-!
# A finite piece expansion of the actual evaluation vectors

Uncompiled proof source. The lists below represent continuum L2 kernels, not
sampled residuals. Admissibility is proved on the actual arc intervals. The
endpoint pi has an empty expansion, so no cosecant is integrated up to pi.
The last theorem identifies every Gram entry with a finite primitive sum.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

/-- The same five/four/two/one pieces as the integrated reconstruction. -/
def evaluationPieces (φ t : ℝ) : List KernelPiece :=
  let A := 1 / cos φ
  if t ≤ φ then
    [⟨0, t, φ, cos t, 0⟩,
     ⟨1, φ, π / 2 - φ, cos t * A, 0⟩,
     ⟨2, π / 2 - φ, π / 2, cos t * A, 0⟩,
     ⟨3, π / 2, π / 2 + φ, cos t * A * (A - sin φ), 0⟩,
     ⟨3, π / 2 + φ, π - φ, cos t * A ^ 2, cos t * A⟩]
  else if t ≤ π / 2 - φ then
    [⟨1, t, π / 2 - φ, 1, 0⟩,
     ⟨2, π / 2 - φ, π / 2, 1, 0⟩,
     ⟨3, π / 2, π / 2 + t, A - sin t, 0⟩,
     ⟨3, π / 2 + t, π - φ, A, 1⟩]
  else if t ≤ π / 2 then
    [⟨2, t, π / 2, sin (π - φ - t), 0⟩,
     ⟨3, π / 2, π - φ, (cos t / cos φ) * sin φ, 0⟩]
  else if t < π then [⟨3, π / 2, t, -sin t, 0⟩]
  else []

/-- This includes all branch endpoints; only the true last endpoint is omitted. -/
theorem evaluationPieces_admissible {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 π) {p : KernelPiece} (hp : p ∈ evaluationPieces φ t) :
    p.Admissible φ := by
  unfold evaluationPieces at hp
  dsimp only at hp
  split_ifs at hp with h1 h2 h3 h4
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num [KernelPiece.Admissible, residualStart, residualEnd]
      all_goals constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, pi_pos]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals
      norm_num [KernelPiece.Admissible, residualStart, residualEnd]
      all_goals constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, pi_pos]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    all_goals
      norm_num [KernelPiece.Admissible, residualStart, residualEnd]
      all_goals constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, pi_pos]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    norm_num [KernelPiece.Admissible, residualStart, residualEnd]
    constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, pi_pos]
  · simp only [List.not_mem_nil] at hp

/-- Attach actual admissibility proofs, rather than treating numeric endpoints
as if they were already subintervals of the integration domain. -/
def evaluationPieceKernel {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t : {t : ℝ // t ∈ Icc 0 π}) : FourKernel φ :=
  pieceModelKernel hφ ((evaluationPieces φ t).attach.map fun p =>
    ⟨p.1, evaluationPieces_admissible hφ t.2 p.2⟩)

/-- Multiplication of an indicator's weight is pointwise, including endpoints. -/
private theorem indicator_mul_weight (a b c : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    (Icc a b).indicator (fun x => c * f x) u = c * (Icc a b).indicator f u := by
  by_cases hu : u ∈ Icc a b <;> simp [hu]

/-- Equality of actual L2 vectors with the finite expansion. The scalar
identities here are precisely coefficient collection, not a norm estimate. -/
theorem evaluationPieceKernel_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t : {t : ℝ // t ∈ Icc 0 π}) :
    (evaluationPieceKernel hφ t).vector = (evaluationKernel hφ t).vector := by
  apply FourKernel.vector_eq_of_ae
  intro i
  apply Eventually.of_forall
  intro u
  unfold evaluationPieceKernel pieceModelKernel evaluationPieces evaluationKernel
  dsimp only
  split_ifs with h1 h2 h3 h4
  all_goals
    fin_cases i
    all_goals
      simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil,
        FourKernel.sum, FourKernel.add, FourKernel.zero, FourKernel.scale,
        KernelPiece.kernel, KernelPiece.weight, firstEvaluationKernel,
        middleEvaluationKernel, thirdEvaluationKernel, lastEvaluationKernel,
        kernelAtom, tailKernel]
      norm_num only [Fin.reduceEq, ↓reduceIte]
      simp only [Set.indicator_apply]
      split_ifs <;> ring

/-- The finite primitive sum, with empty overlap contributing exactly zero. -/
def evaluationPieceGram (φ t u : ℝ) : ℝ :=
  ((evaluationPieces φ t).map fun p =>
    ((evaluationPieces φ u).map fun q => p.cross φ q).sum).sum

/-- Every entry used by a finite certificate is the corresponding continuum
inner product. This does not yet certify any numerical bound. -/
theorem evaluationGram_eq_pieceSum {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t u : {t : ℝ // t ∈ Icc 0 π}) :
    (evaluationKernel hφ t).gram (evaluationKernel hφ u) =
      evaluationPieceGram φ t u := by
  rw [← FourKernel.inner_vectors, ← evaluationPieceKernel_vector hφ t,
    ← evaluationPieceKernel_vector hφ u, FourKernel.inner_vectors]
  unfold evaluationPieceKernel
  rw [pieceModel_gram]
  simp only [evaluationPieceGram, List.map_map, List.map_attach]

/-- Finite piece expansion at the last endpoint is exactly zero. -/
@[simp] theorem evaluationPieces_pi {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    evaluationPieces φ π = [] := by
  have h1 : ¬π ≤ φ := by linarith [hφ.2, pi_pos]
  have h2 : ¬π ≤ π / 2 - φ := by linarith [hφ.1, pi_pos]
  have h3 : ¬π ≤ π / 2 := by linarith [pi_pos]
  simp only [evaluationPieces, if_neg h1, if_neg h2, if_neg h3, lt_self_iff_false, if_false]

@[simp] theorem evaluationPieceGram_pi_left {φ u : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    evaluationPieceGram φ π u = 0 := by
  simp [evaluationPieceGram, evaluationPieces_pi hφ]

@[simp] theorem evaluationPieceGram_pi_right {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    evaluationPieceGram φ t π = 0 := by
  simp [evaluationPieceGram, evaluationPieces_pi hφ]

end MovingSofaQuantitative
