module

public import MovingSofaQuantitative.KernelAtoms

/-!
# Concrete evaluation kernels on the four actual residual arcs

Uncompiled proof source. Every kernel is built from compactly supported
continuous pieces, each carrying its L2 proof. The original reconstruction
identifies its pairing with f(t). At pi the kernel is zero, not an improper
integral multiplied by zero. This is the continuum input to the rank-two bound.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

section Pieces

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))

private theorem secant_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ φ) :
    ContinuousOn (fun u => 1 / cos u) (Icc a b) :=
  continuousOn_const.div continuous_cos.continuousOn fun u hu =>
    (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, pi_pos],
      by linarith [hu.2, hφ.2, pi_pos]⟩).ne'

private theorem cosecant_continuous {a b : ℝ} (ha : π / 2 ≤ a) (hb : b < π) :
    ContinuousOn (fun u => 1 / sin u) (Icc a b) :=
  continuousOn_const.div continuous_sin.continuousOn fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hb)).ne'

private theorem third_continuous {a b : ℝ} (ha : π / 2 - φ ≤ a) (hb : b ≤ π / 2) :
    ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc a b) :=
  continuousOn_const.div (by fun_prop) fun u hu =>
    (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, pi_pos])).ne'

private theorem tail_continuous {a b : ℝ} (ha : π / 2 ≤ a) (hb : b < π) :
    ContinuousOn (tailKernel (1 / cos φ)) (Icc a b) :=
  (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn
    (fun u hu => (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hb)).ne')

/-- Kernel for t on the first arc. -/
def firstEvaluationKernel {t : ℝ} (ht : t ∈ Icc 0 φ) : FourKernel φ :=
  let a := 1 / cos φ
  let k₁ := kernelAtom φ 0 t φ (fun u => 1 / cos u) (secant_continuous hφ ht.1 le_rfl)
  let k₂ := kernelAtom φ 1 φ (π / 2 - φ) (fun _ => 1) continuousOn_const
  let k₃ := kernelAtom φ 2 (π / 2 - φ) (π / 2) (fun u => 1 / sin (π - φ - u))
    (third_continuous hφ le_rfl le_rfl)
  let k₄a := kernelAtom φ 3 (π / 2) (π / 2 + φ) (fun u => 1 / sin u)
    (cosecant_continuous le_rfl (by linarith [hφ.2, pi_pos]))
  let k₄b := kernelAtom φ 3 (π / 2 + φ) (π - φ) (tailKernel a)
    (tail_continuous (by linarith [hφ.1]) (by linarith [hφ.1]))
  (((k₁.scale (cos t)).add (k₂.scale (cos t * a))).add (k₃.scale (cos t * a))).add
    ((k₄a.scale (cos t * a * (a - sin φ))).add (k₄b.scale (cos t * a)))

/-- Kernel for t on the middle arc. The fourth residual is split at pi/2+t. -/
def middleEvaluationKernel {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) : FourKernel φ :=
  let a := 1 / cos φ
  let k₂ := kernelAtom φ 1 t (π / 2 - φ) (fun _ => 1) continuousOn_const
  let k₃ := kernelAtom φ 2 (π / 2 - φ) (π / 2) (fun u => 1 / sin (π - φ - u))
    (third_continuous hφ le_rfl le_rfl)
  let k₄a := kernelAtom φ 3 (π / 2) (π / 2 + t) (fun u => 1 / sin u)
    (cosecant_continuous le_rfl (by linarith [ht.2, hφ.1]))
  let k₄b := kernelAtom φ 3 (π / 2 + t) (π - φ) (tailKernel a)
    (tail_continuous (by linarith [ht.1, hφ.1]) (by linarith [hφ.1]))
  (k₂.add k₃).add ((k₄a.scale (a - sin t)).add k₄b)

/-- Kernel for t on the third arc, including its coupling to the last residual. -/
def thirdEvaluationKernel {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) : FourKernel φ :=
  let k₃ := kernelAtom φ 2 t (π / 2) (fun u => 1 / sin (π - φ - u))
    (third_continuous hφ ht.1 le_rfl)
  let k₄ := kernelAtom φ 3 (π / 2) (π - φ) (fun u => 1 / sin u)
    (cosecant_continuous le_rfl (by linarith [hφ.1]))
  (k₃.scale (sin (π - φ - t))).add (k₄.scale ((cos t / cos φ) * sin φ))

/-- Last-arc kernel; its upper endpoint is strictly below pi. -/
def lastEvaluationKernel {t : ℝ} (ht : t ∈ Ico (π / 2) π) : FourKernel φ :=
  (kernelAtom φ 3 (π / 2) t (fun u => 1 / sin u)
    (cosecant_continuous le_rfl ht.2)).scale (-sin t)

end Pieces

section Representation

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (hf : FourResidualData φ f df)

/-- The first kernel represents the first reconstruction formula evaluated via phi. -/
theorem firstEvaluationKernel_pairing {t : ℝ} (ht : t ∈ Icc 0 φ) :
    (firstEvaluationKernel hφ ht).pairing f df = f t := by
  unfold firstEvaluationKernel
  simp only [FourKernel.pairing_add _ _ hφ hf, FourKernel.pairing_scale]
  rw [kernelAtom_pairing 0 ht.2 ht.1 le_rfl,
    kernelAtom_pairing 1 (by linarith [hφ.2]) le_rfl le_rfl,
    kernelAtom_pairing 2 (by linarith [hφ.1]) le_rfl le_rfl,
    kernelAtom_pairing 3 (by linarith [hφ.1]) le_rfl (by linarith [hφ.2, pi_pos]),
    kernelAtom_pairing 3 (by linarith [hφ.2]) (by linarith [hφ.1]) (by linarith [hφ.1])]
  simp only [residualComponent, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, one_mul]
  have h1 := sharp_first_formula hφ hf ht
  have h2 := sharp_middle_formula hφ hf (t := φ) ⟨le_rfl, by linarith [hφ.2]⟩
  rw [h2] at h1
  linear_combination -h1

/-- The disjoint last-arc pieces are combined before applying any norm bound. -/
theorem middleEvaluationKernel_pairing {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    (middleEvaluationKernel hφ ht).pairing f df = f t := by
  unfold middleEvaluationKernel
  simp only [FourKernel.pairing_add _ _ hφ hf, FourKernel.pairing_scale]
  rw [kernelAtom_pairing 1 ht.2 ht.1 le_rfl,
    kernelAtom_pairing 2 (by linarith [hφ.1]) le_rfl le_rfl,
    kernelAtom_pairing 3 (by linarith [ht.1, hφ.1]) le_rfl (by linarith [ht.2, hφ.1]),
    kernelAtom_pairing 3 (by linarith [ht.2]) (by linarith [ht.1, hφ.1]) (by linarith [hφ.1])]
  simp only [residualComponent, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, one_mul]
  have h := sharp_middle_formula hφ hf ht
  linear_combination -h

/-- Third-arc representation after substituting the exact last-arc endpoint. -/
theorem thirdEvaluationKernel_pairing {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    (thirdEvaluationKernel hφ ht).pairing f df = f t := by
  unfold thirdEvaluationKernel
  simp only [FourKernel.pairing_add _ _ hφ hf, FourKernel.pairing_scale]
  rw [kernelAtom_pairing 2 ht.2 ht.1 le_rfl,
    kernelAtom_pairing 3 (by linarith [hφ.2, pi_pos]) le_rfl (by linarith [hφ.1])]
  simp only [residualComponent, Matrix.cons_val_two, Matrix.cons_val_three]
  have h3 := sharp_third_formula hφ hf ht
  have h4 := sharp_last_formula hf (t := π - φ)
    ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩
  rw [sin_pi_sub] at h4
  rw [h4] at h3
  linear_combination -h3

/-- Last-arc representation never integrates across the singular endpoint. -/
theorem lastEvaluationKernel_pairing {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    (lastEvaluationKernel (φ := φ) ht).pairing f df = f t := by
  unfold lastEvaluationKernel
  rw [FourKernel.pairing_scale, kernelAtom_pairing 3 ht.1 le_rfl ht.2.le]
  simp only [residualComponent, Matrix.cons_val_three]
  exact (sharp_last_formula hf ht).symm

end Representation

/-- The concrete evaluation kernel, including the zero endpoint. -/
def evaluationKernel {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (t : {t : ℝ // t ∈ Icc 0 π}) : FourKernel φ :=
  if h1 : t.1 ≤ φ then firstEvaluationKernel hφ ⟨t.2.1, h1⟩
  else if h2 : t.1 ≤ π / 2 - φ then middleEvaluationKernel hφ ⟨(not_le.mp h1).le, h2⟩
  else if h3 : t.1 ≤ π / 2 then thirdEvaluationKernel hφ ⟨(not_le.mp h2).le, h3⟩
  else if h4 : t.1 < π then lastEvaluationKernel ⟨(not_le.mp h3).le, h4⟩
  else FourKernel.zero

/-- Every upper-half support evaluation is represented by this actual L2 vector. -/
theorem evaluationKernel_pairing {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df)
    (t : {t : ℝ // t ∈ Icc 0 π}) : (evaluationKernel hφ t).pairing f df = f t := by
  unfold evaluationKernel
  split_ifs with h1 h2 h3 h4
  · exact firstEvaluationKernel_pairing hφ hf ⟨t.2.1, h1⟩
  · exact middleEvaluationKernel_pairing hφ hf ⟨(not_le.mp h1).le, h2⟩
  · exact thirdEvaluationKernel_pairing hφ hf ⟨(not_le.mp h2).le, h3⟩
  · exact lastEvaluationKernel_pairing hf ⟨(not_le.mp h3).le, h4⟩
  · have ht : t.1 = π := le_antisymm t.2.2 (not_lt.mp h4)
    rw [FourKernel.pairing_zero, ht, hf.left_zero]

theorem evaluationKernel_inner {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df)
    (t : {t : ℝ // t ∈ Icc 0 π}) :
    ⟪(evaluationKernel hφ t).vector, residualVector hφ hf⟫_ℝ = f t := by
  rw [FourKernel.inner_vector_residual, evaluationKernel_pairing]

end MovingSofaQuantitative
