module

public import MovingSofaQuantitative.KernelPrimitives

/-!
# A finite model of the actual kernel pieces

Uncompiled proof source. Piece endpoints and coefficients are real parameters.
The closed Gram formulas are justified by the previous integral identities;
this is not a discretization of the residual functions. Pieces ending at pi
are used only through separate endpoint/last-arc identities, avoiding a false
integrability claim for cosecant at pi.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

structure KernelPiece where
  component : Fin 4
  lo : ℝ
  hi : ℝ
  a : ℝ
  b : ℝ

namespace KernelPiece

/-- The coefficient b is used only for the last-arc cotangent term. -/
def weight (φ : ℝ) (p : KernelPiece) (u : ℝ) : ℝ :=
  if p.component = 0 then p.a / cos u
  else if p.component = 1 then p.a
  else if p.component = 2 then p.a / sin (π - φ - u)
  else p.a / sin u + p.b * (cos u / sin u)

/-- Geometric positions in the actual residual arc. -/
def Admissible (φ : ℝ) (p : KernelPiece) : Prop :=
  residualStart φ p.component ≤ p.lo ∧ p.lo ≤ p.hi ∧
  p.hi ≤ residualEnd φ p.component ∧ (p.component = 3 → p.hi < π)

theorem weight_continuous {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (p : KernelPiece) (hp : p.Admissible φ) : ContinuousOn (p.weight φ) (Icc p.lo p.hi) := by
  rcases p with ⟨j, a, b, A, B⟩
  fin_cases j
  · have hc : ∀ u ∈ Icc a b, cos u ≠ 0 := by
      intro u hu
      have hlo : 0 ≤ a := hp.1
      have hhi : b ≤ φ := hp.2.2.1
      exact (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, pi_pos],
        by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
    simpa only [weight, ↓reduceIte] using continuousOn_const.div continuous_cos.continuousOn hc
  · simpa only [weight, ↓reduceIte] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => A) (Icc a b))
  · have hs : ∀ u ∈ Icc a b, sin (π - φ - u) ≠ 0 := by
      intro u hu
      have hlo : π / 2 - φ ≤ a := hp.1
      have hhi : b ≤ π / 2 := hp.2.2.1
      exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
        (by linarith [hu.1, pi_pos])).ne'
    simpa only [weight, ↓reduceIte] using continuousOn_const.div (by fun_prop) hs
  · have hs : ∀ u ∈ Icc a b, sin u ≠ 0 := by
      intro u hu
      have hlo : π / 2 ≤ a := hp.1
      have hhi : b < π := hp.2.2.2 rfl
      exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hhi)).ne'
    simpa only [weight, ↓reduceIte] using
      (continuousOn_const.div continuous_sin.continuousOn hs).add
        (continuousOn_const.mul (continuous_cos.continuousOn.div continuous_sin.continuousOn hs))

def kernel {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (p : KernelPiece) (hp : p.Admissible φ) : FourKernel φ :=
  kernelAtom φ p.component p.lo p.hi (p.weight φ) (p.weight_continuous hφ hp)

/-- Closed primitive difference on a correctly ordered nonempty overlap. -/
def crossPrimitive (φ : ℝ) (p q : KernelPiece) (a b : ℝ) : ℝ :=
  if p.component = 0 then p.a * q.a * (tan b - tan a)
  else if p.component = 1 then p.a * q.a * (b - a)
  else if p.component = 2 then
    p.a * q.a * (cotangent (π - φ - b) - cotangent (π - φ - a))
  else
    p.a * q.a * (cotangent a - cotangent b) +
    (p.a * q.b + p.b * q.a) * (1 / sin a - 1 / sin b) +
    p.b * q.b * (cotangent a - cotangent b - (b - a))

def cross (φ : ℝ) (p q : KernelPiece) : ℝ :=
  if p.component = q.component then
    if max p.lo q.lo ≤ min p.hi q.hi then
      crossPrimitive φ p q (max p.lo q.lo) (min p.hi q.hi)
    else 0
  else 0

/-- Every scalar entry computed by the finite model is an actual Hilbert Gram entry. -/
theorem gram_eq_cross {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (p q : KernelPiece) (hp : p.Admissible φ) (hq : q.Admissible φ) :
    (p.kernel hφ hp).gram (q.kernel hφ hq) = p.cross φ q := by
  by_cases hj : p.component = q.component
  · have hraw := kernelAtom_gram_interval p.component p.lo p.hi q.lo q.hi
      hp.1 hp.2.2.1 (by simpa only [hj] using hq.1)
      (by simpa only [hj] using hq.2.2.1) (p.weight φ) (q.weight φ)
      (p.weight_continuous hφ hp) (q.weight_continuous hφ hq)
    change (kernelAtom φ p.component p.lo p.hi (p.weight φ) _).gram
      (kernelAtom φ q.component q.lo q.hi (q.weight φ) _) = _
    rw [← hj, hraw]
    simp only [cross, hj, ↓reduceIte]
    split_ifs with hab
    · have hsubP : Icc (max p.lo q.lo) (min p.hi q.hi) ⊆ Icc p.lo p.hi := by
        intro t ht
        exact ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
      have hsubQ : Icc (max p.lo q.lo) (min p.hi q.hi) ⊆ Icc q.lo q.hi := by
        intro t ht
        exact ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩
      have hcomponent : p.component = 0 ∨ p.component = 1 ∨ p.component = 2 ∨ p.component = 3 := by
        have hlt := p.component.isLt
        omega
      rcases hcomponent with h0 | h1 | h2 | h3
      · have hc : ∀ t ∈ Icc (max p.lo q.lo) (min p.hi q.hi), cos t ≠ 0 := by
          intro t ht
          have ht' := hsubP ht
          have hlo : 0 ≤ p.lo := by simpa only [h0, residualStart, Matrix.cons_val_zero] using hp.1
          have hhi : p.hi ≤ φ := by simpa only [h0, residualEnd, Matrix.cons_val_zero] using hp.2.2.1
          exact (cos_pos_of_mem_Ioo ⟨by linarith [ht'.1, pi_pos],
            by linarith [ht'.2, hφ.2, pi_pos]⟩).ne'
        simpa only [weight, crossPrimitive, h0, ← hj, ↓reduceIte] using
          first_kernel_cross_integral p.a q.a hab hc
      · simp only [weight, crossPrimitive, h1, ← hj, ↓reduceIte,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      · have hs : ∀ t ∈ Icc (max p.lo q.lo) (min p.hi q.hi), sin (π - φ - t) ≠ 0 := by
          intro t ht
          have ht' := hsubP ht
          have hlo : π / 2 - φ ≤ p.lo := by
            simpa only [h2, residualStart, Matrix.cons_val_two] using hp.1
          have hhi : p.hi ≤ π / 2 := by
            simpa only [h2, residualEnd, Matrix.cons_val_two] using hp.2.2.1
          exact (sin_pos_of_pos_of_lt_pi (by linarith [ht'.2, hφ.2, pi_pos])
            (by linarith [ht'.1, pi_pos])).ne'
        simpa only [weight, crossPrimitive, h2, ← hj, ↓reduceIte] using
          third_kernel_cross_integral p.a q.a (π - φ) hab hs
      · have hs : ∀ t ∈ Icc (max p.lo q.lo) (min p.hi q.hi), sin t ≠ 0 := by
          intro t ht
          have ht' := hsubP ht
          have hlo : π / 2 ≤ p.lo := by
            simpa only [h3, residualStart, Matrix.cons_val_three] using hp.1
          have hhi := hp.2.2.2 h3
          exact (sin_pos_of_pos_of_lt_pi (by linarith [ht'.1, pi_pos]) (ht'.2.trans_lt hhi)).ne'
        simpa only [weight, crossPrimitive, h3, ← hj, ↓reduceIte] using
          last_kernel_cross_integral p.a p.b q.a q.b hab hs
    · rfl
  · exact (kernelAtom_gram_ne hj _ _ _ _ _ _ _ _).trans (by simp only [cross, if_neg hj])

/-- Finite model coefficients multiply the represented L2 vector linearly. -/
def scale (a : ℝ) (p : KernelPiece) : KernelPiece :=
  { p with a := a * p.a, b := a * p.b }

theorem scale_admissible {φ : ℝ} {p : KernelPiece} (hp : p.Admissible φ) (a : ℝ) :
    (p.scale a).Admissible φ := hp

theorem scale_weight (φ a : ℝ) (p : KernelPiece) (t : ℝ) :
    (p.scale a).weight φ t = a * p.weight φ t := by
  unfold weight scale
  split_ifs <;> ring

theorem kernel_scale_vector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (p : KernelPiece) (hp : p.Admissible φ) (a : ℝ) :
    ((p.scale a).kernel hφ (scale_admissible hp a)).vector = a • (p.kernel hφ hp).vector := by
  rw [← FourKernel.vector_scale]
  apply FourKernel.vector_eq_of_ae
  intro i
  apply Filter.Eventually.of_forall
  intro t
  by_cases hij : i = p.component <;> by_cases ht : t ∈ Icc p.lo p.hi <;>
    simp [kernel, kernelAtom, FourKernel.scale, scale, weight, hij, ht] <;> ring

end KernelPiece

/-- A finite admissible piece model and its corresponding continuum kernel. -/
def pieceModelKernel {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ps : List {p : KernelPiece // p.Admissible φ}) : FourKernel φ :=
  FourKernel.sum (ps.map fun p => p.1.kernel hφ p.2)

theorem pieceModel_gram {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ps qs : List {p : KernelPiece // p.Admissible φ}) :
    (pieceModelKernel hφ ps).gram (pieceModelKernel hφ qs) =
      (ps.map fun p => (qs.map fun q => p.1.cross φ q.1).sum).sum := by
  simp only [pieceModelKernel, FourKernel.gram_sum_left, List.map_map,
    FourKernel.gram_sum_right]
  congr 1
  funext p
  congr 1
  funext q
  exact KernelPiece.gram_eq_cross hφ p.1 q.1 p.2 q.2

end MovingSofaQuantitative
