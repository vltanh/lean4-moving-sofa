module

public import MovingSofaQuantitative.ResidualAlgebra
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The continuum Hilbert space of four arc residuals

Uncompiled proof source. Each component uses the Lebesgue measure on its actual
arc. The finite product carries the L2, not the supremum, norm. Its squared
norm is proved equal to TWICE the integrated cap energy. No discretization or
sampled derivative enters this construction.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

def residualStart (φ : ℝ) : Fin 4 → ℝ := ![0, φ, π / 2 - φ, π / 2]
def residualEnd (φ : ℝ) : Fin 4 → ℝ := ![φ, π / 2 - φ, π / 2, π]

def residualComponent (φ : ℝ) (f df : ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![tangentResidual (π / 2) f df, cornerResidual f df,
    tangentResidual (π - φ) f df, tangentResidual π f df]

def residualMeasure (φ : ℝ) (i : Fin 4) : Measure ℝ :=
  volume.restrict (Ioo (residualStart φ i) (residualEnd φ i))

abbrev ResidualHilbert (φ : ℝ) := PiLp 2 (fun i : Fin 4 => Lp ℝ 2 (residualMeasure φ i))

theorem residualStart_le_end {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (i : Fin 4) :
    residualStart φ i ≤ residualEnd φ i := by
  fin_cases i <;> simp only [residualStart, residualEnd, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    linarith [hφ.1, hφ.2, pi_pos]

private theorem memLp_of_interval_squares {a b : ℝ} (hab : a ≤ b) {r : ℝ → ℝ}
    (hi : IntervalIntegrable r volume a b)
    (hs : IntervalIntegrable (fun u => r u ^ 2) volume a b) :
    MemLp r 2 (volume.restrict (Ioo a b)) := by
  have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hi
  have hs' := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hs
  exact (memLp_two_iff_integrable_sq hi'.aestronglyMeasurable).2 hs'

/-- Each actual residual defines an L2 class on precisely its own arc. -/
theorem residualComponent_memLp {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) (i : Fin 4) :
    MemLp (residualComponent φ f df i) 2 (residualMeasure φ i) := by
  fin_cases i
  · exact memLp_of_interval_squares hφ.1.le hf.first hf.first_sq
  · exact memLp_of_interval_squares (by linarith [hφ.2]) hf.middle hf.middle_sq
  · exact memLp_of_interval_squares (by linarith [hφ.1]) hf.third hf.third_sq
  · exact memLp_of_interval_squares (by linarith [pi_pos]) hf.last hf.last_sq

def residualVector {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) : ResidualHilbert φ :=
  WithLp.toLp 2 (fun i => (residualComponent_memLp hφ hf i).toLp (residualComponent φ f df i))

/-- The L2 inner product agrees with the actual integral of the chosen functions. -/
theorem inner_toLp_eq_integral {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ u, f u * g u ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with u hfu hgu
  simp [hfu, hgu, RCLike.inner_apply, mul_comm]

/-- This identifies the exact four-integral bilinear form with the Hilbert one. -/
theorem residualVector_inner {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df g dg : ℝ → ℝ} (hf : FourResidualData φ f df) (hg : FourResidualData φ g dg) :
    ⟪residualVector hφ hf, residualVector hφ hg⟫_ℝ = residualPair φ f df g dg := by
  rw [PiLp.inner_apply]
  simp only [residualVector, PiLp.toLp_apply, inner_toLp_eq_integral, Fin.sum_univ_four]
  unfold residualPair residualMeasure residualComponent residualStart residualEnd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [intervalIntegral.integral_of_le hφ.1.le,
    intervalIntegral.integral_of_le (by linarith [hφ.2] : φ ≤ π / 2 - φ),
    intervalIntegral.integral_of_le (by linarith [hφ.1] : π / 2 - φ ≤ π / 2),
    intervalIntegral.integral_of_le (by linarith [pi_pos] : π / 2 ≤ π)]
  simp only [integral_Ioc_eq_integral_Ioo]

/-- The factor of two is explicit and cannot be lost in a numerical adapter. -/
theorem residualVector_norm_sq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) :
    ‖residualVector hφ hf‖ ^ 2 = 2 * fourResidualEnergy φ f df := by
  rw [← real_inner_self_eq_norm_sq, residualVector_inner, residualPair_self]

/-- A square-integrable kernel on all four actual arc measures. -/
structure FourKernel (φ : ℝ) where
  value : Fin 4 → ℝ → ℝ
  memLp : ∀ i, MemLp (value i) 2 (residualMeasure φ i)

namespace FourKernel

variable {φ : ℝ}

def vector (k : FourKernel φ) : ResidualHilbert φ :=
  WithLp.toLp 2 (fun i => (k.memLp i).toLp (k.value i))

def pairing (k : FourKernel φ) (f df : ℝ → ℝ) : ℝ :=
  ∑ i : Fin 4, ∫ u, k.value i u * residualComponent φ f df i u ∂residualMeasure φ i

def gram (k l : FourKernel φ) : ℝ :=
  ∑ i : Fin 4, ∫ u, k.value i u * l.value i u ∂residualMeasure φ i

theorem inner_vector_residual (k : FourKernel φ) (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) :
    ⟪k.vector, residualVector hφ hf⟫_ℝ = k.pairing f df := by
  rw [PiLp.inner_apply]
  simp only [vector, residualVector, PiLp.toLp_apply, pairing, inner_toLp_eq_integral]

theorem inner_vectors (k l : FourKernel φ) : ⟪k.vector, l.vector⟫_ℝ = k.gram l := by
  rw [PiLp.inner_apply]
  simp only [vector, PiLp.toLp_apply, gram, inner_toLp_eq_integral]

theorem norm_vector_sq (k : FourKernel φ) : ‖k.vector‖ ^ 2 = k.gram k := by
  rw [← real_inner_self_eq_norm_sq, inner_vectors]

/-- Finite changes to kernel values do not alter the represented vector. -/
theorem vector_eq_of_ae {k l : FourKernel φ}
    (he : ∀ i, k.value i =ᵐ[residualMeasure φ i] l.value i) : k.vector = l.vector := by
  apply WithLp.ext
  funext i
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (k.memLp i), MemLp.coeFn_toLp (l.memLp i), he i]
    with u hku hlu heu
  exact hku.trans (heu.trans hlu.symm)

end FourKernel
end MovingSofaQuantitative
