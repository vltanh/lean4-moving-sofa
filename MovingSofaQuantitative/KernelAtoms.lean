module

public import MovingSofaQuantitative.ResidualHilbert
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Compact arc pieces in the residual Hilbert space

Uncompiled proof source. A kernel piece is a continuous weight restricted to a
compact subarc of one actual residual measure. Endpoints are assigned by an
indicator; their values have no effect on the L2 vector or integral pairing.
These constructors carry square-integrability proofs, not numerical samples.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open scoped RealInnerProductSpace
open MovingSofaStability

namespace MovingSofaQuantitative

namespace FourKernel

variable {φ : ℝ}

def zero : FourKernel φ where
  value := fun _ _ => 0
  memLp := fun _ => MemLp.zero

def add (k l : FourKernel φ) : FourKernel φ where
  value := fun i t => k.value i t + l.value i t
  memLp := fun i => (k.memLp i).add (l.memLp i)

def scale (a : ℝ) (k : FourKernel φ) : FourKernel φ where
  value := fun i t => a * k.value i t
  memLp := fun i => (k.memLp i).const_mul a

@[simp] theorem pairing_zero (f df : ℝ → ℝ) : (zero : FourKernel φ).pairing f df = 0 := by
  simp [pairing, zero]

@[simp] theorem pairing_add (k l : FourKernel φ) (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df) :
    (k.add l).pairing f df = k.pairing f df + l.pairing f df := by
  unfold pairing add
  simp only [add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hr := residualComponent_memLp hφ hf i
  have hi1 := integrable_product_of_squares (k.memLp i).aestronglyMeasurable
    hr.aestronglyMeasurable
    ((memLp_two_iff_integrable_sq (k.memLp i).aestronglyMeasurable).1 (k.memLp i))
    ((memLp_two_iff_integrable_sq hr.aestronglyMeasurable).1 hr)
  have hi2 := integrable_product_of_squares (l.memLp i).aestronglyMeasurable
    hr.aestronglyMeasurable
    ((memLp_two_iff_integrable_sq (l.memLp i).aestronglyMeasurable).1 (l.memLp i))
    ((memLp_two_iff_integrable_sq hr.aestronglyMeasurable).1 hr)
  exact integral_add hi1 hi2

@[simp] theorem pairing_scale (a : ℝ) (k : FourKernel φ) (f df : ℝ → ℝ) :
    (k.scale a).pairing f df = a * k.pairing f df := by
  simp only [pairing, scale, mul_assoc, integral_const_mul, Finset.mul_sum]

@[simp] theorem vector_zero : (zero : FourKernel φ).vector = 0 := by
  apply WithLp.ext
  funext i
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (zero.memLp i)] with t ht
  simpa [zero] using ht

@[simp] theorem vector_add (k l : FourKernel φ) : (k.add l).vector = k.vector + l.vector := by
  apply WithLp.ext
  funext i
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp ((k.add l).memLp i),
    MemLp.coeFn_toLp (k.memLp i), MemLp.coeFn_toLp (l.memLp i),
    Lp.coeFn_add ((k.memLp i).toLp (k.value i)) ((l.memLp i).toLp (l.value i))]
      with t ht hk hl hadd
  simpa only [add, ht, hk, hl, hadd]

@[simp] theorem vector_scale (a : ℝ) (k : FourKernel φ) :
    (k.scale a).vector = a • k.vector := by
  apply WithLp.ext
  funext i
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp ((k.scale a).memLp i),
    MemLp.coeFn_toLp (k.memLp i), Lp.coeFn_smul a ((k.memLp i).toLp (k.value i))]
      with t ht hk hsmul
  simpa only [scale, ht, hk, hsmul, smul_eq_mul]

end FourKernel

/-- A compactly supported continuous weight is square integrable on the line. -/
theorem memLp_compact_indicator {a b : ℝ} {k : ℝ → ℝ}
    (hk : ContinuousOn k (Icc a b)) : MemLp ((Icc a b).indicator k) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).2
  have hi := hk.integrableOn_compact isCompact_Icc
  have hi2 := (hk.pow 2).integrableOn_compact isCompact_Icc
  exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2 hi2

/-- One atom belongs to one residual component; all other components vanish. -/
def kernelAtom (φ : ℝ) (j : Fin 4) (a b : ℝ) (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc a b)) : FourKernel φ where
  value := fun i t => if i = j then (Icc a b).indicator k t else 0
  memLp := fun i => by
    by_cases hi : i = j
    · subst i
      simpa only [if_true] using
        (memLp_compact_indicator hk).mono_measure (Measure.restrict_le_self)
    · simpa only [if_neg hi] using (MemLp.zero : MemLp (fun _ : ℝ => (0 : ℝ)) 2 _)

/-- The atom's integral pairs only with its own residual. The proof accounts
for the endpoint difference between compact and open integration intervals. -/
theorem kernelAtom_pairing {φ : ℝ} (j : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : residualStart φ j ≤ a) (hb : b ≤ residualEnd φ j)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc a b)) (f df : ℝ → ℝ) :
    (kernelAtom φ j a b k hk).pairing f df =
      ∫ t in a..b, k t * residualComponent φ f df j t := by
  unfold FourKernel.pairing kernelAtom
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
    have he : (fun t => (Icc a b).indicator k t * residualComponent φ f df j t) =
        (Icc a b).indicator (fun t => k t * residualComponent φ f df j t) := by
      funext t
      by_cases ht : t ∈ Icc a b <;> simp [ht]
    rw [he, integral_indicator measurableSet_Icc, residualMeasure,
      Measure.restrict_restrict measurableSet_Icc]
    have hset : Icc a b ∩ Ioo (residualStart φ j) (residualEnd φ j) =ᵐ[volume] Ioo a b := by
      filter_upwards [ae_neq a, ae_neq b] with t hta htb
      constructor
      · rintro ⟨ht, _⟩
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
      · intro ht
        exact ⟨⟨ht.1.le, ht.2.le⟩, ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩⟩
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_set hset
  · intro i _ hij
    simp [hij]
  · simp

/-- The same atom can be scaled without changing its support. -/
theorem kernelAtom_scale_value (φ : ℝ) (j : Fin 4) (a b c : ℝ)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc a b)) :
    (kernelAtom φ j a b (fun t => c * k t) (continuousOn_const.mul hk)).value =
      ((kernelAtom φ j a b k hk).scale c).value := by
  funext i t
  by_cases hi : i = j <;> by_cases ht : t ∈ Icc a b <;>
    simp [kernelAtom, FourKernel.scale, hi, ht]

end MovingSofaQuantitative
