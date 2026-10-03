module

public import Mathlib

/-!
# Finite centered support penalties

The selector may be sampled on the polygon's defining normals. An outward
floating-height perturbation then changes just one normal's sample values.
A hierarchy of persistent samples can identify the target without a Riemann
sum argument. The only global error required is the sum of the positive
variation defects; it is controlled by the total sample weight.

This module is scalar algebra. The application to actual support values and
feasible polygons is separate. All estimates keep nonnegativity of the weights
and finiteness of the sampling set explicit. Uncompiled, admission-free source.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace SofaUniqueness

variable {ι α : Type*}

/-- A finite squared-distance penalty centered at the target samples. -/
def sampledPenalty (s : Finset ι) (w target f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (f i - target i) ^ 2

theorem sampledPenalty_nonneg (s : Finset ι) (w target f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ sampledPenalty s w target f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

/-- Every positively weighted sample is controlled by the full penalty. -/
theorem sample_sq_le_penalty (s : Finset ι) (w target f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {i : ι} (hi : i ∈ s) :
    w i * (f i - target i) ^ 2 ≤ sampledPenalty s w target f := by
  exact Finset.single_le_sum (f := fun j => w j * (f j - target j) ^ 2)
    (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _)) hi

/-- A uniform error in the sampled supports bounds the recovery penalty. -/
theorem sampledPenalty_le (s : Finset ι) (w target f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {η : ℝ}
    (hclose : ∀ i ∈ s, |f i - target i| ≤ η) :
    sampledPenalty s w target f ≤ (∑ i ∈ s, w i) * η ^ 2 := by
  rw [sampledPenalty, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  have h := abs_le.mp (hclose i hi)
  nlinarith

/-- Scalar square-increment estimate. It applies to positive and negative
changes of the actual support, as needed after pinned-strip normalization. -/
theorem abs_square_increment_le {a b c η r : ℝ}
    (hη : 0 ≤ η) (ha : |a - c| ≤ η) (hab : |b - a| ≤ r) :
    |(b - c) ^ 2 - (a - c) ^ 2| ≤ 2 * η * r + r ^ 2 := by
  have hid : (b - c) ^ 2 - (a - c) ^ 2 = 2 * (a - c) * (b - a) + (b - a) ^ 2 := by ring
  rw [hid]
  calc
    |2 * (a - c) * (b - a) + (b - a) ^ 2|
        ≤ |2 * (a - c) * (b - a)| + |(b - a) ^ 2| := abs_add_le _ _
    _ = 2 * |a - c| * |b - a| + (b - a) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (b - a))]
    _ ≤ 2 * η * r + r ^ 2 := by
      have hp := mul_le_mul ha hab (abs_nonneg _) hη
      have hsq : (b - a) ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs (b - a)]
        exact pow_le_pow_left₀ (abs_nonneg _) hab 2
      nlinarith

/-- Uniform changes of the sampled actual supports control the whole penalty.
The estimate has an explicit quadratic remainder. -/
theorem sampledPenalty_change_bound (s : Finset ι) (w target f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {η r : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ i ∈ s, |f i - target i| ≤ η)
    (hchange : ∀ i ∈ s, |g i - f i| ≤ r) :
    |sampledPenalty s w target g - sampledPenalty s w target f| ≤
      (∑ i ∈ s, w i) * (2 * η * r + r ^ 2) := by
  have hu : ∀ i ∈ s,
      w i * (g i - target i) ^ 2 - w i * (f i - target i) ^ 2 ≤
        w i * (2 * η * r + r ^ 2) := by
    intro i hi
    have h := (abs_le.mp (abs_square_increment_le hη (hclose i hi) (hchange i hi))).2
    have hm := mul_le_mul_of_nonneg_left h (hw i hi)
    nlinarith
  have hl : ∀ i ∈ s,
      -(w i * (2 * η * r + r ^ 2)) ≤
        w i * (g i - target i) ^ 2 - w i * (f i - target i) ^ 2 := by
    intro i hi
    have h := (abs_le.mp (abs_square_increment_le hη (hclose i hi) (hchange i hi))).1
    have hm := mul_le_mul_of_nonneg_left h (hw i hi)
    nlinarith
  have hsumU := Finset.sum_le_sum hu
  have hsumL := Finset.sum_le_sum hl
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul] at hsumU hsumL
  exact abs_le.mpr ⟨hsumL, hsumU⟩

/-- The exact sample weight associated with a defining normal. Several samples
from different levels may have the same normal; all of their weights count. -/
def normalWeight (s : Finset ι) (normal : ι → α) (w : ι → ℝ) (t : α) : ℝ := by
  classical
  exact ∑ i ∈ s.filter (fun i => normal i = t), w i

theorem normalWeight_nonneg (s : Finset ι) (normal : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (t : α) : 0 ≤ normalWeight s normal w t := by
  classical
  exact Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1

/-- If just one defining normal changes, only its total sample weight enters
the penalty variation. No claim about unsampled supporting directions is needed. -/
theorem sampledPenalty_change_on_normal (s : Finset ι) (normal : ι → α)
    (w target f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (t : α)
    {η r : ℝ} (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hclose : ∀ i ∈ s, |f i - target i| ≤ η)
    (hsame : ∀ i ∈ s, normal i ≠ t → g i = f i)
    (hchange : ∀ i ∈ s, normal i = t → |g i - f i| ≤ r) :
    |sampledPenalty s w target g - sampledPenalty s w target f| ≤
      normalWeight s normal w t * (2 * η * r + r ^ 2) := by
  classical
  let F := s.filter (fun i => normal i = t)
  have heq : sampledPenalty s w target g - sampledPenalty s w target f =
      sampledPenalty F w target g - sampledPenalty F w target f := by
    unfold sampledPenalty
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hn
    have hne : normal i ≠ t := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨hi, h⟩)
    rw [hsame i hi hne, sub_self]
  rw [heq]
  exact sampledPenalty_change_bound F w target f g
    (fun i hi => hw i (Finset.mem_filter.mp hi).1) hη
    (fun i hi => hclose i (Finset.mem_filter.mp hi).1)
    (fun i hi => hchange i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)

/-- Summing over the defining normals counts every sample exactly once.
This is the reason a mesh-independent total error bound suffices. -/
theorem sum_normalWeight (s : Finset ι) (D : Finset α)
    (normal : ι → α) (w : ι → ℝ) (hmap : ∀ i ∈ s, normal i ∈ D) :
    (∑ t ∈ D, normalWeight s normal w t) = ∑ i ∈ s, w i := by
  classical
  unfold normalWeight
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (normal i)]
  · simp
  · intro t ht hne
    simp [Ne.symm hne]
  · intro hn
    exact (hn (hmap i hi)).elim

/-- Finite sample penalties are continuous in their actual sample values. -/
theorem continuous_sampledPenalty (s : Finset ι) (w target : ι → ℝ) :
    Continuous (sampledPenalty s w target) := by
  unfold sampledPenalty
  fun_prop

/-- Vanishing penalty controls each sample with a fixed positive weight. -/
theorem sample_eq_of_penalty_tendsto {s : Finset ι} {w target : ι → ℝ}
    (f : ℕ → ι → ℝ) (limit : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hlim : ∀ i ∈ s, Tendsto (fun n => f n i) atTop (𝓝 (limit i)))
    (hP : Tendsto (fun n => sampledPenalty s w target (f n)) atTop (𝓝 0))
    {i : ι} (hi : i ∈ s) (hwi : 0 < w i) : limit i = target i := by
  have hl : Tendsto (fun n => w i * (f n i - target i) ^ 2) atTop
      (𝓝 (w i * (limit i - target i) ^ 2)) :=
    ((hlim i hi).sub_const (target i)).pow 2 |>.const_mul (w i)
  have hle : w i * (limit i - target i) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' hl hP fun n => sample_sq_le_penalty s w target (f n) hw hi
  have hsq : (limit i - target i) ^ 2 = 0 := by nlinarith [sq_nonneg (limit i - target i)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end SofaUniqueness
