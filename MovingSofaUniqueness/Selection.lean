module

public import Mathlib
public import MovingSofaOptimality.Balanced.MaximumPolygonCap
public import MovingSofaOptimality.Balanced.BalancedMaximumSofa
public import MovingSofaOptimality.Injectivity.LimitIneq

/-!
# Proposition 1: polygon caps converging to a given maximizing cap

Let `K` be a cap that maximizes the sofa area `A_ω`. At stage `n`, maximize `A_ω` over the polygon
caps with the `n`-th dyadic normals, minus a squared penalty on the differences between their
support function and `K`'s at dyadic sample normals of total weight at most one. The polygon
circumscribed about `K` has penalty zero, and two orthogonal samples keep the maximizers in a
bounded box, so the maximizers exist (`exists_penalizedMax`) and a subsequence converges to `K`
(`exists_selectedCapSequence`). This is Proposition 1 of `docs/uniqueness/20-complete-paper-proof.md`,
with a fixed penalty on persistent samples in place of the note's vanishing penalty.
-/

@[expose] public section
noncomputable section

/-!
## Finite centered support penalties

The selector may be sampled on the polygon's defining normals. An outward
floating-height perturbation then changes just one normal's sample values.
A hierarchy of persistent samples can identify the target without a Riemann
sum argument. The only global error required is the sum of the positive
variation defects; it is controlled by the total sample weight.

This module is scalar algebra. The application to actual support values and
feasible polygons is separate. All estimates keep nonnegativity of the weights
and finiteness of the sampling set explicit.
-/

section

open Set Filter Topology
open scoped BigOperators

namespace MovingSofaUniqueness

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
    {η r : ℝ} (hη : 0 ≤ η)
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

end MovingSofaUniqueness

end

/-!
## Finite penalties on the actual defining supports

The data below include only finitely many upper defining normals, with
nonnegative weights. Repeated normals are allowed. A circumscribed recovery
polygon has exactly the target's values at all these normals, so its penalty
is ZERO, rather than merely tending to zero.

The use of actual support values is essential. Assigned heights are used only
for a comparison whose direction is justified separately in `PolygonPenalty`.
-/

section

open Set Real Filter Topology MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- A finite, possibly repeated, sampling of the polygon's defining normals. -/
structure SupportSamples (Θ : AngleSet) where
  Index : Type
  finiteIndex : Fintype Index
  normal : Index → ℝ
  weight : Index → ℝ
  normal_mem : ∀ i, normal i ∈ Θ.diamond
  weight_nonneg : ∀ i, 0 ≤ weight i

attribute [instance] SupportSamples.finiteIndex

namespace SupportSamples

variable {Θ : AngleSet} (S : SupportSamples Θ)

def totalWeight : ℝ := ∑ i, S.weight i

def penalty (target K : Set (ℝ × ℝ)) : ℝ :=
  sampledPenalty Finset.univ S.weight (fun i => supp target (S.normal i))
    (fun i => supp K (S.normal i))

def atNormal (t : ℝ) : ℝ :=
  normalWeight Finset.univ S.normal S.weight t

theorem totalWeight_nonneg : 0 ≤ S.totalWeight :=
  Finset.sum_nonneg fun i _ => S.weight_nonneg i

theorem penalty_nonneg (target K : Set (ℝ × ℝ)) : 0 ≤ S.penalty target K :=
  sampledPenalty_nonneg _ _ _ _ (fun i _ => S.weight_nonneg i)

theorem atNormal_nonneg (t : ℝ) : 0 ≤ S.atNormal t :=
  normalWeight_nonneg _ _ _ (fun i _ => S.weight_nonneg i) t

theorem sum_atNormal : (∑ t ∈ mpcDiamond Θ, S.atNormal t) = S.totalWeight := by
  exact sum_normalWeight Finset.univ (mpcDiamond Θ) S.normal S.weight
    (fun i _ => mpc_mem_mpcDiamond.mpr (S.normal_mem i))

/-- One positively weighted support sample is bounded by the whole penalty. -/
theorem sample_bound (target K : Set (ℝ × ℝ)) (i : S.Index) :
    S.weight i * (supp K (S.normal i) - supp target (S.normal i)) ^ 2 ≤
      S.penalty target K :=
  sample_sq_le_penalty Finset.univ S.weight (fun i => supp target (S.normal i))
    (fun i => supp K (S.normal i)) (fun i _ => S.weight_nonneg i) (Finset.mem_univ i)

/-- The recovery penalty vanishes identically, at every finite mesh. -/
theorem penalty_recovery_zero {target : Set (ℝ × ℝ)} (hK : IsCap target Θ.ω) :
    S.penalty target (polyCap Θ target) = 0 := by
  unfold penalty sampledPenalty
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [nef_supp_polyCap hK (nef_diamond_subset_capAngles Θ (S.normal_mem i)), sub_self]
  simp

/-- Therefore the recovery objective already has the full continuum value. -/
theorem recovery_objective_ge {target : Set (ℝ × ℝ)} (hK : IsCap target Θ.ω) :
    sofaArea Θ.ω target ≤
      polyArea Θ (polyCap Θ target) - S.penalty target (polyCap Θ target) := by
  rw [S.penalty_recovery_zero hK, sub_zero]
  have h := theorem3_2_3_le (Θ := Θ) hK
  have heq : polyArea Θ (polyCap Θ target) = polyArea Θ target := by
    unfold polyArea
    rw [proposition3_2_1_fix (proposition3_2_1 hK).2,
      ← (proposition3_2_2 hK).1]
  rw [heq]
  exact h

/-- Continuity uses only finitely many actual support values. -/
theorem penalty_tendsto {Ks : ℕ → Set (ℝ × ℝ)} {K target : Set (ℝ × ℝ)}
    (hlim : ∀ i, Tendsto (fun n => supp (Ks n) (S.normal i)) atTop
      (𝓝 (supp K (S.normal i)))) :
    Tendsto (fun n => S.penalty target (Ks n)) atTop (𝓝 (S.penalty target K)) := by
  have hv : Tendsto (fun n i => supp (Ks n) (S.normal i)) atTop
      (𝓝 (fun i => supp K (S.normal i))) := tendsto_pi_nhds.mpr hlim
  exact (continuous_sampledPenalty Finset.univ S.weight
    (fun i => supp target (S.normal i))).continuousAt.tendsto.comp hv

/-- A floating perturbation affects only the sample weight at its own normal. -/
theorem penalty_change_one {target K K' : Set (ℝ × ℝ)} {t η ε : ℝ}
    (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    (hsame : ∀ i, S.normal i ≠ t → supp K' (S.normal i) = supp K (S.normal i))
    (hchange : ∀ i, S.normal i = t → |supp K' (S.normal i) - supp K (S.normal i)| ≤ ε) :
    |S.penalty target K' - S.penalty target K| ≤
      S.atNormal t * (2 * η * ε + ε ^ 2) := by
  exact sampledPenalty_change_on_normal Finset.univ S.normal S.weight
    (fun i => supp target (S.normal i)) (fun i => supp K (S.normal i))
    (fun i => supp K' (S.normal i)) (fun i _ => S.weight_nonneg i) t hη
    (fun i _ => hclose i) (fun i _ => hsame i) (fun i _ => hchange i)

/-- Uniform actual-support changes, including normalization after a pinned
move, have a penalty bound controlled by the total sample weight. -/
theorem penalty_change_uniform {target K K' : Set (ℝ × ℝ)} {η r : ℝ}
    (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    (hchange : ∀ i, |supp K' (S.normal i) - supp K (S.normal i)| ≤ r) :
    |S.penalty target K' - S.penalty target K| ≤
      S.totalWeight * (2 * η * r + r ^ 2) := by
  exact sampledPenalty_change_bound Finset.univ S.weight
    (fun i => supp target (S.normal i)) (fun i => supp K (S.normal i))
    (fun i => supp K' (S.normal i)) (fun i _ => S.weight_nonneg i) hη
    (fun i _ => hclose i) (fun i _ => hchange i)

end SupportSamples

end MovingSofaUniqueness

end

/-!
## A persistent sampled selector

Level m receives total weight 2^(-(m+1)), divided equally among its first- and
second-quadrant defining normals. At stage n all levels m<=n are retained.
Consequently the total weight is at most one and every fixed dyadic normal
keeps a strictly positive weight at all later stages.

The recovery polygon has zero penalty at EVERY stage. The coarsest level
contains a pair of orthogonal directions and controls horizontal escape of a
positive-objective maximizing sequence. No added box constraints or vanishing
penalty coefficients are required.

Only the total stationarity error is required to vanish; a uniform per-facet
O(delta) bound is not asserted for persistent coarse samples.
-/

section

open Set Real Filter Topology MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

variable (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2))

/-- The coefficient of one of the two copies of a level-m angle. -/
def dyadicLevelWeight (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 1) /
    (2 * ((dyadicAngleSet ω hω m).angles.card : ℝ))

theorem dyadicLevelWeight_pos (m : ℕ) : 0 < dyadicLevelWeight ω hω m := by
  have hcard : 0 < ((dyadicAngleSet ω hω m).angles.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (dyadicAngleSet ω hω m).nonempty
  unfold dyadicLevelWeight
  positivity

/-- Repeated coarse normals are intentionally retained as distinct samples. -/
abbrev DyadicSampleIndex (n : ℕ) : Type :=
  Σ m : Fin (n + 1), ↥(dyadicAngleSet ω hω m.1).angles × Fin 2

/-- The actual finite sample data for the stage-n polygon. -/
def dyadicSamples (n : ℕ) : SupportSamples (dyadicAngleSet ω hω n) where
  Index := DyadicSampleIndex ω hω n
  finiteIndex := by classical infer_instance
  normal i := i.2.1.1 + (i.2.2 : ℝ) * (π / 2)
  weight i := dyadicLevelWeight ω hω i.1.1
  normal_mem := by
    rintro ⟨m, t, b⟩
    have hm : m.1 ≤ n := Nat.le_of_lt_succ m.2
    have ht : t.1 ∈ (dyadicAngleSet ω hω n).angles :=
      mpc_dyadic_mono hω hm t.2
    fin_cases b
    · simpa using
        (show t.1 ∈ (dyadicAngleSet ω hω n).diamond from Or.inl (Or.inl ht))
    · simpa using
        (show t.1 + π / 2 ∈ (dyadicAngleSet ω hω n).diamond from
          Or.inl (Or.inr ⟨t.1, ht, rfl⟩))
  weight_nonneg i := (dyadicLevelWeight_pos ω hω i.1.1).le

/-- The finite mass of a single level, independent of its number of normals. -/
theorem dyadic_level_mass (m : ℕ) :
    (∑ _i : ↥(dyadicAngleSet ω hω m).angles × Fin 2,
      dyadicLevelWeight ω hω m) = (1 / 2 : ℝ) ^ (m + 1) := by
  classical
  have hcard : ((dyadicAngleSet ω hω m).angles.card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Finset.card_pos.mpr (dyadicAngleSet ω hω m).nonempty)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fin, nsmul_eq_mul]
  unfold dyadicLevelWeight
  push_cast
  field_simp

/-- Exact finite geometric mass. -/
theorem dyadic_totalWeight (n : ℕ) :
    (dyadicSamples ω hω n).totalWeight = 1 - (1 / 2 : ℝ) ^ (n + 1) := by
  classical
  have hlevels : (dyadicSamples ω hω n).totalWeight =
      ∑ m : Fin (n + 1), (1 / 2 : ℝ) ^ (m.1 + 1) := by
    change (∑ i : DyadicSampleIndex ω hω n, dyadicLevelWeight ω hω i.1.1) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro m _
    exact dyadic_level_mass ω hω m.1
  have hgeom : ∀ r : ℕ,
      (∑ m ∈ Finset.range r, (1 / 2 : ℝ) ^ (m + 1)) = 1 - (1 / 2 : ℝ) ^ r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [hlevels, Fin.sum_univ_eq_sum_range (fun m => (1 / 2 : ℝ) ^ (m + 1)) (n + 1)]
  exact hgeom (n + 1)

theorem dyadic_totalWeight_le_one (n : ℕ) : (dyadicSamples ω hω n).totalWeight ≤ 1 := by
  rw [dyadic_totalWeight]
  have h : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  linarith

/-- The stage-n penalty used in the actual polygon optimization. -/
def dyadicPenalty (n : ℕ) (target K : Set (ℝ × ℝ)) : ℝ :=
  (dyadicSamples ω hω n).penalty target K

theorem dyadicPenalty_nonneg (n : ℕ) (target K : Set (ℝ × ℝ)) :
    0 ≤ dyadicPenalty ω hω n target K :=
  (dyadicSamples ω hω n).penalty_nonneg target K

/-- A first-quadrant dyadic sample retains its fixed level weight. -/
theorem persistent_sample_first {m n : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ (dyadicAngleSet ω hω m).angles) (target K : Set (ℝ × ℝ)) :
    dyadicLevelWeight ω hω m * (supp K t - supp target t) ^ 2 ≤
      dyadicPenalty ω hω n target K := by
  let i : DyadicSampleIndex ω hω n := ⟨⟨m, by omega⟩, ⟨⟨t, ht⟩, 0⟩⟩
  have h := (dyadicSamples ω hω n).sample_bound target K i
  have hn : (dyadicSamples ω hω n).normal i = t := by
    simp only [dyadicSamples, i, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
  rw [hn] at h
  exact h

/-- The shifted dyadic sample has the same persistent weight. -/
theorem persistent_sample_second {m n : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ (dyadicAngleSet ω hω m).angles) (target K : Set (ℝ × ℝ)) :
    dyadicLevelWeight ω hω m * (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤
      dyadicPenalty ω hω n target K := by
  let i : DyadicSampleIndex ω hω n := ⟨⟨m, by omega⟩, ⟨⟨t, ht⟩, 1⟩⟩
  have h := (dyadicSamples ω hω n).sample_bound target K i
  have hn : (dyadicSamples ω hω n).normal i = t + π / 2 := by
    simp only [dyadicSamples, i, Fin.val_one, Nat.cast_one, one_mul]
  rw [hn] at h
  exact h

theorem dyadic_recovery_ge {target : Set (ℝ × ℝ)} (hK : IsCap target ω) (n : ℕ) :
    sofaArea ω target ≤ polyArea (dyadicAngleSet ω hω n)
      (polyCap (dyadicAngleSet ω hω n) target) -
        dyadicPenalty ω hω n target (polyCap (dyadicAngleSet ω hω n) target) :=
  (dyadicSamples ω hω n).recovery_objective_ge hK

end MovingSofaUniqueness

end

/-!
## Existence of actual penalized polygon maximizers

We maximize the polygon objective minus a finite sampled support penalty over
ALL standard polygon caps of the fixed angle set. Two positively weighted
orthogonal samples prevent translations from escaping. Positive objective
prevents the width from escaping, by the paper's general polygon-width lemma.

The compactness argument is the finite-support-value argument used for
Theorem 3.4.3, with the continuous finite penalty retained. It does not assume
that the selected polygons are balanced, and it imposes no artificial box
constraint whose later variations would have to be justified.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- A common position bound from two controlled orthogonal support samples. -/
def sampleBoxRadius (target : Set (ℝ × ℝ)) (t c q : ℝ) : ℝ :=
  let H := |supp target t| + |supp target (t + π / 2)| + c / q + 1
  H / sin t + H / cos t

theorem sampleBoxRadius_nonneg (target : Set (ℝ × ℝ)) {t c q : ℝ}
    (ht0 : 0 < t) (htL : t < π / 2) (hc : 0 ≤ c) (hq : 0 < q) :
    0 ≤ sampleBoxRadius target t c q := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], htL⟩
  unfold sampleBoxRadius
  positivity

/-- Two sample bounds give a compact bounding rectangle for the actual cap. -/
theorem polygon_subset_sampleBox {Θ : AngleSet} {K target : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t c q : ℝ} (ht : t ∈ Θ.angles)
    (hc : 0 ≤ c) (hq : 0 < q)
    (hfirst : q * (supp K t - supp target t) ^ 2 ≤ c)
    (hsecond : q * (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ c) :
    K ⊆ Icc (-sampleBoxRadius target t c q) (sampleBoxRadius target t c q) ×ˢ Icc 0 1 := by
  have htI := mpc_angles_bounds ht
  have htL : t < π / 2 := htI.2.trans_le (mpc_omega_le Θ)
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi htI.1 (by linarith [pi_pos])
  have hcos : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htI.1, pi_pos], htL⟩
  have hqdiv : 0 ≤ c / q := div_nonneg hc hq.le
  have hsq₀ : (supp K t - supp target t) ^ 2 ≤ c / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm] using hfirst
  have hsq₁ : (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ c / q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm] using hsecond
  have habs (x : ℝ) (hx : x ^ 2 ≤ c / q) : |x| ≤ c / q + 1 := by
    have h₀ := abs_nonneg x
    have h₁ : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 1)]
  have ha₀ := habs _ hsq₀
  have ha₁ := habs _ hsq₁
  let H := |supp target t| + |supp target (t + π / 2)| + c / q + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hb₀ : supp K t ≤ H := by
    have h := (abs_le.mp ha₀).2
    have htarget := le_abs_self (supp target t)
    dsimp [H]
    linarith [abs_nonneg (supp target (t + π / 2))]
  have hb₁ : supp K (t + π / 2) ≤ H := by
    have h := (abs_le.mp ha₁).2
    have htarget := le_abs_self (supp target (t + π / 2))
    dsimp [H]
    linarith [abs_nonneg (supp target t)]
  intro p hp
  have hy₀ : 0 ≤ p.2 := (mpc_cap_nonneg hK.1 hp).1
  have hy₁ : p.2 ≤ 1 := (mpc_cap_le_one hK.1 hp).2
  have h₀ := (dot_le_supp hK.1.2.1.2.1 hp t).trans hb₀
  have h₁ := (dot_le_supp hK.1.2.1.2.1 hp (t + π / 2)).trans hb₁
  rw [uvec_add_pi_div_two] at h₁
  simp only [dot, uvec, vvec] at h₀ h₁
  have hx₀ : p.1 ≤ H / cos t := by
    apply (le_div_iff₀ hcos).mpr
    nlinarith
  have hx₁ : -p.1 ≤ H / sin t := by
    apply (le_div_iff₀ hs).mpr
    nlinarith
  have hdiv₀ : 0 ≤ H / cos t := div_nonneg hH hcos.le
  have hdiv₁ : 0 ≤ H / sin t := div_nonneg hH hs.le
  change p ∈ Icc (-(H / sin t + H / cos t)) (H / sin t + H / cos t) ×ˢ Icc 0 1
  exact ⟨⟨by linarith, by linarith⟩, hy₀, hy₁⟩

/-- Actual penalized maximality, with no balancing condition. -/
def IsPenalizedMax {Θ : AngleSet} (S : SupportSamples Θ)
    (target K : Set (ℝ × ℝ)) : Prop :=
  IsPolygonCap Θ K ∧ ∀ C, IsPolygonCap Θ C →
    polyArea Θ C - S.penalty target C ≤ polyArea Θ K - S.penalty target K

/-- Positive penalized value implies a bound on the unpenalized objective and
on the nonnegative penalty, using a supplied polygon-width bound. -/
theorem penalty_and_area_le_of_positive {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {c : ℝ}
    (hcK : ∀ C, IsPolygonCap Θ C → 0 < polyArea Θ C → width C 0 ≤ c)
    (hpos : 0 < polyArea Θ K - S.penalty target K) :
    polyArea Θ K ≤ c ∧ S.penalty target K ≤ c := by
  have hP := S.penalty_nonneg target K
  have hApos : 0 < polyArea Θ K := by linarith
  have hw := hcK K hK hApos
  have ha := mpc_area_le_width hK.1
  have hN : 0 ≤ area (polyNiche Θ K) := ENNReal.toReal_nonneg
  have heq := theorem3_2_3 hK
  constructor <;> linarith

/-- The penalized objective attains its supremum whenever a positive reference
value and two positively weighted orthogonal samples are available. -/
theorem exists_penalizedMax {Θ : AngleSet} (S : SupportSamples Θ)
    (target : Set (ℝ × ℝ)) {t : ℝ} (ht : t ∈ Θ.angles)
    (i₀ i₁ : S.Index) (hi₀ : S.normal i₀ = t) (hi₁ : S.normal i₁ = t + π / 2)
    (hw₀ : 0 < S.weight i₀) (hw₁ : 0 < S.weight i₁)
    {R₀ : Set (ℝ × ℝ)} (hR₀ : IsPolygonCap Θ R₀)
    (hpositive : 0 < polyArea Θ R₀ - S.penalty target R₀) :
    ∃ K, IsPenalizedMax S target K := by
  classical
  obtain ⟨c, hc, hcAll⟩ := lemma3_4_2 Θ.hω (mpc_angles_bounds ht)
  have hcK : ∀ C, IsPolygonCap Θ C → 0 < polyArea Θ C → width C 0 ≤ c :=
    fun C hC hpos => hcAll Θ rfl ht C hC hpos
  let F : Set (ℝ × ℝ) → ℝ := fun K => polyArea Θ K - S.penalty target K
  have hFbound : ∀ K, IsPolygonCap Θ K → F K ≤ c := by
    intro K hK
    by_cases hp : 0 < F K
    · have hA := (penalty_and_area_le_of_positive S hK hcK hp).1
      have hP := S.penalty_nonneg target K
      dsimp [F]
      linarith
    · exact (le_of_not_gt hp).trans hc.le
  let values : Set ℝ := {x | ∃ K, IsPolygonCap Θ K ∧ F K = x}
  have hbdd : BddAbove values := ⟨c, by rintro _ ⟨K, hK, rfl⟩; exact hFbound K hK⟩
  have hmem : F R₀ ∈ values := ⟨R₀, hR₀, rfl⟩
  let M := sSup values
  have hMref : F R₀ ≤ M := le_csSup hbdd hmem
  have hMpos : 0 < M := hpositive.trans_le hMref
  have hseq : ∀ n : ℕ, ∃ K, IsPolygonCap Θ K ∧
      M - 1 / (n + 1) < F K ∧ 0 < F K := by
    intro n
    have hlt : max (M - 1 / (n + 1)) (M / 2) < M := by
      apply max_lt
      · have h : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
      · linarith
    obtain ⟨_, ⟨K, hK, rfl⟩, hval⟩ := exists_lt_of_lt_csSup ⟨_, hmem⟩ hlt
    exact ⟨K, hK, (le_max_left _ _).trans_lt hval,
      by linarith [le_max_right (M - 1 / (n + 1)) (M / 2)]⟩
  choose Ks hKs hnear hpos using hseq
  let q := min (S.weight i₀) (S.weight i₁)
  have hq : 0 < q := lt_min hw₀ hw₁
  have hq₀ : q ≤ S.weight i₀ := min_le_left _ _
  have hq₁ : q ≤ S.weight i₁ := min_le_right _ _
  let R := sampleBoxRadius target t c q
  have hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
    intro n
    have hP := (penalty_and_area_le_of_positive S (hKs n) hcK (hpos n)).2
    have h₀ := (S.sample_bound target (Ks n) i₀).trans hP
    have h₁ := (S.sample_bound target (Ks n) i₁).trans hP
    rw [hi₀] at h₀
    rw [hi₁] at h₁
    apply polygon_subset_sampleBox (hKs n) ht hc.le hq
    · exact (mul_le_mul_of_nonneg_right hq₀ (sq_nonneg _)).trans h₀
    · exact (mul_le_mul_of_nonneg_right hq₁ (sq_nonneg _)).trans h₁
  have hR : 0 ≤ R := sampleBoxRadius_nonneg target (mpc_angles_bounds ht).1
    ((mpc_angles_bounds ht).2.trans_le (mpc_omega_le Θ)) hc.le hq
  let v : ℕ → ({s // s ∈ mpcDiamond Θ} → ℝ) := fun n s => supp (Ks n) s.1
  have hvb : ∀ n, v n ∈ Metric.closedBall (0 : {s // s ∈ mpcDiamond Θ} → ℝ) (R + 1) := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    intro s
    obtain ⟨p, hp, hpe⟩ := exists_dot_eq_supp (hKs n).1.2.1.2.1 (hKs n).1.2.1.1 s.1
    rw [Real.norm_eq_abs]
    change |supp (Ks n) s.1| ≤ R + 1
    rw [← hpe]
    have hdot := mpc_abs_dot_uvec_le p s.1
    obtain ⟨hx, hy⟩ := hbox n hp
    have hx' : |p.1| ≤ R := abs_le.mpr hx
    have hy' : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    linarith
  obtain ⟨a, _, φ, hφ, hvlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hvb
  let hinf : ℝ → ℝ := fun s => if hs : s ∈ mpcDiamond Θ then a ⟨s, hs⟩ else 0
  have hlim : ∀ s ∈ Θ.diamond,
      Tendsto (fun n => supp (Ks (φ n)) s) atTop (𝓝 (hinf s)) := by
    intro s hs
    have hs' := mpc_mem_mpcDiamond.mpr hs
    have h := tendsto_pi_nhds.mp hvlim ⟨s, hs'⟩
    have he : hinf s = a ⟨s, hs'⟩ := by simp only [hinf, hs', dite_true]
    rw [he]
    exact h
  obtain ⟨hLcap, hsupp, _, husc, hlsc⟩ := mpc_limit_polycap (fun n => hKs (φ n))
    (isCompact_Icc.prod isCompact_Icc) (fun n => hbox (φ n)) hlim
  have hPlim : Tendsto (fun n => S.penalty target (Ks (φ n))) atTop
      (𝓝 (S.penalty target (capH Θ hinf))) := by
    apply S.penalty_tendsto
    intro i
    rw [hsupp _ (S.normal_mem i)]
    exact hlim _ (S.normal_mem i)
  have hML : M ≤ F (capH Θ hinf) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hε4 : 0 < ε / 4 := by positivity
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε4
    have hnear' : ∀ᶠ n in atTop, M - ε / 4 < F (Ks (φ n)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have h₁ := hnear (φ n)
      have h₂ : (1 : ℝ) / (φ n + 1) ≤ 1 / (N + 1) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        have hNφ : (N : ℝ) ≤ φ n := by exact_mod_cast hn.trans (hφ.id_le n)
        linarith
      linarith
    have hP' : ∀ᶠ n in atTop,
        S.penalty target (capH Θ hinf) - ε / 4 < S.penalty target (Ks (φ n)) :=
      hPlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨n, hn⟩ := (hnear'.and ((husc (ε / 4) hε4).and
      ((hlsc (ε / 4) hε4).and hP'))).exists
    rcases hn with ⟨hn, hA, hN, hP⟩
    dsimp [F] at hn ⊢
    rw [theorem3_2_3 hLcap]
    rw [theorem3_2_3 (hKs (φ n))] at hn
    linarith
  refine ⟨capH Θ hinf, hLcap, ?_⟩
  intro K hK
  exact (le_csSup hbdd ⟨K, hK, rfl⟩).trans hML

end MovingSofaUniqueness

end

/-!
## The approximation facts needed by the sampled selector

Only upper semicontinuity of the varying polygon objective is needed. The
niches of caps in a common horizontal box have a common bounded rectangle;
this does NOT use niche containment in the cap or balancedness. Eventual
membership in the open inner quadrants then gives the required lower bound
for the niche areas.

Agreement on all persistent dyadic supports identifies a cap. There is no
uniform convergence theorem for the area functionals hidden in that step.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- A uniform bound for niches, without assuming that a niche is in its cap. -/
theorem niche_subset_box {K : Set (ℝ × ℝ)} {ω R : ℝ}
    (hK : IsCap K ω) (hR : 0 ≤ R)
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    niche K ω ⊆ Icc (-R) R ×ˢ Icc 0 (2 * R) := by
  have hcb := hK.2.1
  rintro p ⟨⟨_, hfy⟩, hquad⟩
  have hy₀ : 0 ≤ p.2 := by
    simpa only [halfPlus, mem_ofPred_eq, nef_dot_uvec_pi_div_two] using hfy
  obtain ⟨t, ht, hp⟩ := mem_iUnion₂.mp hquad
  have hcos : 0 < cos t :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2.trans_le hK.1.2⟩
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, hK.1.2, pi_pos])
  have hsupA : supp K t ≤ R * cos t + 1 := by
    apply nef_supp_le hcb.1
    intro q hq
    obtain ⟨⟨_, hx₁⟩, _, hy₁⟩ := hbox hq
    simp only [dot, uvec]
    nlinarith [sin_le_one t, mul_le_mul_of_nonneg_right hx₁ hcos.le,
      mul_le_mul_of_nonneg_right hy₁ hsin.le]
  have hsupC : supp K (t + π / 2) ≤ R * sin t + 1 := by
    apply nef_supp_le hcb.1
    intro q hq
    obtain ⟨⟨hx₀, _⟩, _, hy₁⟩ := hbox hq
    rw [uvec_add_pi_div_two]
    simp only [dot, vvec]
    nlinarith [cos_le_one t, mul_le_mul_of_nonneg_right (show -q.1 ≤ R by linarith) hsin.le,
      mul_le_mul_of_nonneg_right hy₁ hcos.le]
  rw [proposition2_2_2_qMinus] at hp
  have hpa : dot p (uvec t) < R * cos t := by
    have h : dot p (uvec t) < supp K t - 1 := hp.1
    linarith
  have hpc : dot p (vvec t) < R * sin t := by
    have h : dot p (uvec (t + π / 2)) < supp K (t + π / 2) - 1 := hp.2
    rw [uvec_add_pi_div_two] at h
    linarith
  have hx₁ : p.1 < R := by
    simp only [dot, uvec] at hpa
    nlinarith
  have hx₀ : -R < p.1 := by
    simp only [dot, vvec] at hpc
    nlinarith
  have hyid : p.2 = sin t * dot p (uvec t) + cos t * dot p (vvec t) := by
    simp only [dot, uvec, vvec]
    linear_combination (-p.2) * sin_sq_add_cos_sq t
  have hylt : p.2 < 2 * R * (sin t * cos t) := by
    rw [hyid]
    have h₁ := mul_lt_mul_of_pos_left hpa hsin
    have h₂ := mul_lt_mul_of_pos_left hpc hcos
    nlinarith
  have hprod : sin t * cos t ≤ 1 := by
    have h := mul_le_mul (sin_le_one t) (cos_le_one t) hcos.le zero_le_one
    simpa only [one_mul] using h
  have hy₁ : p.2 ≤ 2 * R := by
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * R by positivity)
    linarith
  exact ⟨⟨hx₀.le, hx₁.le⟩, hy₀, hy₁⟩

/-- The same rectangle bounds every sampled niche of a cap in the box. -/
theorem polyNiche_subset_box {Θ : AngleSet} {K : Set (ℝ × ℝ)} {R : ℝ}
    (hK : IsCap K Θ.ω) (hR : 0 ≤ R)
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    polyNiche Θ K ⊆ Icc (-R) R ×ˢ Icc 0 (2 * R) :=
  (proposition3_2_2 hK).2.trans (niche_subset_box hK hR hbox)

/-- Upper semicontinuity of the varying dyadic polygon objective along a
Hausdorff-convergent sequence. No maximizer hypothesis is used. -/
theorem dyadic_objective_limsup {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {k : ℕ → ℕ} (hk : StrictMono k) {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ n, IsPolygonCap (dyadicAngleSet ω hω (k n)) (Ks n))
    {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      polyArea (dyadicAngleSet ω hω (k n)) (Ks n) ≤ sofaArea ω K + ε := by
  intro ε hε
  have hKsc : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.2.1
  have hA := mpc_area_usc hK hKsc hlim (half_pos hε)
  have hN := mpc_area_lsc (N := niche K ω)
    (fun p hp => mpc_niche_eventually hω hK hk hKsc hlim hp)
    ((isCompact_Icc.prod isCompact_Icc).isBounded :
      Bornology.IsBounded (Icc (-R) R ×ˢ Icc (0 : ℝ) (2 * R)))
    (Eventually.of_forall fun n => polyNiche_subset_box (hKs n).1 hR (hbox n))
    (half_pos hε)
  filter_upwards [hA, hN] with n hnA hnN
  rw [theorem3_2_3 (hKs n)]
  unfold sofaArea
  linarith

/-- Exact recovery comparison plus a one-sided objective limit forces the
possibly varying nonnegative penalties to converge to zero. -/
theorem penalty_tendsto_zero_of_objective
    (F P : ℕ → ℝ) (M A : ℝ) (hP : ∀ n, 0 ≤ P n)
    (hselect : ∀ n, M ≤ F n - P n) (hA : A ≤ M)
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop, F n ≤ A + ε) :
    Tendsto P atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hP n)
  · intro b hb
    filter_upwards [hupper (b / 2) (by linarith)] with n hn
    have h := hselect n
    linarith

/-- Continuous functions agreeing on every dyadic angle agree on the whole
closed rotation interval, including its two endpoints. -/
theorem eqOn_of_dyadic_eq {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ m, ∀ t ∈ (dyadicAngleSet ω hω m).angles, f t = g t) :
    EqOn f g (Icc 0 ω) := by
  let E : Set ℝ := {t | f t = g t}
  have hE : IsClosed E := isClosed_eq hf hg
  have hI : Ioo 0 ω ⊆ E := by
    intro t ht
    have htE : t ∈ closure E := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨m, s, hs, hst⟩ := mpc_dyadic_dense hω ht hε
      refine ⟨s, heq m s hs, ?_⟩
      rw [Real.dist_eq, abs_sub_comm]
      exact hst
    rwa [hE.closure_eq] at htE
  have hclosure := closure_minimal hI hE
  rw [closure_Ioo hω.1.ne] at hclosure
  exact hclosure

/-- Upper supports and the standard lower strips determine the entire cap. -/
theorem caps_eq_of_upper_supports {ω : ℝ} {K L : Set (ℝ × ℝ)}
    (hK : IsCap K ω) (hL : IsCap L ω)
    (heq : ∀ t ∈ jSet ω, supp K t = supp L t) : K = L := by
  have hA : ∀ t ∈ jSet ω ∪ {ω + π, 3 * π / 2}, supp K t = supp L t := by
    intro t ht
    simp only [mem_union, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with ht | rfl | rfl
    · exact heq t ht
    · rw [hK.2.2.2.2.1, hL.2.2.2.2.1]
    · rw [hK.2.2.2.2.2.1, hL.2.2.2.2.2.1]
  rw [nef_eq_setOf_supp hK.2.1 hK.2.2.2.2.2.2,
    nef_eq_setOf_supp hL.2.1 hL.2.2.2.2.2.2]
  ext p
  constructor
  · intro hp t ht
    rw [← hA t ht]
    exact hp t ht
  · intro hp t ht
    rw [hA t ht]
    exact hp t ht

/-- Persistent first and shifted dyadic supports identify a standard cap. -/
theorem caps_eq_of_dyadic_supports {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {K L : Set (ℝ × ℝ)} (hK : IsCap K ω) (hL : IsCap L ω)
    (heq : ∀ m, ∀ t ∈ (dyadicAngleSet ω hω m).angles,
      supp K t = supp L t ∧ supp K (t + π / 2) = supp L (t + π / 2)) : K = L := by
  have hfirst := eqOn_of_dyadic_eq hω (continuous_supp hK.2.1.2.1)
    (continuous_supp hL.2.1.2.1) (fun m t ht => (heq m t ht).1)
  have hsecond := eqOn_of_dyadic_eq hω
    (f := fun s => supp K (s + π / 2)) (g := fun s => supp L (s + π / 2))
    ((continuous_supp hK.2.1.2.1).comp (continuous_id.add continuous_const))
    ((continuous_supp hL.2.1.2.1).comp (continuous_id.add continuous_const))
    (fun m t ht => (heq m t ht).2)
  apply caps_eq_of_upper_supports hK hL
  intro t ht
  rcases ht with ht | ht
  · exact hfirst ht
  · have h := hsecond (show t - π / 2 ∈ Icc (0 : ℝ) ω by
      constructor <;> linarith [ht.1, ht.2])
    simpa only [sub_add_cancel] using h

end MovingSofaUniqueness

end

/-!
## Polygon selection which retains the specified maximizer

The finite objective is A_n-P_n. The recovery polygon has P_n=0 exactly.
Persistent dyadic sample weights identify every Hausdorff subsequential limit
with the specified cap. Two coarsest samples give a common bounding box before
compactness is used. Neither a vanishing penalty weight nor uniform convergence
of the objectives is assumed.

Only a convergent subsequence is selected, which is all the subsequent
variational arguments require. Its finite polygons remain exact maximizers of
A_n-P_n, never reclassified as unpenalized or balanced maxima.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Every stage has an actual penalized maximizer. -/
theorem exists_dyadic_penalizedMax {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target) (n : ℕ) :
    ∃ K, IsPenalizedMax (dyadicSamples ω hω n) target K := by
  obtain ⟨t₀, ht₀⟩ := (dyadicAngleSet ω hω 0).nonempty
  have ht₀n : t₀ ∈ (dyadicAngleSet ω hω n).angles :=
    mpc_dyadic_mono hω (Nat.zero_le n) ht₀
  let i₀ : DyadicSampleIndex ω hω n := ⟨⟨0, by omega⟩, ⟨⟨t₀, ht₀⟩, 0⟩⟩
  let i₁ : DyadicSampleIndex ω hω n := ⟨⟨0, by omega⟩, ⟨⟨t₀, ht₀⟩, 1⟩⟩
  have hR := (proposition3_2_1 (Θ := dyadicAngleSet ω hω n) hK).2
  apply exists_penalizedMax (dyadicSamples ω hω n) target ht₀n i₀ i₁
  · simp [dyadicSamples, i₀]
  · simp [dyadicSamples, i₁]
  · exact dyadicLevelWeight_pos ω hω 0
  · exact dyadicLevelWeight_pos ω hω 0
  · exact hR
  · exact hpositive.trans_le (dyadic_recovery_ge ω hω hK n)

/-- The recovery comparison gives the continuum value as a lower bound for
the selected finite penalized objective at every stage. -/
theorem selected_objective_ge {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target K : Set (ℝ × ℝ)} (hK : IsCap target ω) {n : ℕ}
    (hselected : IsPenalizedMax (dyadicSamples ω hω n) target K) :
    sofaArea ω target ≤ polyArea (dyadicAngleSet ω hω n) K -
      dyadicPenalty ω hω n target K := by
  have hrec := dyadic_recovery_ge ω hω hK n
  have hmax := hselected.2 (polyCap (dyadicAngleSet ω hω n) target)
    (proposition3_2_1 (Θ := dyadicAngleSet ω hω n) hK).2
  exact hrec.trans hmax

/-- A common box for a full sequence of selected finite maximizers. Its bound
uses the persistent coarsest samples, not any fine-grid angle denominator. -/
theorem selected_sequence_bounded {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target)
    (Ks : ℕ → Set (ℝ × ℝ))
    (hKs : ∀ n, IsPenalizedMax (dyadicSamples ω hω n) target (Ks n)) :
    ∃ R ≥ 0, ∀ n, Ks n ⊆ Icc (-R) R ×ˢ Icc 0 1 := by
  obtain ⟨t₀, ht₀⟩ := (dyadicAngleSet ω hω 0).nonempty
  have htI : t₀ ∈ Ioo 0 ω := (dyadicAngleSet ω hω 0).subset t₀ ht₀
  obtain ⟨c, hc, hcAll⟩ := lemma3_4_2 hω htI
  let q := dyadicLevelWeight ω hω 0
  have hq : 0 < q := dyadicLevelWeight_pos ω hω 0
  let R := sampleBoxRadius target t₀ c q
  refine ⟨R, sampleBoxRadius_nonneg target htI.1 (htI.2.trans_le hω.2) hc.le hq, ?_⟩
  intro n
  have ht₀n := mpc_dyadic_mono hω (Nat.zero_le n) ht₀
  have hFn : 0 < polyArea (dyadicAngleSet ω hω n) (Ks n) -
      dyadicPenalty ω hω n target (Ks n) :=
    hpositive.trans_le (selected_objective_ge hω hK (hKs n))
  have hwidth : ∀ C, IsPolygonCap (dyadicAngleSet ω hω n) C →
      0 < polyArea (dyadicAngleSet ω hω n) C → width C 0 ≤ c :=
    fun C hC hpos => hcAll (dyadicAngleSet ω hω n) rfl ht₀n C hC hpos
  have hP := (penalty_and_area_le_of_positive (dyadicSamples ω hω n)
    (hKs n).1 hwidth hFn).2
  have h₀ := (persistent_sample_first ω hω (Nat.zero_le n) ht₀ target (Ks n)).trans hP
  have h₁ := (persistent_sample_second ω hω (Nat.zero_le n) ht₀ target (Ks n)).trans hP
  exact polygon_subset_sampleBox (hKs n).1 ht₀n hc.le hq h₀ h₁

/-- The exact data passed to the variational and limiting arguments. -/
structure SelectedCapSequence (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2))
    (target : Set (ℝ × ℝ)) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  cap : ℕ → Set (ℝ × ℝ)
  selected : ∀ n, IsPenalizedMax (dyadicSamples ω hω (index n)) target (cap n)
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  boxed : ∀ n, cap n ⊆ Icc (-radius) radius ×ˢ Icc 0 1
  tends : HausdorffTendsto cap target

/-- Selection of the specified cap, rather than an arbitrary limit maximizer. -/
theorem exists_selectedCapSequence {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target : Set (ℝ × ℝ)} (hK : IsCap target ω)
    (hpositive : 0 < sofaArea ω target)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω target) :
    Nonempty (SelectedCapSequence ω hω target) := by
  classical
  choose Ks hKs using fun n => exists_dyadic_penalizedMax hω hK hpositive n
  obtain ⟨R, hR, hbox⟩ := selected_sequence_bounded hω hK hpositive Ks hKs
  have hKsc : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.1.2.1
  obtain ⟨L, hL, _, φ, hφ, hlim⟩ := mpc_blaschke hKsc
    (isCompact_Icc.prod isCompact_Icc) hbox
  have hpoly : ∀ n, IsPolygonCap (dyadicAngleSet ω hω (φ n)) (Ks (φ n)) :=
    fun n => (hKs (φ n)).1
  have hLcap : IsCap L ω := mpc_limit_isCap hω (fun _ => rfl) hpoly hL hlim
  have hupper := dyadic_objective_limsup hω hφ hpoly hL hlim hR (fun n => hbox (φ n))
  have hPzero : Tendsto (fun n => dyadicPenalty ω hω (φ n) target (Ks (φ n)))
      atTop (𝓝 0) := by
    apply penalty_tendsto_zero_of_objective
      (fun n => polyArea (dyadicAngleSet ω hω (φ n)) (Ks (φ n)))
      (fun n => dyadicPenalty ω hω (φ n) target (Ks (φ n)))
      (sofaArea ω target) (sofaArea ω L)
    · exact fun n => dyadicPenalty_nonneg ω hω (φ n) target (Ks (φ n))
    · exact fun n => selected_objective_ge hω hK (hKs (φ n))
    · exact hmax L hLcap
    · exact hupper
  have hsame : L = target := by
    apply caps_eq_of_dyadic_supports hω hLcap hK
    intro m t ht
    have hcoef : 0 < dyadicLevelWeight ω hω m := dyadicLevelWeight_pos ω hω m
    have hlarge : ∀ᶠ n in atTop, m ≤ φ n := hφ.tendsto_atTop.eventually_ge_atTop m
    have hsupport := mpc_supp_tendsto hL (fun n => hKsc (φ n)) hlim
    have hfirstLim : Tendsto (fun n => dyadicLevelWeight ω hω m *
        (supp (Ks (φ n)) t - supp target t) ^ 2) atTop
        (𝓝 (dyadicLevelWeight ω hω m * (supp L t - supp target t) ^ 2)) :=
      ((hsupport t).sub_const (supp target t)).pow 2 |>.const_mul (dyadicLevelWeight ω hω m)
    have hsecondLim : Tendsto (fun n => dyadicLevelWeight ω hω m *
        (supp (Ks (φ n)) (t + π / 2) - supp target (t + π / 2)) ^ 2) atTop
        (𝓝 (dyadicLevelWeight ω hω m * (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2)) :=
      ((hsupport (t + π / 2)).sub_const (supp target (t + π / 2))).pow 2
        |>.const_mul (dyadicLevelWeight ω hω m)
    have hfirst : dyadicLevelWeight ω hω m * (supp L t - supp target t) ^ 2 ≤ 0 := by
      apply le_of_tendsto_of_tendsto hfirstLim hPzero
      filter_upwards [hlarge] with n hn
      exact persistent_sample_first ω hω hn ht target (Ks (φ n))
    have hsecond : dyadicLevelWeight ω hω m *
        (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤ 0 := by
      apply le_of_tendsto_of_tendsto hsecondLim hPzero
      filter_upwards [hlarge] with n hn
      exact persistent_sample_second ω hω hn ht target (Ks (φ n))
    constructor
    · have hsq : (supp L t - supp target t) ^ 2 = 0 := by
        nlinarith [sq_nonneg (supp L t - supp target t)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    · have hsq : (supp L (t + π / 2) - supp target (t + π / 2)) ^ 2 = 0 := by
        nlinarith [sq_nonneg (supp L (t + π / 2) - supp target (t + π / 2))]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  refine ⟨⟨φ, hφ, fun n => Ks (φ n), fun n => hKs (φ n), R, hR,
    fun n => hbox (φ n), ?_⟩⟩
  rw [← hsame]
  exact hlim

end MovingSofaUniqueness

end
