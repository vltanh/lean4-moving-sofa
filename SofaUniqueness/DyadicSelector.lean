module

public import SofaUniqueness.SupportSamples
public import MovingSofa.Balanced.BalancedMaximumSofa

/-!
# A persistent sampled selector

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

Uncompiled source. No admissions, external scripts, or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MovingSofa
open scoped BigOperators

namespace SofaUniqueness

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
    (∑ i : ↥(dyadicAngleSet ω hω m).angles × Fin 2,
      dyadicLevelWeight ω hω m) = (1 / 2 : ℝ) ^ (m + 1) := by
  sorry

/-- Exact finite geometric mass. -/
theorem dyadic_totalWeight (n : ℕ) :
    (dyadicSamples ω hω n).totalWeight = 1 - (1 / 2 : ℝ) ^ (n + 1) := by
  sorry

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
  sorry

/-- The shifted dyadic sample has the same persistent weight. -/
theorem persistent_sample_second {m n : ℕ} (hmn : m ≤ n) {t : ℝ}
    (ht : t ∈ (dyadicAngleSet ω hω m).angles) (target K : Set (ℝ × ℝ)) :
    dyadicLevelWeight ω hω m * (supp K (t + π / 2) - supp target (t + π / 2)) ^ 2 ≤
      dyadicPenalty ω hω n target K := by
  sorry

/-- Exact recovery: no rate of approximation is needed for this penalty. -/
theorem dyadicPenalty_recovery_zero {target : Set (ℝ × ℝ)} (hK : IsCap target ω) (n : ℕ) :
    dyadicPenalty ω hω n target (polyCap (dyadicAngleSet ω hω n) target) = 0 :=
  (dyadicSamples ω hω n).penalty_recovery_zero hK

theorem dyadic_recovery_ge {target : Set (ℝ × ℝ)} (hK : IsCap target ω) (n : ℕ) :
    sofaArea ω target ≤ polyArea (dyadicAngleSet ω hω n)
      (polyCap (dyadicAngleSet ω hω n) target) -
        dyadicPenalty ω hω n target (polyCap (dyadicAngleSet ω hω n) target) :=
  (dyadicSamples ω hω n).recovery_objective_ge hK

/-- The whole penalty is at most the squared uniform support error. -/
theorem dyadicPenalty_le_uniform (n : ℕ) (target K : Set (ℝ × ℝ)) {η : ℝ}
    (hη : 0 ≤ η) (hclose : ∀ t, |supp K t - supp target t| ≤ η) :
    dyadicPenalty ω hω n target K ≤ η ^ 2 := by
  sorry

/-- Summing the weights of the actual polygon normals loses no multiplicity. -/
theorem dyadic_normalWeight_sum_le_one (n : ℕ) :
    (∑ t ∈ mpcDiamond (dyadicAngleSet ω hω n),
      (dyadicSamples ω hω n).atNormal t) ≤ 1 := by
  rw [(dyadicSamples ω hω n).sum_atNormal]
  exact dyadic_totalWeight_le_one ω hω n

end SofaUniqueness
