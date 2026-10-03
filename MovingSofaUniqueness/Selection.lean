module

public import MovingSofaOptimality.Balanced.BalancedMaximumSofa

/-!
# Proposition 1: polygon caps converging to a given maximizing cap

Let `K` be a cap that maximizes the sofa area `A_ω`. At stage `n`, maximize the polygon sofa area
`A_Θ` over the polygon caps with the `n`-th dyadic normals, minus a squared penalty on the
differences between their support function and `K`'s at dyadic sample normals of total weight at
most one. The polygon circumscribed about `K` has penalty zero, and two orthogonal samples keep the
maximizers in a bounded box, so the maximizers exist (`exists_penalizedMax`) and a subsequence
converges to `K` (`exists_selectedCapSequence`). This is Proposition 1 of
`docs/archive/uniqueness/20-complete-paper-proof.md`, with a fixed penalty on persistent samples in place of
the note's vanishing penalty.
-/

@[expose] public section
noncomputable section

/-!
## Weighted squared penalties

`sampledPenalty s w target f` is the weighted squared distance between finitely many samples `f`
and `target`, with nonnegative weights `w`. If `f` is within `η` of the target and `g` is within `r`
of `f` at every sample, their penalties differ by at most the total weight times
`2 * η * r + r ^ 2` (`sampledPenalty_change_bound`). If `g` differs from `f` only at the samples of
one normal `t`, the total weight of these samples, `normalWeight`, replaces the total weight
(`sampledPenalty_change_on_normal`).
-/

section

open Set Filter Topology
open scoped BigOperators

namespace MovingSofaUniqueness

variable {ι α : Type*}

/-- The weighted squared distance `∑ i ∈ s, w i * (f i - target i) ^ 2` between the samples `f`
and `target`. -/
def sampledPenalty (s : Finset ι) (w target f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (f i - target i) ^ 2

theorem sampledPenalty_nonneg (s : Finset ι) (w target f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ sampledPenalty s w target f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

/-- Each weighted term is at most the whole penalty. -/
theorem sample_sq_le_penalty (s : Finset ι) (w target f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {i : ι} (hi : i ∈ s) :
    w i * (f i - target i) ^ 2 ≤ sampledPenalty s w target f := by
  exact Finset.single_le_sum (f := fun j => w j * (f j - target j) ^ 2)
    (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _)) hi

/-- When a point within `η` of `c` moves by at most `r`, its squared distance to `c` changes by at
most `2 * η * r + r ^ 2`. -/
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

/-- If `f` is within `η` of the target and `g` is within `r` of `f` at every sample, their penalties
differ by at most the total weight times `2 * η * r + r ^ 2`. -/
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

/-- The total weight of the samples at the normal `t`. -/
def normalWeight (s : Finset ι) (normal : ι → α) (w : ι → ℝ) (t : α) : ℝ := by
  classical
  exact ∑ i ∈ s.filter (fun i => normal i = t), w i

theorem normalWeight_nonneg (s : Finset ι) (normal : ι → α) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (t : α) : 0 ≤ normalWeight s normal w t := by
  classical
  exact Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1

/-- If `g` differs from `f` only at the samples of the normal `t`, the bound of
`sampledPenalty_change_bound` holds with the weight `normalWeight` of `t` in place of the total
weight. -/
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

/-- Summing `normalWeight` over a set of normals that contains the normal of every sample gives the
total weight. -/
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

/-- The penalty is continuous in the samples. -/
theorem continuous_sampledPenalty (s : Finset ι) (w target : ι → ℝ) :
    Continuous (sampledPenalty s w target) := by
  unfold sampledPenalty
  fun_prop

end MovingSofaUniqueness

end

/-!
## Support penalties of polygon caps

A `SupportSamples Θ` is a finite family of weighted samples of the defining normals `Θ^◇` of the
polygon caps of `Θ`, in which a normal may occur several times. Its `penalty target K` is the
weighted squared distance between the supports of `K` and `target` at the sampled normals. The
polygon `polyCap Θ target` circumscribed about a cap has the supports of the cap on `Θ^◇`, so its
penalty is zero (`penalty_recovery_zero`) and its penalized objective is at least the sofa area
`A_ω` of the cap (`recovery_objective_ge`).
-/

section

open Set Real Filter Topology MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- Finitely many weighted samples of the defining normals `Θ^◇`; a normal may occur several
times. -/
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

/-- The total weight of the samples. -/
def totalWeight : ℝ := ∑ i, S.weight i

/-- The weighted squared distance between the supports of `K` and `target` at the sampled
normals. -/
def penalty (target K : Set (ℝ × ℝ)) : ℝ :=
  sampledPenalty Finset.univ S.weight (fun i => supp target (S.normal i))
    (fun i => supp K (S.normal i))

/-- The total weight of the samples at the normal `t`. -/
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

/-- Each weighted squared support difference is at most the penalty. -/
theorem sample_bound (target K : Set (ℝ × ℝ)) (i : S.Index) :
    S.weight i * (supp K (S.normal i) - supp target (S.normal i)) ^ 2 ≤
      S.penalty target K :=
  sample_sq_le_penalty Finset.univ S.weight (fun i => supp target (S.normal i))
    (fun i => supp K (S.normal i)) (fun i _ => S.weight_nonneg i) (Finset.mem_univ i)

/-- The polygon `polyCap Θ target` circumscribed about a cap has penalty zero. -/
theorem penalty_recovery_zero {target : Set (ℝ × ℝ)} (hK : IsCap target Θ.ω) :
    S.penalty target (polyCap Θ target) = 0 := by
  unfold penalty sampledPenalty
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [nef_supp_polyCap hK (nef_diamond_subset_capAngles Θ (S.normal_mem i)), sub_self]
  simp

/-- The penalized objective of the polygon circumscribed about a cap is at least the cap's sofa
area `A_ω`. -/
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

/-- The penalty is continuous along sequences whose supports converge at the sampled normals. -/
theorem penalty_tendsto {Ks : ℕ → Set (ℝ × ℝ)} {K target : Set (ℝ × ℝ)}
    (hlim : ∀ i, Tendsto (fun n => supp (Ks n) (S.normal i)) atTop
      (𝓝 (supp K (S.normal i)))) :
    Tendsto (fun n => S.penalty target (Ks n)) atTop (𝓝 (S.penalty target K)) := by
  have hv : Tendsto (fun n i => supp (Ks n) (S.normal i)) atTop
      (𝓝 (fun i => supp K (S.normal i))) := tendsto_pi_nhds.mpr hlim
  exact (continuous_sampledPenalty Finset.univ S.weight
    (fun i => supp target (S.normal i))).continuousAt.tendsto.comp hv

/-- If the sampled supports of `K` are within `η` of the target, and those of `K'` differ from them
only at the normal `t`, by at most `ε`, the penalties differ by at most
`atNormal t * (2 * η * ε + ε ^ 2)`. -/
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

/-- If the sampled supports of `K` are within `η` of the target, and those of `K'` differ from them
by at most `r`, the penalties differ by at most `totalWeight * (2 * η * r + r ^ 2)`. -/
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
## Persistent dyadic samples

At stage `n`, `dyadicSamples` samples the normals `t` and `t + π/2` for the dyadic angles `t` of
every level `m ≤ n`, level `m` carrying the total weight `(1/2)^(m+1)`. The total weight is
`1 - (1/2)^(n+1) ≤ 1` (`dyadic_totalWeight`), and a sample of level `m` keeps the weight
`dyadicLevelWeight m` at every stage `n ≥ m` (`persistent_sample_first`,
`persistent_sample_second`). The circumscribed polygon has penalty zero at every stage, so its
penalized objective is at least `A_ω` of the target (`dyadic_recovery_ge`).
-/

section

open Set Real Filter Topology MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

variable (ω : ℝ) (hω : ω ∈ Ioc 0 (π / 2))

/-- The weight of each sample of level `m`: the level's total weight `(1/2)^(m+1)`, divided equally
among its samples `t` and `t + π/2`. -/
def dyadicLevelWeight (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 1) /
    (2 * ((dyadicAngleSet ω hω m).angles.card : ℝ))

theorem dyadicLevelWeight_pos (m : ℕ) : 0 < dyadicLevelWeight ω hω m := by
  have hcard : 0 < ((dyadicAngleSet ω hω m).angles.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (dyadicAngleSet ω hω m).nonempty
  unfold dyadicLevelWeight
  positivity

/-- The samples of stage `n`: a level `m ≤ n`, a dyadic angle `t` of level `m`, and a choice of `t`
or `t + π/2`. An angle of several levels gives several samples. -/
abbrev DyadicSampleIndex (n : ℕ) : Type :=
  Σ m : Fin (n + 1), ↥(dyadicAngleSet ω hω m.1).angles × Fin 2

/-- The samples of stage `n`: the normals `t` and `t + π/2` for the dyadic angles `t` of the levels
`m ≤ n`. -/
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

/-- The samples of level `m` have total weight `(1/2)^(m+1)`. -/
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

/-- The total weight at stage `n` is `1 - (1/2)^(n+1)`. -/
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

/-- The penalty of stage `n`. -/
def dyadicPenalty (n : ℕ) (target K : Set (ℝ × ℝ)) : ℝ :=
  (dyadicSamples ω hω n).penalty target K

theorem dyadicPenalty_nonneg (n : ℕ) (target K : Set (ℝ × ℝ)) :
    0 ≤ dyadicPenalty ω hω n target K :=
  (dyadicSamples ω hω n).penalty_nonneg target K

/-- The sample at a dyadic angle `t` of level `m ≤ n` keeps the weight `dyadicLevelWeight m` in the
penalty of stage `n`. -/
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

/-- The same for the sample at `t + π/2`. -/
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
## Penalized polygon maximizers exist

`IsPenalizedMax S target K` says that the polygon cap `K` maximizes the penalized objective
`A_Θ(C) - S.penalty target C` over the polygon caps `C` of `Θ`. By Baek's Lemma 3.4.2 a polygon cap
of positive area `A_Θ` has bounded width, and the penalty bounds its supports at two orthogonal
sampled normals `t` and `t + π/2`, so it lies in a fixed box (`polygon_subset_sampleBox`). The
compactness argument of Baek's Theorem 3.4.3 then gives a maximizer (`exists_penalizedMax`).
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- The half-width of the box of `polygon_subset_sampleBox`. -/
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

/-- If `q * (supp K s - supp target s) ^ 2 ≤ c` at `s = t` and at `s = t + π/2`, the polygon cap `K`
lies in `[-R, R] × [0, 1]`, where `R = sampleBoxRadius target t c q`. -/
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

/-- `K` maximizes the penalized objective `A_Θ(C) - S.penalty target C` over the polygon caps `C`
of `Θ`. -/
def IsPenalizedMax {Θ : AngleSet} (S : SupportSamples Θ)
    (target K : Set (ℝ × ℝ)) : Prop :=
  IsPolygonCap Θ K ∧ ∀ C, IsPolygonCap Θ C →
    polyArea Θ C - S.penalty target C ≤ polyArea Θ K - S.penalty target K

/-- If the polygon caps of positive area `A_Θ` have width at most `c`, a polygon cap with positive
penalized objective has `A_Θ` and penalty at most `c`. -/
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

/-- The penalized objective has a maximizer if some polygon cap has a positive penalized objective
and two samples of positive weight lie at normals `t` and `t + π/2`. -/
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
## Limits of dyadic polygon caps

Along a Hausdorff-convergent sequence of polygon caps in a common box, with dyadic angle sets of
increasing level, the objective `A_Θ` is eventually at most `A_ω` of the limit plus any `ε > 0`
(`dyadic_objective_limsup`): the areas of the caps are upper semicontinuous, and every point of the
limit's niche eventually lies in the polygon niches, which stay in a common box
(`polyNiche_subset_box`). A cap is determined by its supports at the dyadic angles `t` and at
`t + π/2` (`caps_eq_of_dyadic_supports`), since support functions are continuous and the dyadic
angles are dense in `[0, ω]`.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The niche of a cap in the box `[-R, R] × [0, 1]` lies in `[-R, R] × [0, 2R]`. -/
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

/-- The same box contains the polygon niche `polyNiche Θ K`. -/
theorem polyNiche_subset_box {Θ : AngleSet} {K : Set (ℝ × ℝ)} {R : ℝ}
    (hK : IsCap K Θ.ω) (hR : 0 ≤ R)
    (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    polyNiche Θ K ⊆ Icc (-R) R ×ˢ Icc 0 (2 * R) :=
  (proposition3_2_2 hK).2.trans (niche_subset_box hK hR hbox)

/-- Along a Hausdorff-convergent sequence of dyadic polygon caps in a common box, `A_Θ` is
eventually at most `A_ω` of the limit plus `ε`. -/
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

/-- If `M ≤ F n - P n` with `P n ≥ 0`, and for every `ε > 0` eventually `F n ≤ A + ε`, where
`A ≤ M`, then `P n → 0`. -/
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

/-- Continuous functions that agree at every dyadic angle agree on `[0, ω]`. -/
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

/-- Caps with the same supports at the upper normals `J_ω` are equal. -/
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

/-- Caps with the same supports at the dyadic angles `t` and at `t + π/2` are equal. -/
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
## Selected polygon caps converge to the given maximizer

Let `target` be a cap maximizing `A_ω`, with positive value. At every stage a penalized maximizer
exists (`exists_dyadic_penalizedMax`), with penalized objective at least `A_ω(target)`
(`selected_objective_ge`), and the two samples of level `0` keep all of them in one box
(`selected_sequence_bounded`). By Blaschke selection a subsequence converges to a cap `L`; the
maximality of `target` and `dyadic_objective_limsup` force the penalties to zero, so `L` has the
dyadic supports of `target` and equals it (`exists_selectedCapSequence`). This is Proposition 1 of
note 20.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Every stage has a penalized maximizer, for a target cap of positive sofa area. -/
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

/-- The penalized objective of a penalized maximizer is at least the sofa area `A_ω` of the
target. -/
theorem selected_objective_ge {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    {target K : Set (ℝ × ℝ)} (hK : IsCap target ω) {n : ℕ}
    (hselected : IsPenalizedMax (dyadicSamples ω hω n) target K) :
    sofaArea ω target ≤ polyArea (dyadicAngleSet ω hω n) K -
      dyadicPenalty ω hω n target K := by
  have hrec := dyadic_recovery_ge ω hω hK n
  have hmax := hselected.2 (polyCap (dyadicAngleSet ω hω n) target)
    (proposition3_2_1 (Θ := dyadicAngleSet ω hω n) hK).2
  exact hrec.trans hmax

/-- Penalized maximizers of all stages lie in one box `[-R, R] × [0, 1]`. -/
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

/-- A subsequence of penalized maximizers in one box `[-R, R] × [0, 1]`, converging to `target` in
the Hausdorff distance. -/
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

/-- Proposition 1 of note 20: a subsequence of penalized polygon maximizers converges to a cap
that maximizes `A_ω` with positive value. -/
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
