module

public import SofaUniqueness.SampledPenalty
public import MovingSofa.Balanced.MaximumPolygonCap

/-!
# Finite penalties on the actual defining supports

The data below include only finitely many upper defining normals, with
nonnegative weights. Repeated normals are allowed. A circumscribed recovery
polygon has exactly the target's values at all these normals, so its penalty
is ZERO, rather than merely tending to zero.

The use of actual support values is essential. Assigned heights are used only
for a comparison whose direction is justified separately in `PolygonPenalty`.
Uncompiled source, without admissions or external evaluation.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MovingSofa
open scoped BigOperators

namespace SofaUniqueness

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

theorem atNormal_eq_zero_of_not_mem {t : ℝ} (ht : t ∉ Θ.diamond) : S.atNormal t = 0 := by
  classical
  unfold atNormal normalWeight
  apply Finset.sum_eq_zero
  intro i hi
  have heq := (Finset.mem_filter.mp hi).2
  exact (ht (heq ▸ S.normal_mem i)).elim

/-- One positively weighted support sample is bounded by the whole penalty. -/
theorem sample_bound (target K : Set (ℝ × ℝ)) (i : S.Index) :
    S.weight i * (supp K (S.normal i) - supp target (S.normal i)) ^ 2 ≤
      S.penalty target K := by
  sorry

/-- A bound on all sampled support differences controls the penalty. -/
theorem penalty_le (target K : Set (ℝ × ℝ)) {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    S.penalty target K ≤ S.totalWeight * η ^ 2 :=
  sampledPenalty_le _ _ _ _ (fun i _ => S.weight_nonneg i) hη (fun i _ => hclose i)

/-- The recovery penalty vanishes identically, at every finite mesh. -/
theorem penalty_recovery_zero {target : Set (ℝ × ℝ)} (hK : IsCap target Θ.ω) :
    S.penalty target (polyCap Θ target) = 0 := by
  sorry

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
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    (hsame : ∀ i, S.normal i ≠ t → supp K' (S.normal i) = supp K (S.normal i))
    (hchange : ∀ i, S.normal i = t → |supp K' (S.normal i) - supp K (S.normal i)| ≤ ε) :
    |S.penalty target K' - S.penalty target K| ≤
      S.atNormal t * (2 * η * ε + ε ^ 2) := by
  exact sampledPenalty_change_on_normal Finset.univ S.normal S.weight
    (fun i => supp target (S.normal i)) (fun i => supp K (S.normal i))
    (fun i => supp K' (S.normal i)) (fun i _ => S.weight_nonneg i) t hη hε
    (fun i _ => hclose i) (fun i _ => hsame i) (fun i _ => hchange i)

/-- Uniform actual-support changes, including normalization after a pinned
move, have a penalty bound controlled by the total sample weight. -/
theorem penalty_change_uniform {target K K' : Set (ℝ × ℝ)} {η r : ℝ}
    (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    (hchange : ∀ i, |supp K' (S.normal i) - supp K (S.normal i)| ≤ r) :
    |S.penalty target K' - S.penalty target K| ≤
      S.totalWeight * (2 * η * r + r ^ 2) := by
  exact sampledPenalty_change_bound Finset.univ S.weight
    (fun i => supp target (S.normal i)) (fun i => supp K (S.normal i))
    (fun i => supp K' (S.normal i)) (fun i _ => S.weight_nonneg i) hη hr
    (fun i _ => hclose i) (fun i _ => hchange i)

end SupportSamples

end SofaUniqueness
