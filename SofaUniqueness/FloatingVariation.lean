module

public import SofaUniqueness.PolygonPenalty
public import SofaUniqueness.PolygonSelection

/-!
# Floating-facet variations of the actual selected polygons

Raising a non-pinned defining height preserves every other sampled actual
support. The changed actual support lies between its old height and the new
assigned height. These two elementary facts, not an unproved support-hat
formula, give the penalty bound needed for stationarity.

The conclusion holds even for a zero-length floating facet. No unpenalized
maximality, balancedness, or geometric regularity is assumed.
Uncompiled source. No admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa

namespace SofaUniqueness

/-- The actual outward-perturbed cap. -/
def floatingCap (Θ : AngleSet) (K : Set (ℝ × ℝ)) (t ε : ℝ) : Set (ℝ × ℝ) :=
  capH Θ (Function.update (supp K) t (supp K t + ε))

theorem floatingCap_polygon {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : IsPolygonCap Θ (floatingCap Θ K t ε) :=
  mpc_capH_update_inner hK htω htL hε

@[simp] theorem floatingCap_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) (t : ℝ) : floatingCap Θ K t 0 = K := by
  classical
  have heq : Function.update (supp K) t (supp K t + 0) = supp K := by
    funext s
    by_cases hs : s = t
    · subst s
      simp
    · simp [hs]
  unfold floatingCap
  rw [heq]
  exact proposition3_3_4 ⟨K, 0, hK, by simp⟩

/-- Every old point satisfies the relaxed upper constraint; the two lower
strip constraints are unchanged. -/
theorem subset_floatingCap {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ} (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hε : 0 ≤ ε) : K ⊆ floatingCap Θ K t ε := by
  classical
  intro p hp
  change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε))
  rw [mpc_mem_capH]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have h := dot_le_supp hK.1.2.1.2.1 hp s
    by_cases hst : s = t
    · subst s
      rw [Function.update_self]
      linarith
    · rw [Function.update_of_ne hst]
      exact h
  · rw [Function.update_of_ne htω.symm, hK.1.2.2.1]
    simpa only [sub_self] using (mpc_cap_nonneg hK.1 hp).2
  · rw [Function.update_of_ne htL.symm, hK.1.2.2.2.1]
    simpa only [sub_self, mpc_dot_uvec_pi_div_two] using (mpc_cap_nonneg hK.1 hp).1

/-- At every defining normal, the old actual support is a lower bound and the
new assigned height is an upper bound for the perturbed actual support. -/
theorem floatingCap_support_bounds {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) (hs : s ∈ Θ.diamond) :
    supp K s ≤ supp (floatingCap Θ K t ε) s ∧
      supp (floatingCap Θ K t ε) s ≤ Function.update (supp K) t (supp K t + ε) s := by
  have hC := floatingCap_polygon hK htω htL hε
  constructor
  · exact supp_mono (subset_floatingCap hK htω htL hε) hK.1.2.1.1 hC.1.2.1.2.1 s
  · apply nef_supp_le hC.1.2.1.1
    intro p hp
    change p ∈ capH Θ (Function.update (supp K) t (supp K t + ε)) at hp
    rw [mpc_mem_capH] at hp
    exact hp.1 s hs

/-- No unsampled-direction estimate is necessary for this selector. -/
theorem floatingCap_support_other {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε s : ℝ}
    (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε)
    (hs : s ∈ Θ.diamond) (hst : s ≠ t) :
    supp (floatingCap Θ K t ε) s = supp K s := by
  have h := floatingCap_support_bounds hK htω htL hε hs
  rw [Function.update_of_ne hst] at h
  exact le_antisymm h.2 h.1

theorem floatingCap_support_self {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) {t ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2) (hε : 0 ≤ ε) :
    |supp (floatingCap Θ K t ε) t - supp K t| ≤ ε := by
  have h := floatingCap_support_bounds hK htω htL hε ht
  rw [Function.update_self] at h
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith

/-- Exact one-sided penalty growth for an outward floating move. -/
theorem floating_penalty_growth {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPolygonCap Θ K) {t η ε : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    S.penalty target (floatingCap Θ K t ε) - S.penalty target K ≤
      (2 * η * S.atNormal t) * ε + S.atNormal t * ε ^ 2 := by
  have h := S.penalty_change_one hη hε hclose
    (fun i hi => floatingCap_support_other hK htω htL hε (S.normal_mem i) hi)
    (fun i hi => by rw [hi]; exact floatingCap_support_self hK ht htω htL hε)
  have hu := (abs_le.mp h).2
  nlinarith

/-- The actual stationarity estimate for selected polygons. Total sample mass,
not the number of finest-mesh normals, controls the sum of these errors. -/
theorem floating_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K) {t η : ℝ}
    (ht : t ∈ Θ.diamond) (htω : t ≠ Θ.ω) (htL : t ≠ π / 2)
    (hη : 0 ≤ η)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤ 2 * η * S.atNormal t := by
  let P : ℝ → ℝ := fun ε => S.penalty target (floatingCap Θ K t ε)
  apply polygon_defect_le_penalty_growth hK.1 ht P (ε₀ := 1)
    (D := S.atNormal t) (by norm_num)
  · intro ε hε
    dsimp only [P]
    rw [floatingCap_zero hK.1]
    exact floating_penalty_growth S hK.1 ht htω htL hη hε.1.le hclose
  · intro ε hε
    have hC := floatingCap_polygon hK.1 htω htL hε.1.le
    have hcomp := hK.2 (floatingCap Θ K t ε) hC
    have h := assigned_comparison_of_actual hK.1 hC
      (Function.update (supp K) t (supp K t + ε)) (0 : ℝ × ℝ)
      (by simp [floatingCap]) (S.penalty target K)
      (S.penalty target (floatingCap Θ K t ε)) hcomp
    simpa only [assignedAreaIncrement, P, floatingCap_zero hK.1] using h

end SofaUniqueness
