module

public import SofaUniqueness.PinnedGeometry
public import SofaUniqueness.VariationDefect

/-!
# Pinned stationarity and the endpoint balance identity

The structured strip sandwich controls the selected penalty after the actual
normalization supplied by Lemma 3.4.8. The positive pinned defect is therefore
O(eta), where eta is the uniform support distance to the target. The outer and
completed inner boundary walks have the same horizontal displacement. Their
weighted defect sum is zero, so the negative pinned defect is controlled too.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa
open scoped BigOperators

namespace SofaUniqueness

/-- The outward pinned defect for an actual selected polygon. -/
theorem pinned_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {t η R : ℝ} (ht : t = Θ.ω ∨ t = π / 2)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η) :
    sigmaAt K t - tau Θ K t ≤
      2 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1) := by
  classical
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have htd : t ∈ Θ.diamond := by
    rcases ht with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hσ : 0 < sigmaAt K t
  · obtain ⟨r, hr, hfeasible⟩ := lemma3_4_8 hK.1 htd hσ
    let r' := min r 1
    have hr' : 0 < r' := lt_min hr zero_lt_one
    have hC : ∀ e : Ioc (0 : ℝ) r', ∃ C v, IsPolygonCap Θ C ∧
        floatingCap Θ K t e.1 = (fun p => p + v) '' C := by
      intro e
      exact hfeasible e.1 ⟨e.2.1, e.2.2.trans (min_le_left _ _)⟩
    choose C v hCp hset using hC
    let chosen : ℝ → Set (ℝ × ℝ) := fun ε =>
      if he : ε ∈ Ioc (0 : ℝ) r' then C ⟨ε, he⟩ else K
    let P : ℝ → ℝ := fun ε => S.penalty target (chosen ε)
    have hchosen0 : chosen 0 = K := by simp [chosen]
    apply polygon_defect_le_penalty_growth hK.1 htd P hr'
      (D := S.totalWeight * G ^ 2)
    · intro ε he
      have hε : ε ∈ Icc (0 : ℝ) 1 :=
        ⟨he.1.le, he.2.trans (min_le_right _ _)⟩
      have hgrowth := S.penalty_change_uniform hη hclose
        (fun i => pinned_normalized_support_bound hK.1 (hCp ⟨ε, he⟩)
          hω ht hε hR hsupp (v ⟨ε, he⟩) (hset ⟨ε, he⟩) (S.normal i))
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      have h := (abs_le.mp hgrowth).2
      dsimp [G] at h ⊢
      nlinarith
    · intro ε he
      have hcompare := hK.2 (C ⟨ε, he⟩) (hCp ⟨ε, he⟩)
      have h := assigned_comparison_of_actual hK.1 (hCp ⟨ε, he⟩)
        (Function.update (supp K) t (supp K t + ε)) (v ⟨ε, he⟩)
        (hset ⟨ε, he⟩) (S.penalty target K) (S.penalty target (C ⟨ε, he⟩)) hcompare
      dsimp only [P]
      rw [hchosen0, show chosen ε = C ⟨ε, he⟩ from dite_eq_left he]
      exact h
  · have hz : sigmaAt K t = 0 := le_antisymm (le_of_not_gt hσ) ENNReal.toReal_nonneg
    apply polygon_defect_le_of_zero_facet hz
    change 0 ≤ 2 * S.totalWeight * η * G
    have hw := S.totalWeight_nonneg
    positivity

/-- The weighted signed defect identity holds for every polygon cap. -/
theorem polygon_weighted_defect_zero {Θ : AngleSet} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap Θ K) :
    (∑ t ∈ mpcDiamond Θ, sin t * (sigmaAt K t - tau Θ K t)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_comm (sin _)]
  rw [mpc_sum_sigma_sin hK, mpc_sum_tau_sin hK, sub_self]

/-- Total error controlling every defect of the actual sampled selector. -/
def selectorDefectBound {Θ : AngleSet} (S : SupportSamples Θ) (G η t : ℝ) : ℝ := by
  classical
  exact 2 * η * S.atNormal t +
    if t = Θ.ω ∨ t = π / 2 then 2 * S.totalWeight * η * G else 0

theorem selectorDefectBound_nonneg {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) (t : ℝ) :
    0 ≤ selectorDefectBound S G η t := by
  classical
  have hw := S.atNormal_nonneg t
  have hW := S.totalWeight_nonneg
  unfold selectorDefectBound
  split_ifs <;> positivity

/-- At most two pinned normals contribute a normalization error. -/
theorem selectorDefectBound_sum_le {Θ : AngleSet} (S : SupportSamples Θ)
    {G η : ℝ} (hG : 0 ≤ G) (hη : 0 ≤ η) :
    (∑ t ∈ mpcDiamond Θ, selectorDefectBound S G η t) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
  classical
  let b := 2 * S.totalWeight * η * G
  have hb : 0 ≤ b := by
    have hW := S.totalWeight_nonneg
    dsimp [b]
    positivity
  have hpin : (∑ t ∈ mpcDiamond Θ, if t = Θ.ω ∨ t = π / 2 then b else 0) ≤ 2 * b := by
    calc
      (∑ t ∈ mpcDiamond Θ, if t = Θ.ω ∨ t = π / 2 then b else 0)
          ≤ ∑ t ∈ mpcDiamond Θ, ((if t = Θ.ω then b else 0) + (if t = π / 2 then b else 0)) := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs <;> simp_all
      _ ≤ 2 * b := by
        rw [Finset.sum_add_distrib]
        have h₀ : (∑ t ∈ mpcDiamond Θ, if t = Θ.ω then b else 0) ≤ b := by
          by_cases h : Θ.ω ∈ mpcDiamond Θ <;> simp [h, hb]
        have h₁ : (∑ t ∈ mpcDiamond Θ, if t = π / 2 then b else 0) ≤ b := by
          by_cases h : π / 2 ∈ mpcDiamond Θ <;> simp [h, hb]
        linarith
  unfold selectorDefectBound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, S.sum_atNormal]
  dsimp [b] at hpin
  linarith

/-- Two-sided control of any specified upper-normal defect. Only its own
positive sine appears in the denominator, so this is uniform at fixed pins. -/
theorem abs_selected_defect_le {Θ : AngleSet} (S : SupportSamples Θ)
    {target K : Set (ℝ × ℝ)} (hK : IsPenalizedMax S target K)
    (hω : Θ.ω < π / 2) {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hsupp : ∀ s, |supp K s| ≤ R)
    (hclose : ∀ i, |supp K (S.normal i) - supp target (S.normal i)| ≤ η)
    {t : ℝ} (ht : t ∈ Θ.diamond) :
    |sigmaAt K t - tau Θ K t| ≤
      (2 * η * S.totalWeight +
        4 * S.totalWeight * η * (2 * R + 2 / cos Θ.ω + 1)) / sin t := by
  classical
  let G := 2 * R + 2 / cos Θ.ω + 1
  have hcos : 0 < cos Θ.ω :=
    cos_pos_of_mem_Ioo ⟨by linarith [Θ.hω.1, pi_pos], hω⟩
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have herror : ∀ s ∈ mpcDiamond Θ,
      sigmaAt K s - tau Θ K s ≤ selectorDefectBound S G η s := by
    intro s hs
    have hsd := mpc_mem_mpcDiamond.mp hs
    by_cases hpin : s = Θ.ω ∨ s = π / 2
    · have h := pinned_defect_le S hK hω hpin hη hR hsupp hclose
      have hnonneg : 0 ≤ 2 * η * S.atNormal s := by
        have hw := S.atNormal_nonneg s
        positivity
      simp only [selectorDefectBound, ite_eq_left hpin]
      exact h.trans (le_add_of_nonneg_left hnonneg)
    · have hnot := not_or.mp hpin
      simpa only [selectorDefectBound, ite_eq_right hpin, add_zero] using
        floating_defect_le S hK hsd hnot.1 hnot.2 hη hclose
  have h := abs_defect_le_div (mpcDiamond Θ) sin
    (fun s => sigmaAt K s - tau Θ K s) (selectorDefectBound S G η)
    (fun s hs => (mpc_sin_pos_of_diamond (mpc_mem_mpcDiamond.mp hs)).le)
    (fun s _ => selectorDefectBound_nonneg S hG hη s) herror
    (polygon_weighted_defect_zero hK.1) (mpc_mem_mpcDiamond.mpr ht)
    (mpc_sin_pos_of_diamond ht)
  have hsum : (∑ s ∈ mpcDiamond Θ, sin s * selectorDefectBound S G η s) ≤
      2 * η * S.totalWeight + 4 * S.totalWeight * η * G := by
    calc
      _ ≤ ∑ s ∈ mpcDiamond Θ, selectorDefectBound S G η s := by
        apply Finset.sum_le_sum
        intro s hs
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (sin_le_one s)
          (selectorDefectBound_nonneg S hG hη s)
      _ ≤ _ := selectorDefectBound_sum_le S hG hη
  exact h.trans (div_le_div_of_nonneg_right hsum (mpc_sin_pos_of_diamond ht).le)

end SofaUniqueness
