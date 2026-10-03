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

Uncompiled source. No admissions, artificial feasibility assumptions, or
unpenalized maximality hypotheses.
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
  sorry

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
  sorry

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
      simp only [selectorDefectBound, if_pos hpin]
      exact h.trans (le_add_of_nonneg_left hnonneg)
    · have hnot := not_or.mp hpin
      simpa only [selectorDefectBound, if_neg hpin, add_zero] using
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
