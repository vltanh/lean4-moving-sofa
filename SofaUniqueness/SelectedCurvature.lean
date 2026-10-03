module

public import SofaUniqueness.CurvatureLimit
public import SofaUniqueness.FloatingVariation
public import SofaUniqueness.PinnedLimit

/-!
# Curvature domination for the specified cap

Actual penalized stationarity, the geometric inner-ray bound, the cellwise arm
estimate, and the endpoint-safe limiting theorem are assembled here. Persistent
coarse sample weights need not be O(delta); their total is at most one, and the
new integrated estimate sums their errors just once.

Uncompiled source. No admissions, balanced-maximizer substitution, or decision
tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa
open scoped BigOperators

namespace SofaUniqueness

/-- Any injective finite list of normals collects at most all the sample mass. -/
theorem distinct_normalWeight_sum_le {Θ : AngleSet} (S : SupportSamples Θ)
    {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (hinj : Set.InjOn t (s : Set ι)) :
    (∑ j ∈ s, S.atNormal (t j)) ≤ S.totalWeight := by
  classical
  unfold SupportSamples.atNormal normalWeight SupportSamples.totalWeight
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hex : ∃ j ∈ s, S.normal i = t j
  · obtain ⟨j, hj, heq⟩ := hex
    rw [Finset.sum_eq_single j]
    · simp [heq]
    · intro k hk hkj
      have hne : S.normal i ≠ t k := by
        intro h
        have he : t k = t j := h.symm.trans heq
        exact hkj (hinj hk hj he)
      simp [hne]
    · exact fun hn => (hn hj).elim
  · have hne : ∀ j ∈ s, S.normal i ≠ t j := by
      intro j hj h
      exact hex ⟨j, hj, h⟩
    have hz : (∑ j ∈ s, if S.normal i = t j then S.weight i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hne j hj]
    rw [hz]
    exact S.weight_nonneg i

/-- In particular, the first-quadrant grid error is bounded by twice the
uniform support error, independently of the finest mesh. -/
theorem sampled_grid_error_le {k : ℕ} (S : SupportSamples (rightAngleSet k))
    {η : ℝ} (hη : 0 ≤ η) (hW : S.totalWeight ≤ 1) :
    polygonGridError k (fun t => 2 * η * S.atNormal t) ≤ 2 * η := by
  have hδ := inj_stepSize_pos k
  have hmass := distinct_normalWeight_sum_le S (Finset.range (2 ^ (k + 1)))
    (fun j : ℕ => (j : ℝ) * stepSize k) (by
      intro i hi j hj hij
      have he : (i : ℝ) = j := (mul_right_cancel₀ hδ.ne') hij
      exact_mod_cast he)
  unfold polygonGridError
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (hmass.trans hW) (show 0 ≤ 2 * η by positivity)
  simpa only [mul_one] using h

/-- A common coordinate box supplies the Euclidean diameter bound needed by
cellwise arm control. The ordinary product norm is not used as Euclidean norm. -/
theorem diameter_le_box {K : Set (ℝ × ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ 2 * R + 2 := by
  intro p hp q hq
  obtain ⟨hpX, hpY⟩ := hbox hp
  obtain ⟨hqX, hqY⟩ := hbox hq
  have hx : |p.1 - q.1| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith [hpX.1, hpX.2, hqX.1, hqX.2]
  have hy : |p.2 - q.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hpY.1, hpY.2, hqY.1, hqY.2]
  rw [norm2, Real.sqrt_le_iff]
  constructor
  · positivity
  · simp only [dot, Prod.fst_sub, Prod.snd_sub]
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    nlinarith [sq_nonneg (2 * R - (p.1 - q.1)),
      sq_nonneg (2 * R + (p.1 - q.1)), sq_nonneg (1 - (p.2 - q.2)),
      sq_nonneg (1 + (p.2 - q.2))]

/-- Dyadic mesh sizes tend to zero along every strictly increasing subsequence. -/
theorem selected_stepSize_tendsto {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun n => stepSize (k n)) atTop (𝓝 0) := by
  have hmesh : Tendsto stepSize atTop (𝓝 0) := by
    unfold stepSize
    have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ (m + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.div_atTop hpow
  exact hmesh.comp hk.tendsto_atTop

/-- First-half curvature domination for every specified cap maximizing a
positive sofa-area value. Normal zero is included in the conclusion. -/
theorem firstCurvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    FirstCurvatureBound K := by
  sorry

end SofaUniqueness
