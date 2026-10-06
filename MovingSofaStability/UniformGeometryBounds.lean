module

public import MovingSofaStability.CoreMonotonicity

/-!
# Uniform bounds in a cap neighborhood

Uncompiled proof source. Coarse Euclidean constants are intentional. They
control changing hallway angles and support perturbations independently of
any regularity of the cap boundary.
-/

@[expose] public section
noncomputable section

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

theorem abs_dot_le_norm2_mul (p q : Point) : |dot p q| ≤ norm2 p * norm2 q := by
  apply abs_le.mpr
  constructor
  · have h := dot_le_norm2_mul (-p) q
    rw [norm2_neg] at h
    simp only [dot, Prod.fst_neg, Prod.snd_neg] at h ⊢
    nlinarith
  · exact dot_le_norm2_mul p q

theorem norm2_uvec_sub_le (s t : ℝ) : norm2 (uvec s - uvec t) ≤ 2 * |s - t| := by
  sorry

theorem norm2_vvec (t : ℝ) : norm2 (vvec t) = 1 := by
  rw [← uvec_add_pi_div_two]
  exact norm2_uvec _

theorem norm2_vvec_sub_le (s t : ℝ) : norm2 (vvec s - vvec t) ≤ 2 * |s - t| := by
  rw [← uvec_add_pi_div_two, ← uvec_add_pi_div_two]
  simpa only [add_sub_add_right_eq_sub] using norm2_uvec_sub_le (s + π / 2) (t + π / 2)

theorem exists_uniform_cap_radius {K₀ : Set Point} (h₀ : IsCap K₀ (π / 2)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ K : Set Point, IsCap K (π / 2) →
      UpperSupportClose 1 K K₀ → ∀ p ∈ K, norm2 p ≤ R := by
  let B := K₀ + euclideanDisk 1
  have hB := convexBody_add h₀.2.1 (euclideanDisk_isConvexBody (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨M, hM⟩ := hB.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro K hK hclose p hp
  have hpB := cap_subset_unit_parallel hK h₀ le_rfl hclose hp
  have hb : norm2 p ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm2_nonneg p)] using hM p hpB
  exact hb.trans (le_max_right _ _)

/-- A radius bound controls every support, including negative supports. -/
theorem support_abs_le_radius {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR : ∀ p ∈ K, norm2 p ≤ R) (t : ℝ) : |supp K t| ≤ R := by
  obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hs]
  have h := abs_dot_le_norm2_mul p (uvec t)
  rw [norm2_uvec, mul_one] at h
  exact h.trans (hR p hp)

/-- Support functions have a uniform angular Lipschitz constant in a bounded cap family. -/
theorem support_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) (s t : ℝ) :
    |supp K s - supp K t| ≤ 2 * R * |s - t| := by
  have one_way : ∀ s t, supp K s - supp K t ≤ 2 * R * |s - t| := by
    intro s t
    obtain ⟨p, hp, hs⟩ := exists_dot_eq_supp hK.2.1 hK.1 s
    have ht := dot_le_supp hK.2.1 hp t
    have hd := abs_dot_le_norm2_mul p (uvec s - uvec t)
    have hb := mul_le_mul (hR p hp) (norm2_uvec_sub_le s t)
      (norm2_nonneg _) hR0
    have hh := (le_abs_self _).trans (hd.trans hb)
    rw [dot_sub_right] at hh
    nlinarith
  have h1 := one_way s t
  have h2 := one_way t s
  rw [abs_sub_comm t s] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem innerCorner_support_error {δ : ℝ} {K L : Set Point}
    (h : UpperSupportClose δ K L) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    euclideanDist (innerCorner K t) (innerCorner L t) ≤ 2 * δ := by
  have h1 := h t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
  have h2 := h (t + π / 2) ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have he : innerCorner K t - innerCorner L t =
      (supp K t - supp L t) • uvec t +
      (supp K (t + π / 2) - supp L (t + π / 2)) • vvec t := by
    rw [proposition2_2_2_innerCorner, proposition2_2_2_innerCorner]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  unfold euclideanDist
  rw [he]
  have hh := norm2_add_le ((supp K t - supp L t) • uvec t)
    ((supp K (t + π / 2) - supp L (t + π / 2)) • vvec t)
  rw [norm2_smul, norm2_smul, norm2_uvec, norm2_vvec, mul_one, mul_one] at hh
  linarith

/-- The inner-wall slacks are uniformly Lipschitz in the hallway angle. -/
theorem innerSlack_angle_bound {K : Set Point} (hK : IsConvexBody K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R) {p : Point} (hp : p ∈ K) (s t : ℝ) :
    |innerSlackU K s p - innerSlackU K t p| ≤ 4 * R * |s - t| ∧
      |innerSlackV K s p - innerSlackV K t p| ≤ 4 * R * |s - t| := by
  have hU : |dot p (uvec s - uvec t)| ≤ 2 * R * |s - t| := by
    have h := (abs_dot_le_norm2_mul p (uvec s - uvec t)).trans
      (mul_le_mul (hR p hp) (norm2_uvec_sub_le s t) (norm2_nonneg _) hR0)
    nlinarith
  have hV : |dot p (vvec s - vvec t)| ≤ 2 * R * |s - t| := by
    have h := (abs_dot_le_norm2_mul p (vvec s - vvec t)).trans
      (mul_le_mul (hR p hp) (norm2_vvec_sub_le s t) (norm2_nonneg _) hR0)
    nlinarith
  have hs := support_angle_bound hK hR0 hR s t
  have hsq := support_angle_bound hK hR0 hR (s + π / 2) (t + π / 2)
  rw [add_sub_add_right_eq_sub] at hsq
  constructor
  · have he : innerSlackU K s p - innerSlackU K t p =
        dot p (uvec s - uvec t) - (supp K s - supp K t) := by
      rw [dot_sub_right]
      unfold innerSlackU
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  · have he : innerSlackV K s p - innerSlackV K t p =
        dot p (vvec s - vvec t) - (supp K (s + π / 2) - supp K (t + π / 2)) := by
      rw [dot_sub_right]
      unfold innerSlackV
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)

/-- A partial-angle sofa satisfies the missing full-angle inequalities with a linear allowance. -/
theorem approximate_full_angle_slack {K S : Set Point} (hK : IsCap K (π / 2))
    {R ω : ℝ} (hR0 : 0 ≤ R) (hR : ∀ p ∈ K, norm2 p ≤ R)
    (hω : ω ∈ Icc (0 : ℝ) (π / 2)) (hSK : S ⊆ K)
    (hpartial : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) :
    ApproxHallways K S (4 * R * (π / 2 - ω)) := by
  intro p hp t ht
  by_cases htw : t ≤ ω
  · have hz : 0 ≤ 4 * R * (π / 2 - ω) := by nlinarith [hω.2]
    exact (neg_nonpos.mpr hz).trans (hpartial p hp t ⟨ht.1.le, htw⟩)
  have hwt : ω < t := not_le.mp htw
  have he := innerSlack_angle_bound hK.2.1 hR0 hR (hSK hp) t ω
  have hs := hpartial p hp ω ⟨hω.1, le_rfl⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hwt.le)] at he
  have hU := (abs_le.mp he.1).1
  have hV := (abs_le.mp he.2).1
  have hmax : max (innerSlackU K ω p) (innerSlackV K ω p) ≤
      max (innerSlackU K t p) (innerSlackV K t p) + 4 * R * (t - ω) := by
    apply max_le
    · linarith [le_max_left (innerSlackU K t p) (innerSlackV K t p)]
    · linarith [le_max_right (innerSlackU K t p) (innerSlackV K t p)]
  nlinarith [ht.2]

end MovingSofaStability
