module

public import MovingSofaStability.CanonicalContacts

/-!
# Canonical triples for nearby nonsmooth caps

Uncompiled proof source. All endpoint contacts and linear wall constraints
are proved. The final neighborhood result supplies an actual WideTriple and
does not assume Ki of the competing cap or feasibility of its canonical tails.
The geometric inequality A <= Q is a subsequent, separate result.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The right-body wall inequalities hold for all caps once the cut is nonnegative. -/
theorem canonical_right_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point} (hK : IsCap K (π / 2))
    {t : ℝ} (ht : t ∈ Icc φ (π / 2)) :
    supp K t + supp (rightBody φ K) (π + t) ≤ 1 := by
  sorry

/-- The left-body inequalities are likewise independent of curvature regularity. -/
theorem canonical_left_wall {φ : ℝ} (hφ : 0 ≤ φ) {K : Set Point} (hK : IsCap K (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supp K (π / 2 + t) + supp (leftBody φ K) (3 * π / 2 + t) ≤ 1 := by
  sorry

/-- Feasibility of the canonical triple needs only width and the two cut-arm inequalities. -/
theorem canonical_inWideL_of_cut_arms {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (hg : 1 < gPlus K φ) (hf : 1 < fMinus K (π / 2 - φ)) :
    InWideL φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, -, -, -⟩ := opt_phi_bounds hφ
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  have hp := pi_pos
  have hB := opt_rightBody_isConvexBody hφ0.le hK
  have hD := opt_leftBody_isConvexBody hφ0.le hK
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  obtain ⟨p, hpB, hpR⟩ := canonical_right_contact hφ' hK hW.1.1 hg
  obtain ⟨q, hqD, hqL⟩ := canonical_left_contact hφ' hK hZ.1.1 hf
  have hR : supp K φ + supp (rightBody φ K) (π + φ) = 1 := by
    have hlo := dot_le_supp hB.2.1 hpB (π + φ)
    rw [show π + φ = φ + π by ring, uvec_add_pi, dot_neg_right, hpR] at hlo
    have hhi := canonical_right_wall hφ0.le hK ⟨le_rfl, by linarith⟩
    rw [show φ + π = π + φ by ring] at hlo
    linarith
  have hL : supp K (π / 2 + (π / 2 - φ)) +
      supp (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) = 1 := by
    have hlo := dot_le_supp hD.2.1 hqD (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = ((π / 2 - φ) + π / 2) + π by ring,
      uvec_add_pi, dot_neg_right, uvec_add_pi_div_two, hqL] at hlo
    have hhi := canonical_left_wall hφ0.le hK ⟨by linarith, le_rfl⟩
    have ea : π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 := by ring
    have eb : ((π / 2 - φ) + π / 2) + π = 3 * π / 2 + (π / 2 - φ) := by ring
    rw [eb] at hlo
    rw [ea] at hhi ⊢
    linarith
  have hB0 := opt_supp_three_pi_div_two_eq_zero hK hB inter_subset_left
    (opt_rightBody_A_mem hφ0.le hK)
  have hD0 := opt_supp_three_pi_div_two_eq_zero hK hD inter_subset_left
    (opt_leftBody_C_mem hφ0.le hK)
  refine ⟨hK, hB, hD, inter_subset_left, inter_subset_left,
    fun t ht => canonical_right_wall hφ0.le hK ht, hR, ?_,
    fun t ht => canonical_left_wall hφ0.le hK ht, ?_, hL⟩
  · rw [show π + π / 2 = 3 * π / 2 by ring, hB0, hK.2.2.2.1]
    norm_num
  · rw [add_zero, add_zero, hD0, hK.2.2.2.1]
    norm_num

/-- An open neighborhood of Gerver has feasible canonical triples on the nonsmooth domain. -/
theorem nearby_canonical_inWideL {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) := by
  sorry

/-- Package the canonical bodies without introducing a choice of auxiliary solver output. -/
def canonicalWideTriple {φ : ℝ} {K : Set Point}
    (h : InWideL φ K (rightBody φ K) (leftBody φ K)) : WideTriple φ :=
  ⟨(⟨K, h.1.2.1⟩, ⟨rightBody φ K, h.2.1⟩, ⟨leftBody φ K, h.2.2.1⟩), h⟩

end MovingSofaStability
