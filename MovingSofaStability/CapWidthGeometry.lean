module

public import MovingSofaStability.NicheContainment

/-!
# Cut geometry from a lower bound on bottom width

Uncompiled proof source. A width of 21/10 suffices for the fixed small cut
angles. This avoids assuming area continuity, curvature regularity, or Ki
membership of the competing cap when locating its cut feet.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def bottomWidth (K : Set Point) : ℝ := supp K 0 + supp K π

theorem area_le_bottomWidth {K : Set Point} (hK : IsCap K (π / 2)) : area K ≤ bottomWidth K := by
  have h := opt_area_le_of_fst_bounds hK (fun p hp => opt_cap_fst_le hK hp)
  simpa only [bottomWidth, sub_neg_eq_add, add_comm] using h

/-- Gerver's cap has enough bottom width even after a fixed support perturbation. -/
theorem nearby_bottomWidth {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hclose : UpperSupportClose (1 / 20) K P.cap) :
    (21 / 10 : ℝ) ≤ bottomWidth K := by
  have hKi := theorem8_1_1_gerver hP hbox
  have hw := area_le_bottomWidth hKi.1
  have ha := hKi.2.2
  have h0 := (abs_le.mp (hclose 0 ⟨le_rfl, pi_pos.le⟩)).1
  have hπ := (abs_le.mp (hclose π ⟨pi_pos.le, le_rfl⟩)).1
  unfold bottomWidth at *
  linarith

/-- Both cut feet lie on the bottom face, strictly between its endpoints. -/
theorem cut_feet_mem_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    wRight φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} ∧
      zLeft φ K ∈ edge K (3 * π / 2) \ {aK K 0, cK K (π / 2)} := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hpi := pi_pos
  have hφ' : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hψ' : π / 2 - φ ∈ Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hW : (21 / 10 : ℝ) * cos φ > 1 := by linarith
  have hwidthmul : 1 < bottomWidth K * cos φ :=
    hW.trans_le (mul_le_mul_of_nonneg_right hwidth hc.le)
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  unfold bottomWidth at hwidthmul
  constructor
  · rw [opt_wRight_eq]
    apply opt_mem_bottom_edge hK
    · rw [lt_div_iff₀ hc]
      nlinarith
    · have h := (theorem2_5_5_supp hK hφ').1
      rw [div_lt_iff₀ hc]
      linarith
  · rw [opt_zLeft_eq]
    apply opt_mem_bottom_edge hK
    · have h := (theorem2_5_5_supp hK hψ').2
      rw [show π / 2 - φ + π / 2 = π - φ by ring, add_halves, sub_sub_cancel] at h
      rw [lt_div_iff₀ hc]
      linarith
    · rw [div_lt_iff₀ hc]
      nlinarith

/-- The two cut half-planes do not meet inside a sufficiently wide cap. -/
theorem cut_regions_disjoint_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    Disjoint (K ∩ hRight φ K) (K ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 ≤ cos φ := by linarith
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  have hwidthmul := mul_le_mul_of_nonneg_right hwidth hc
  unfold bottomWidth at hwidthmul
  rw [Set.disjoint_left]
  rintro p ⟨hpK, hpR⟩ ⟨-, hpL⟩
  have hy := hK.snd_le_one hpK
  change supp K φ - 1 ≤ dot p (uvec φ) at hpR
  change supp K (π / 2 - φ + π / 2) - 1 ≤ dot p (uvec (π / 2 - φ + π / 2)) at hpL
  rw [show π / 2 - φ + π / 2 = π - φ by ring] at hpL
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub] at hpR hpL
  have hys := mul_le_mul_of_nonneg_right hy hs0.le
  nlinarith

/-- The feet are ordered from left to right. -/
theorem cut_feet_order_of_width {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K) :
    (zLeft φ K).1 < (wRight φ K).1 := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hA := dot_le_supp hK.2.1.2.1 (opt_cap_A_mem hK) φ
  have hC := dot_le_supp hK.2.1.2.1 (opt_cap_C_mem hK) (π - φ)
  simp only [dot, uvec, cos_pi_sub, sin_pi_sub, zero_mul, add_zero] at hA hC
  have hw := mul_le_mul_of_nonneg_right hwidth hc.le
  unfold bottomWidth at hw
  rw [opt_zLeft_eq, opt_wRight_eq]
  exact (div_lt_div_iff_of_pos_right hc).2 (by nlinarith)

end MovingSofaStability
