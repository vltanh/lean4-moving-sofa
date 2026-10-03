module

public import MovingSofaUniquenessFC.ReferenceDifferential

/-!
# Analytic localization of the reference roots

Every solution on the full upstream domain has `0 < phi < 1/20`. The proof
combines the global `phi < 1/2` exclusion, the explicit phi derivative, and a
single vertical comparison at phi = 1/20. All scalar estimates are displayed
as real inequalities proved from elementary sine/cosine bounds.

No recursively evaluated interval certificate or decision tactic is involved.
Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real

namespace MovingSofaUniquenessFC.Reference

theorem cut_trig :
    (499 / 10000 : ℝ) ≤ sin (1 / 20) ∧ sin (1 / 20) ≤ 1 / 20 ∧
      (499 / 500 : ℝ) ≤ cos (1 / 20) ∧ cos (1 / 20) ≤ 1 := by
  have hs := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hc := one_sub_sq_div_two_le_cos (x := (1 / 20 : ℝ))
  refine ⟨by linarith, sin_le (by norm_num), by linarith, cos_le_one _⟩

theorem cut_frame_bounds {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    (9 / 10 : ℝ) ≤ frameDen (1 / 20) θ ∧
      frameOffset (1 / 20) θ ≤ 151 / 1000 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  have hs0 : 0 ≤ sin (1 / 20 : ℝ) := by linarith
  have hd0 : 0 ≤ gap (1 / 20) θ := by unfold gap; linarith
  have hd1 : gap (1 / 20) θ ≤ 3 / 4 := by unfold gap; linarith [pi_lt_d2]
  have hk0 : 0 ≤ slope (1 / 20) θ := by unfold slope; linarith
  have hk1 : slope (1 / 20) θ ≤ 11 / 8 := by unfold slope gap at *; linarith
  have hoff : offset (1 / 20) θ ≤ 2 := by
    unfold offset
    have hsq : (θ - 1 / 20) ^ 2 ≤ 2 * (θ - 1 / 20) := by
      change 0 ≤ θ - 1 / 20 at hd0
      change θ - 1 / 20 ≤ 3 / 4 at hd1
      nlinarith
    linarith [pi_lt_four]
  have hp := mul_le_mul hk1 hshi hs0 (by norm_num : (0 : ℝ) ≤ 11 / 8)
  have hz : sin (1 / 20) * (1 + offset (1 / 20) θ) ≤ (1 / 20) * 3 := by
    apply mul_le_mul hshi (by linarith)
    · exact add_nonneg zero_le_one (offset_nonneg (by norm_num) hl hu)
    · norm_num
  constructor
  · unfold frameDen
    linarith
  · unfold frameOffset
    linarith

theorem qTheta_cut_pos {θ : ℝ} (hl : (1 / 20 : ℝ) ≤ θ) (hu : θ ≤ π / 4) :
    0 < qTheta (1 / 20) θ := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  obtain ⟨hJ, hZ⟩ := cut_frame_bounds hl hu
  have ht0 : 0 ≤ θ := by linarith
  have hsθ : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos])
  have hd0 : 0 ≤ gap (1 / 20) θ := by unfold gap; linarith
  have hd1 : gap (1 / 20) θ ≤ 3 / 4 := by unfold gap; linarith [pi_lt_d2]
  have hUprod : (1 / 4 : ℝ) * (9 / 10) ≤
      (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ := by
    apply mul_le_mul (by linarith) hJ (by norm_num)
    linarith
  have hU : 0 < (1 - gap (1 / 20) θ) * frameDen (1 / 20) θ -
      frameOffset (1 / 20) θ := by linarith
  have hC : 0 < 3 * (1 - gap (1 / 20) θ) * cos (1 / 20) -
      3 * sin (1 / 20) + sin θ - 1 := by
    by_cases ht : θ ≤ 1 / 2
    · have hd : gap (1 / 20) θ ≤ 9 / 20 := by unfold gap; linarith
      have hm : (11 / 20 : ℝ) * (499 / 500) ≤
          (1 - gap (1 / 20) θ) * cos (1 / 20) := by
        apply mul_le_mul (by linarith) hclo (by norm_num)
        linarith
      nlinarith
    · have htHalf : (1 / 2 : ℝ) ≤ θ := le_of_lt (lt_of_not_ge ht)
      have hsHalf : (23 / 48 : ℝ) ≤ sin (1 / 2) := by
        have h := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith
      have hsOrder := sin_le_sin_of_le_of_le_pi_div_two
        (x := (1 / 2 : ℝ)) (y := θ) (by linarith [pi_pos])
        (by linarith [pi_pos]) htHalf
      have hm : (1 / 4 : ℝ) * (499 / 500) ≤
          (1 - gap (1 / 20) θ) * cos (1 / 20) := by
        apply mul_le_mul (by linarith) hclo (by norm_num)
        linarith
      nlinarith
  have hfirst := mul_nonneg hU.le hsθ
  have hsecond : 0 <
      (3 * (1 - gap (1 / 20) θ) * cos (1 / 20) - 3 * sin (1 / 20) + sin θ - 1) *
        sin (1 / 20) := mul_pos hC (by linarith)
  unfold qTheta
  linarith

/-- A single exact boundary sign, using loose rational trigonometric bounds. -/
theorem reducedQ_cut_boundary_neg : reducedQ (1 / 20) (π / 4) < 0 := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ := cut_trig
  have hπlo : (314 / 100 : ℝ) < π := by linarith [pi_gt_d20]
  have hπhi : π < (3144 / 1000 : ℝ) := by linarith [pi_lt_d20]
  have hdlo : (147 / 200 : ℝ) ≤ gap (1 / 20) (π / 4) := by unfold gap; linarith
  have hdhi : gap (1 / 20) (π / 4) ≤ 92 / 125 := by unfold gap; linarith
  have hu : (707 / 1000 : ℝ) ≤ cos (π / 4) ∧ cos (π / 4) ≤ 708 / 1000 := by
    rw [cos_pi_div_four]
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt0 := sqrt_nonneg (2 : ℝ)
    constructor <;> nlinarith
  have heq : sin (π / 4) = cos (π / 4) := by rw [sin_pi_div_four, cos_pi_div_four]
  have hN : num (1 / 20) (π / 4) ≤ 257 / 1000 := by
    have hm : (2 - (92 / 125 : ℝ)) * (707 / 1000) ≤
        (2 - gap (1 / 20) (π / 4)) * cos (π / 4) := by
      apply mul_le_mul (by linarith) hu.1 (by norm_num)
      linarith
    unfold num
    rw [heq]
    unfold gap at hm
    nlinarith
  have hD : (2286 / 1000 : ℝ) ≤ den (1 / 20) (π / 4) := by
    unfold den
    linarith [hu.2]
  have hJ0 := (cut_frame_bounds (θ := π / 4) (by linarith) le_rfl).1
  have hJ : frameDen (1 / 20) (π / 4) ≤ 932 / 1000 := by
    have hk : (1 + (147 / 200 : ℝ) / 2) ≤ slope (1 / 20) (π / 4) := by
      unfold slope gap at *
      linarith
    have hm := mul_le_mul hk hslo (by norm_num : (0 : ℝ) ≤ 499 / 10000)
      (by unfold slope; linarith : 0 ≤ slope (1 / 20) (π / 4))
    unfold frameDen
    nlinarith
  have hoff : (1237 / 1000 : ℝ) ≤ offset (1 / 20) (π / 4) := by
    have he : offset (1 / 20) (π / 4) =
        3 * gap (1 / 20) (π / 4) / 2 + gap (1 / 20) (π / 4) ^ 2 / 4 := by
      unfold offset gap
      ring
    rw [he]
    nlinarith
  have hZ : (111 / 1000 : ℝ) ≤ frameOffset (1 / 20) (π / 4) := by
    have hm : (499 / 10000 : ℝ) * (1 + 1237 / 1000) ≤
        sin (1 / 20) * (1 + offset (1 / 20) (π / 4)) := by
      apply mul_le_mul hslo (by linarith) (by norm_num)
      linarith
    unfold frameOffset
    linarith
  have hNJ : num (1 / 20) (π / 4) * frameDen (1 / 20) (π / 4) ≤
      (257 / 1000 : ℝ) * (932 / 1000) := by
    calc
      _ ≤ (257 / 1000) * frameDen (1 / 20) (π / 4) :=
        mul_le_mul_of_nonneg_right hN (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by norm_num)
  have hDZ : (2286 / 1000 : ℝ) * (111 / 1000) ≤
      den (1 / 20) (π / 4) * frameOffset (1 / 20) (π / 4) := by
    apply mul_le_mul hD hZ (by norm_num)
    linarith
  rw [reducedQ_frame]
  linarith

/-- Every root in the original full domain has a small first angle. -/
theorem Spec.phi_lt_twentieth {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < 1 / 20 := by
  by_contra hlarge
  have hl : (1 / 20 : ℝ) ≤ φ := le_of_not_gt hlarge
  have hhalf := h.phi_lt_half
  have horder := h.phi_lt_theta
  have hθ := h.2.2.1
  have hanti : AntitoneOn (fun p => reducedQ p θ) (Icc (1 / 20) φ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun p _ => (reducedQ_phi_deriv p θ).continuousAt.continuousWithinAt
    · exact fun p _ => (reducedQ_phi_deriv p θ).differentiableAt.differentiableWithinAt
    · intro p hp
      rw [interior_Icc] at hp
      rw [(reducedQ_phi_deriv p θ).deriv]
      exact (qPhi_neg (by linarith [hp.1]) (by linarith [hp.2])
        (hp.2.trans horder) hθ).le
  have hmono : MonotoneOn (reducedQ (1 / 20)) (Icc (1 / 20) (π / 4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ => (reducedQ_theta_deriv (1 / 20) t).continuousAt.continuousWithinAt
    · exact fun t _ => (reducedQ_theta_deriv (1 / 20) t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(reducedQ_theta_deriv (1 / 20) t).deriv]
      exact (qTheta_cut_pos ht.1.le ht.2.le).le
  have hfirst := hanti ⟨le_rfl, hl⟩ ⟨hl, le_rfl⟩ hl
  have hsecond := hmono ⟨hl.trans horder.le, hθ⟩
    ⟨hl.trans (horder.le.trans hθ), le_rfl⟩ hθ
  have hzero := h.reduced_zero.1
  linarith [reducedQ_cut_boundary_neg]

end MovingSofaUniquenessFC.Reference
