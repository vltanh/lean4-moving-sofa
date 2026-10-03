module

public import MovingSofaUniquenessFC.ReferenceBoundary

/-!
# Elementary bounds on the full reference parameter domain

The first localization step uses the original equations and nonnegativity,
not a checked list of excluded boxes. In particular every reference solution
has `phi < 1/2`. This keeps the later derivative comparison away from the
ill-conditioned corner `phi = theta = pi/4`.

Uncompiled source. No numerical certificate evaluation is used.
-/

@[expose] public section
noncomputable section

open Set Real

namespace MovingSofaUniquenessFC.Reference

/-- Common trigonometric order on the closed angle triangle. -/
theorem triangle_trig {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) :
    0 ≤ sin φ ∧ sin φ ≤ cos φ ∧ 0 < cos φ ∧ cos θ ≤ cos φ ∧
      0 ≤ sin θ ∧ 0 < cos θ ∧ 1 ≤ cos θ + sin θ := by
  have hθ0 := hφ.trans horder
  have hpL : φ ≤ π / 2 := by linarith [pi_pos]
  have htL : θ ≤ π / 2 := by linarith [pi_pos]
  have hpSin := sin_nonneg_of_nonneg_of_le_pi hφ (by linarith [pi_pos])
  have htSin := sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos])
  have hpCos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (x := φ)
  have htCos := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (x := θ)
  have hpc : sin φ ≤ cos φ := by
    have h := sin_le_sin_of_le_of_le_pi_div_two
      (x := φ) (y := π / 2 - φ) (by linarith [pi_pos])
      (by linarith) (by linarith)
    simpa only [sin_pi_div_two_sub] using h
  have hcOrder := cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_pos]) horder
  have hsum : 1 ≤ cos θ + sin θ := by
    have hsq := sin_sq_add_cos_sq θ
    have hmul : 0 ≤ sin θ * cos θ := mul_nonneg htSin htCos.le
    nlinarith
  exact ⟨hpSin, hpc, hpCos, hcOrder, htSin, htCos, hsum⟩

theorem offset_nonneg {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) : 0 ≤ offset φ θ := by
  unfold offset
  have hδ : 0 ≤ θ - φ := sub_nonneg.mpr horder
  nlinarith [sq_nonneg (θ - φ)]

/-- The fourth equation and the domain imply B >= A. -/
theorem Spec.A_le_B {A B φ θ : ℝ} (h : Spec A B φ θ) : A ≤ B := by
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  have hoff := offset_nonneg hp ho ht
  have he := eliminate_eq4 A B φ θ
  rw [h4] at he
  have hslope : 1 ≤ slope φ θ := by unfold slope; linarith
  have hm := mul_le_mul_of_nonneg_left hslope hA
  linarith

/-- A useful inequality with no trigonometric division. -/
theorem Spec.angle_inequality {A B φ θ : ℝ} (h : Spec A B φ θ) :
    3 * sin φ ^ 2 - cos φ * sin φ ≤ (θ - φ) * (cos φ - sin φ) := by
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hp ho ht
  have hab := h.A_le_B
  have hcs : 0 ≤ cos φ - sin φ := sub_nonneg.mpr hsc
  have hbase : sin φ ≤ A * (cos φ - sin φ) := by
    have hAB := mul_le_mul_of_nonneg_right hab hs
    unfold eq3 at h3
    nlinarith [cos_le_one φ]
  have hid := eliminate_B A B φ θ
  rw [h1, h3] at hid
  have hsmall : 2 * A * cos φ ≤ θ - φ + 3 * sin φ := by
    have hm := mul_le_mul_of_nonneg_left hcc hA
    have hd : (θ - φ) * cos θ ≤ θ - φ := by
      simpa using mul_le_mul_of_nonneg_left (cos_le_one θ) (sub_nonneg.mpr ho)
    unfold num den at hid
    nlinarith
  have hleft := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2 * cos φ by positivity)
  have hright := mul_le_mul_of_nonneg_right hsmall hcs
  nlinarith

/-- Global, analytic exclusion of phi >= 1/2. -/
theorem Spec.phi_lt_half {A B φ θ : ℝ} (h : Spec A B φ θ) : φ < 1 / 2 := by
  by_contra hlarge
  have hφlo : (1 / 2 : ℝ) ≤ φ := le_of_not_gt hlarge
  obtain ⟨hp, ho, ht, hA, hB, h1, h2, h3, h4⟩ := spec_iff.mp h
  obtain ⟨hs, hsc, hc, hcc, hts, htc, hsum⟩ := triangle_trig hp ho ht
  have hπ : π < (16 / 5 : ℝ) := by linarith [pi_lt_d2]
  have hδ : θ - φ ≤ 3 / 10 := by linarith
  have hsinHalf : (23 / 48 : ℝ) ≤ sin (1 / 2) := by
    have h := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at h ⊢
    linarith
  have hsinOrder := sin_le_sin_of_le_of_le_pi_div_two
    (x := (1 / 2 : ℝ)) (y := φ) (by linarith [pi_pos])
    (by linarith [pi_pos]) hφlo
  have hslo : (23 / 48 : ℝ) ≤ sin φ := hsinHalf.trans hsinOrder
  have hprod : (θ - φ) * (cos φ - sin φ) ≤ (3 / 10) * (1 - sin φ) := by
    apply mul_le_mul hδ (sub_le_sub_right (cos_le_one φ) _)
    · exact sub_nonneg.mpr hsc
    · norm_num
  have hmul := mul_le_mul_of_nonneg_right (cos_le_one φ) hs
  have hin := h.angle_inequality
  nlinarith [sq_nonneg (sin φ - 23 / 48)]

end MovingSofaUniquenessFC.Reference
