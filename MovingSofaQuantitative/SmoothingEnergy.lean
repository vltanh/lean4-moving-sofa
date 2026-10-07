module

public import MovingSofaQuantitative.SmoothingError

/-!
# Quantitative convergence of the actual smoothed cap energy

Uncompiled proof source. The error has two short middle-arc pieces and one
short last-arc piece. Each has a uniform residual bound. The comparison pairing
cancels the cross term exactly, leaving an O(eta) energy excess.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative.OneSidedSmoothing

variable {φ η : ℝ}

theorem patch_zero_off {t : ℝ} (ht : t ∉ Ico φ (φ + η)) : patch φ η t = 0 := by
  unfold patch rightJoin
  split_ifs <;> first | rfl | (exfalso; exact ht ⟨by linarith, by assumption⟩)

theorem patchFirst_zero_off {t : ℝ} (ht : t ∉ Ico φ (φ + η)) : patchFirst φ η t = 0 := by
  unfold patchFirst rightJoin
  split_ifs <;> first | rfl | (exfalso; exact ht ⟨by linarith, by assumption⟩)

theorem patchFirstLeft_zero_off {t : ℝ} (ht : t ∉ Ioc φ (φ + η)) :
    patchFirstLeft φ η t = 0 := by
  unfold patchFirstLeft leftJoin
  split_ifs <;> first | rfl | (exfalso; exact ht ⟨by linarith, by assumption⟩)

theorem symmetricPatch_endpoints (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) :
    symmetricPatch φ η (π / 2) = 0 ∧ symmetricPatch φ η (π - φ) = 0 ∧
      symmetricPatch φ η π = 0 := by
  have hφv : φ < π / 2 := by linarith [hφ.2, pi_pos]
  have hv : φ + η < π / 2 := by linarith [hsep, hφ.1]
  have hTv : π / 2 < π - φ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp [symmetricPatch, patch, rightJoin, not_lt.mpr hφv.le, not_lt.mpr hv.le]
  · simp [symmetricPatch, not_le.mpr hTv, patch, rightJoin, bump,
      show φ < φ + η by linarith]
  · simp [symmetricPatch, not_le.mpr (show π / 2 < π by linarith [pi_pos]),
      patch, rightJoin, hφ.1]

theorem symmetricPatch_left_zero (hφ : φ ∈ Ioo 0 (π / 4))
    {t : ℝ} (ht : t < φ) :
    symmetricPatch φ η t = 0 ∧ symmetricPatchDerivative φ η t = 0 := by
  have htv : t < π / 2 := by linarith [ht, hφ.2, pi_pos]
  simp [symmetricPatch, symmetricPatchDerivative, patch, patchFirst, rightJoin, ht, htv.le, htv]

theorem symmetricPatch_central_zero (hφ : φ ∈ Ioo 0 (π / 4)) (hη : 0 < η)
    (hsep : φ + η < π / 2 - φ) {t : ℝ}
    (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    symmetricPatch φ η t = 0 ∧ symmetricPatchDerivative φ η t = 0 := by
  have hφt : φ < t := by linarith [ht.1, hφ.2]
  have hηt : φ + η < t := hsep.trans_le ht.1
  refine ⟨?_, ?_⟩
  · simp [symmetricPatch, if_pos ht.2, patch, rightJoin, not_lt.mpr hφt.le, not_lt.mpr hηt.le]
  · rcases ht.2.lt_or_eq with h | rfl
    · simp [symmetricPatchDerivative, rightJoin, h, patchFirst,
        not_lt.mpr hφt.le, not_lt.mpr hηt.le]
    · have he : π - π / 2 = π / 2 := by ring
      simp [symmetricPatchDerivative, rightJoin, he, patchFirstLeft, leftJoin,
        not_le.mpr hφt, not_le.mpr hηt]

theorem symmetricPatch_last_zero (hφ : φ ∈ Ioo 0 (π / 4)) {t : ℝ}
    (ht : π / 2 < t) (hout : t < π - φ - η ∨ π - φ < t) :
    symmetricPatch φ η t = 0 ∧ symmetricPatchDerivative φ η t = 0 := by
  have h1 : π - t ∉ Ico φ (φ + η) := by
    intro hu
    rcases hout with h | h <;> linarith [hu.1, hu.2]
  have h2 : π - t ∉ Ioc φ (φ + η) := by
    intro hu
    rcases hout with h | h <;> linarith [hu.1, hu.2]
  simp only [symmetricPatch, if_neg (not_le.mpr ht), symmetricPatchDerivative,
    rightJoin, if_neg (not_lt.mpr ht.le), patch_zero_off h1,
    patchFirstLeft_zero_off h2, neg_zero]

/-- The full residual error is bounded by 216 J(phi)^2 eta. -/
theorem energy_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hηsin : η ≤ sin P.φ)
    (hsep : P.φ + 2 * η < π / 2 - P.φ) :
    fourResidualEnergy P.φ
      (profile (GerverParams.gm_φ_mem_Ioo hP hbox) hη
        (show P.φ + η < π / 2 - P.φ by linarith)).pinnedProfile
      (profile (GerverParams.gm_φ_mem_Ioo hP hbox) hη
        (show P.φ + η < π / 2 - P.φ by linarith)).pinnedProfileDerivative ≤
      (A P.φ)^2 + 216 * (J P.φ)^2 * η := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hsep' : P.φ + η < π / 2 - P.φ := by linarith
  let F := profile hφ hη hsep'
  let f := fun t => F.pinnedProfile t + comparisonProfile P.φ t
  let df := fun t => F.pinnedProfileDerivative t + comparisonDerivative P.φ t
  have hF := halfCapProfile_data hP hbox F
  have hdata : FourResidualData P.φ f df := by
    simpa only [sub_neg_eq_add, neg_one_mul] using
      fourResidualData_sub_smul hφ hF (comparisonProfile_data hφ) (-1)
  have hv : ∀ t ∈ Icc (0 : ℝ) π, f t = symmetricPatch P.φ η t :=
    fun t ht => error_value hφ hη hsep' ht
  have hd : ∀ t ∈ Ioo (0 : ℝ) π, df t = symmetricPatchDerivative P.φ η t :=
    fun t ht => error_derivative hP hbox hη hsep' ht
  have hJ := J_nonneg hφ
  have hsin : 0 < sin P.φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, pi_pos])
  have hfv : f (π / 2) = 0 := hdata.top_zero
  have hfT : f (π - P.φ) = 0 := by
    rw [hv _ ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩]
    exact (symmetricPatch_endpoints hφ hη hsep').2.1
  have h1zero : ∀ t ∈ Ioo (0 : ℝ) P.φ, tangentResidual (π / 2) f df t = 0 := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨ht.1, by linarith [ht.2, hφ.2, pi_pos]⟩
    have hz := symmetricPatch_left_zero (η := η) hφ ht.2
    simp only [tangentResidual, hfv, hv t (Ioo_subset_Icc_self ht'), hd t ht', hz.1, hz.2,
      zero_mul, sub_zero, zero_div]
  have h3zero : ∀ t ∈ Ioo (π / 2 - P.φ) (π / 2), tangentResidual (π - P.φ) f df t = 0 := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨by linarith [ht.1, hφ.2, pi_pos], by linarith [ht.2, pi_pos]⟩
    have hz := symmetricPatch_central_zero hφ hη hsep' (Ioo_subset_Icc_self ht)
    simp only [tangentResidual, hfT, hv t (Ioo_subset_Icc_self ht'), hd t ht', hz.1, hz.2,
      zero_mul, sub_zero, zero_div]
  have h2bound : ∀ t ∈ Icc P.φ (π / 2 - P.φ), |cornerResidual f df t| ≤ 12 * J P.φ := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨hφ.1.trans_le ht.1, by linarith [ht.2, hφ.1, pi_pos]⟩
    rw [cornerResidual, hv (t + π / 2) ⟨by linarith [ht.1, hφ.1, pi_pos], by linarith [ht.2, hφ.1]⟩,
      hd t ht']
    have hb := (abs_sub _ _).trans (add_le_add
      (symmetricPatch_bounds hφ hη (t + π / 2)).1
      (symmetricPatch_bounds hφ hη t).2)
    have hm := mul_le_mul_of_nonneg_left hη1 (by positivity : 0 ≤ 4 * J P.φ)
    linarith
  have h2gap : ∀ t ∈ Ioo (P.φ + η) (π / 2 - P.φ - η), cornerResidual f df t = 0 := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1, pi_pos]⟩
    rw [cornerResidual, hv (t + π / 2) ⟨by linarith [ht'.1, pi_pos], by linarith [ht.2, hφ.1]⟩,
      hd t ht']
    have htlow : t < π / 2 := by linarith [ht.2, hφ.1]
    have htplus : π / 2 < t + π / 2 := by linarith [ht'.1]
    have harg : π - (t + π / 2) ∉ Ico P.φ (P.φ + η) := by
      intro hu
      linarith [ht.2, hu.2]
    have hself : t ∉ Ico P.φ (P.φ + η) := by intro hu; linarith [ht.1, hu.2]
    simp only [symmetricPatch, if_neg (not_le.mpr htplus), patch_zero_off harg,
      symmetricPatchDerivative, rightJoin, if_pos htlow, patchFirst_zero_off hself, sub_self]
  have h4bound : ∀ t ∈ Icc (π - P.φ - η) (π - P.φ), |tangentResidual π f df t| ≤ 12 * J P.φ := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨by linarith [ht.1, hsep', pi_pos], by linarith [ht.2, hφ.1]⟩
    have htv : π / 2 ≤ t := by linarith [ht.1, hsep', hφ.1]
    have hst : sin P.φ ≤ sin t := by
      rw [← sin_pi_sub t]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [hφ.1, pi_pos])
        (by linarith) (by linarith [ht.2])
    have hsp : 0 < sin t := hsin.trans_le hst
    have hb := symmetricPatch_bounds hφ hη t
    have hval : |symmetricPatch P.φ η t| ≤ 4 * J P.φ * sin t := by
      have hm := mul_le_mul_of_nonneg_left (hηsin.trans hst) (by positivity : 0 ≤ 4 * J P.φ)
      exact hb.1.trans hm
    have hcot : |(cos t / sin t) * symmetricPatch P.φ η t| ≤ 4 * J P.φ := by
      rw [abs_mul, abs_div, abs_of_pos hsp]
      have hm := mul_le_mul_of_nonneg_left hval (div_nonneg (abs_nonneg _) hsp.le)
      have he : |cos t| / sin t * (4 * J P.φ * sin t) = 4 * J P.φ * |cos t| := by
        field_simp [hsp.ne']
        ring
      rw [he] at hm
      exact hm.trans (mul_le_of_le_one_right (by positivity) (abs_cos_le_one t))
    rw [tangentResidual_left hdata.left_zero, hv t (Ioo_subset_Icc_self ht'), hd t ht']
    exact (abs_sub _ _).trans ((add_le_add hcot hb.2).trans_eq (by ring))
  have h4zero : ∀ t ∈ Ioo (π / 2) π,
      (t < π - P.φ - η ∨ π - P.φ < t) → tangentResidual π f df t = 0 := by
    intro t ht hout
    have ht' : t ∈ Ioo (0 : ℝ) π := ⟨by linarith [ht.1, pi_pos], ht.2⟩
    have hz := symmetricPatch_last_zero (η := η) hφ ht.1 hout
    rw [tangentResidual_left hdata.left_zero, hv t (Ioo_subset_Icc_self ht'), hd t ht', hz.1, hz.2]
    ring
  have h2 := arcSquare_two_ends (a := P.φ) (b := π / 2 - P.φ)
    (c := P.φ + η) (d := π / 2 - P.φ - η) (B := 12 * J P.φ)
    (by linarith) (by linarith) (by linarith) hdata.middle_sq h2gap h2bound
  have h4 := arcSquare_localized (a := π / 2) (b := π)
    (c := π - P.φ - η) (d := π - P.φ) (B := 12 * J P.φ)
    (by linarith [hsep', hφ.1]) (by linarith) (by linarith [hφ.1]) hdata.last_sq
    (fun t ht => h4zero t ⟨ht.1, by linarith [ht.2, hφ.1]⟩ (Or.inl ht.2))
    (fun t ht => h4zero t ⟨by linarith [ht.1, hφ.2, pi_pos], ht.2⟩ (Or.inr ht.1)) h4bound
  have hE : fourResidualEnergy P.φ f df ≤ 216 * (J P.φ)^2 * η := by
    unfold fourResidualEnergy
    rw [arcSquare_eq_zero_of_zero_on hφ.1.le h1zero,
      arcSquare_eq_zero_of_zero_on (by linarith [hφ.1]) h3zero]
    nlinarith only [h2, h4]
  have hzero : F.pinnedProfile 0 = -2 * (1 / cos P.φ)^2 := by
    simp only [HalfCapProfile.pinnedProfile, pinnedDifference, cos_zero, mul_one,
      F.symmetricValue_zero, F.symmetricValue_pi]
    rw [profile_zero hφ hη hsep']
    unfold A
    ring
  have he := comparison_energy_excess hφ hF hzero
  change fourResidualEnergy P.φ F.pinnedProfile F.pinnedProfileDerivative ≤ _
  rw [he]
  exact add_le_add_left hE _

end MovingSofaQuantitative.OneSidedSmoothing
