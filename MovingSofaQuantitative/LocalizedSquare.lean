module

public import MovingSofaQuantitative.PerturbationEnergy

/-!
# Square integrals on shrinking support intervals

Uncompiled proof source. Integral identities use actual integrability and
ignore only finitely many endpoint values. These estimates replace an informal
dominated-convergence assertion in the cap-sharpness construction.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaStability

namespace MovingSofaQuantitative

theorem arcSquare_eq_zero_of_zero_on {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ∀ t ∈ Ioo a b, f t = 0) : arcSquare a b f = 0 := by
  unfold arcSquare
  rw [intervalIntegral_eq_of_eqOn_Ioo hab (g := fun _ => (0 : ℝ))
    (fun t ht => by rw [hf t ht]; ring)]
  simp

theorem arcSquare_le_length_mul {a b B : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hbound : ∀ t ∈ Icc a b, |f t| ≤ B) : arcSquare a b f ≤ (b - a) * B ^ 2 := by
  have hm := intervalIntegral.integral_mono_on hab hi
    (intervalIntegrable_const (c := B ^ 2)) (fun t ht => by
      have hb := hbound t ht
      nlinarith [sq_abs (f t), abs_nonneg (f t)])
  simpa only [arcSquare, intervalIntegral.integral_const, smul_eq_mul] using hm

/-- Only the middle interval contributes. The function is still the original
function; it is not replaced by a sampled or stepwise approximation. -/
theorem arcSquare_localized {a b c d B : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) {f : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hleft : ∀ t ∈ Ioo a c, f t = 0)
    (hright : ∀ t ∈ Ioo d b, f t = 0)
    (hbound : ∀ t ∈ Icc c d, |f t| ≤ B) :
    arcSquare a b f ≤ (d - c) * B ^ 2 := by
  have iac := intervalIntegrable_subinterval hi le_rfl hac (hcd.trans hdb)
  have icd := intervalIntegrable_subinterval hi hac hcd hdb
  have idb := intervalIntegrable_subinterval hi (hac.trans hcd) hdb le_rfl
  have hsplit : arcSquare a b f = arcSquare a c f + arcSquare c d f + arcSquare d b f := by
    unfold arcSquare
    rw [intervalIntegral.integral_add_adjacent_intervals iac icd,
      intervalIntegral.integral_add_adjacent_intervals (iac.trans icd) idb]
  rw [hsplit, arcSquare_eq_zero_of_zero_on hac hleft,
    arcSquare_eq_zero_of_zero_on hdb hright, zero_add, add_zero]
  exact arcSquare_le_length_mul hcd icd hbound

/-- Two end intervals contribute, while the open gap contributes zero. -/
theorem arcSquare_two_ends {a b c d B : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) {f : ℝ → ℝ}
    (hi : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hgap : ∀ t ∈ Ioo c d, f t = 0)
    (hbound : ∀ t ∈ Icc a b, |f t| ≤ B) :
    arcSquare a b f ≤ ((c - a) + (b - d)) * B ^ 2 := by
  have iac := intervalIntegrable_subinterval hi le_rfl hac (hcd.trans hdb)
  have icd := intervalIntegrable_subinterval hi hac hcd hdb
  have idb := intervalIntegrable_subinterval hi (hac.trans hcd) hdb le_rfl
  have hsplit : arcSquare a b f = arcSquare a c f + arcSquare c d f + arcSquare d b f := by
    unfold arcSquare
    rw [intervalIntegral.integral_add_adjacent_intervals iac icd,
      intervalIntegral.integral_add_adjacent_intervals (iac.trans icd) idb]
  have hl := arcSquare_le_length_mul hac iac (fun t ht => hbound t ⟨ht.1, ht.2.trans (hcd.trans hdb)⟩)
  have hr := arcSquare_le_length_mul hdb idb (fun t ht => hbound t ⟨(hac.trans hcd).trans ht.1, ht.2⟩)
  rw [hsplit, arcSquare_eq_zero_of_zero_on hcd hgap]
  nlinarith only [hl, hr]

/-- If endpoint pairing with the comparison profile is unchanged, the excess
energy is exactly the energy of the added localized error. -/
theorem comparison_energy_excess {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {f df : ℝ → ℝ} (hf : FourResidualData φ f df)
    (hzero : f 0 = -2 * (1 / cos φ) ^ 2) :
    fourResidualEnergy φ f df = (1 / cos φ) ^ 2 +
      fourResidualEnergy φ (fun t => f t + comparisonProfile φ t)
        (fun t => df t + comparisonDerivative φ t) := by
  have he := fourResidualEnergy_sub_smul hφ hf (comparisonProfile_data hφ) (-1)
  rw [residualPair_comparison hφ hf, hzero, comparisonProfile_energy hφ] at he
  simp only [neg_one_mul, sub_neg_eq_add, neg_one_sq, one_mul] at he
  linarith

/-- A purely scalar strict margin: a positive excess tending to zero does not
consume the fixed gap between C and the sharp residual coefficient A. -/
theorem exists_small_energy_error {A C D η₀ : ℝ}
    (hA : 0 < A) (hC : C < A) (hD : 0 ≤ D) (hη₀ : 0 < η₀) :
    ∃ η : ℝ, 0 < η ∧ η < η₀ ∧ C * sqrt (A ^ 2 + D * η) < A ^ 2 := by
  have hc : Continuous (fun η : ℝ => C * sqrt (A ^ 2 + D * η)) := by fun_prop
  have hbase : C * sqrt (A ^ 2 + D * (0 : ℝ)) < A ^ 2 := by
    rw [mul_zero, add_zero, sqrt_sq hA.le]
    nlinarith only [mul_lt_mul_of_pos_right hC hA]
  have hn := (isOpen_lt hc continuous_const).mem_nhds hbase
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let η := min r η₀ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr : η < r := by dsimp [η]; linarith [min_le_left r η₀, lt_min hr hη₀]
  have hηsmall : η < η₀ := by dsimp [η]; linarith [min_le_right r η₀, lt_min hr hη₀]
  exact ⟨η, hη, hηsmall, hball (by simpa only [Metric.mem_ball, Real.dist_eq,
    sub_zero, abs_of_pos hη] using hηr)⟩

end MovingSofaQuantitative
