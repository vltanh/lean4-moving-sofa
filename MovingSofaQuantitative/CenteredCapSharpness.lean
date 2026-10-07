module

public import MovingSofaQuantitative.SmoothingEnergy
public import MovingSofaQuantitative.CenteredCap

/-!
# Sharpness of centered cap coercivity among actual convex caps

Uncompiled proof source. The family is constructed by positively turning support
curves. A one-sided cubic bump repairs the forbidden negative curvature atoms.
The exact Mamikon energy is identified, and its excess tends to zero by an
explicit O(eta) estimate. Width gives the lower bound against EVERY horizontal
translation. No conclusion is drawn about sharpness for the full Q deficit.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- Equal endpoint perturbations preserve the midpoint of the horizontal
projection. This chosen symmetric family therefore needs no recentering. -/
theorem perturbedCap_midpoint {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) :
    horizontalMidpoint (perturbedCap hP hbox F τ hτ hsmall).1 = horizontalMidpoint P.cap := by
  unfold horizontalMidpoint
  rw [perturbedCap_support hP hbox F τ hτ hsmall ⟨le_rfl, pi_pos.le⟩,
    perturbedCap_support hP hbox F τ hτ hsmall ⟨pi_pos.le, le_rfl⟩,
    F.symmetricValue_zero, F.symmetricValue_pi]
  ring

/-- The endpoint-width obstruction is geometric because the cap quotient is
attained by a Euclidean point-witness bound. -/
theorem perturbedCap_width_lower {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude) :
    τ * |F.value 0| ≤ capTranslationDistance P.cap (perturbedCap hP hbox F τ hτ hsmall).1 := by
  let K := perturbedCap hP hbox F τ hτ hsmall
  have hG := (wideGerverTriple hP hbox).2.1
  have hK := perturbedCap_isCap hP hbox F τ hτ hsmall
  obtain ⟨_, _, a, ha⟩ := capTranslationDistance_formula hG hK
  have hfit := (fitsTranslation_iff_capClose hG hK _).mpr ⟨a, ha⟩
  have hw := endpoint_width_lower hfit
    (i := ⟨0, le_rfl, pi_pos.le⟩) (j := ⟨π, pi_pos.le, le_rfl⟩)
    (by simp [horizontalMode]) (by simp [horizontalMode])
  change |(supp K.1 0 - supp P.cap 0) + (supp K.1 π - supp P.cap π)| / 2 ≤ _ at hw
  rw [perturbedCap_support hP hbox F τ hτ hsmall ⟨le_rfl, pi_pos.le⟩,
    perturbedCap_support hP hbox F τ hτ hsmall ⟨pi_pos.le, le_rfl⟩,
    F.symmetricValue_zero, F.symmetricValue_pi] at hw
  have he : (supp P.cap 0 + τ * F.value 0 - supp P.cap 0) +
      (supp P.cap π + τ * F.value 0 - supp P.cap π) = (2 * τ) * F.value 0 := by ring
  rw [he, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hτ)] at hw
  nlinarith only [hw]

/-- Exact target G.3: for every smaller coefficient and every neighborhood,
a genuine normalized cap violates that coefficient after EVERY horizontal
translation. The amplitude is chosen only after the smoothing width. -/
theorem centered_residual_sharpness : Targets.CenteredResidualSharpness := by
  intro P hP hbox C ε hC hε
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  let A := OneSidedSmoothing.A P.φ
  let J := OneSidedSmoothing.J P.φ
  have hA : 0 < A := OneSidedSmoothing.A_pos hφ
  have hJ : 0 ≤ J := OneSidedSmoothing.J_nonneg hφ
  let C₀ := max C 0
  have hC₀ : C₀ < A := max_lt hC hA
  have hC₀nonneg : 0 ≤ C₀ := le_max_right _ _
  let η₀ := min (1 : ℝ) (min (sin P.φ) ((π / 2 - 2 * P.φ) / 4))
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (lt_min
    (sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, pi_pos])) (by linarith [hφ.2]))
  obtain ⟨η, hη, hηsmall, hstrict⟩ := exists_small_energy_error
    (A := A) (C := C₀) (D := 216 * J ^ 2) hA hC₀ (by positivity) hη₀
  have hη1 : η ≤ 1 := hηsmall.le.trans (min_le_left _ _)
  have hηsin : η ≤ sin P.φ := hηsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηgap : η < (π / 2 - 2 * P.φ) / 4 :=
    hηsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsep2 : P.φ + 2 * η < π / 2 - P.φ := by linarith [hφ.2]
  have hsep : P.φ + η < π / 2 - P.φ := by linarith
  let F := OneSidedSmoothing.profile hφ hη hsep
  let E := fourResidualEnergy P.φ F.pinnedProfile F.pinnedProfileDerivative
  have hF := halfCapProfile_data hP hbox F
  have hF0 : F.value 0 = -A ^ 2 := OneSidedSmoothing.profile_zero hφ hη hsep
  have hf0 : F.pinnedProfile 0 = -2 * (1 / cos P.φ)^2 := by
    simp only [HalfCapProfile.pinnedProfile, pinnedDifference, cos_zero, mul_one,
      F.symmetricValue_zero, F.symmetricValue_pi, hF0]
    dsimp [A, OneSidedSmoothing.A]
    ring
  have hElo : A ^ 2 ≤ E := by
    have he := comparison_energy_excess hφ hF hf0
    have hn := fourResidualEnergy_nonneg' hφ
      (fun t => F.pinnedProfile t + comparisonProfile P.φ t)
      (fun t => F.pinnedProfileDerivative t + comparisonDerivative P.φ t)
    change A ^ 2 ≤ fourResidualEnergy P.φ F.pinnedProfile F.pinnedProfileDerivative
    rw [he]
    exact le_add_of_nonneg_right hn
  have hEpos : 0 < E := (sq_pos_of_pos hA).trans_le hElo
  have hEupper : E ≤ A ^ 2 + 216 * J ^ 2 * η :=
    OneSidedSmoothing.energy_bound hP hbox hη hη1 hηsin hsep2
  have hCE : C * sqrt E < A ^ 2 := by
    calc
      C * sqrt E ≤ C₀ * sqrt E := mul_le_mul_of_nonneg_right (le_max_left _ _) (sqrt_nonneg E)
      _ ≤ C₀ * sqrt (A ^ 2 + 216 * J ^ 2 * η) :=
        mul_le_mul_of_nonneg_left (sqrt_le_sqrt hEupper) hC₀nonneg
      _ < A ^ 2 := hstrict
  let τ := min F.safeAmplitude (ε / (1 + A * sqrt E)) / 2
  have hden : 0 < 1 + A * sqrt E := by positivity
  have hτ : 0 < τ := by dsimp [τ]; exact div_pos (lt_min F.safeAmplitude_pos (div_pos hε hden)) (by norm_num)
  have hτsafe : τ ≤ F.safeAmplitude := by
    have hmin := min_le_left F.safeAmplitude (ε / (1 + A * sqrt E))
    have hp := lt_min F.safeAmplitude_pos (div_pos hε hden)
    dsimp [τ]
    linarith
  have hτnear : τ * (A * sqrt E) ≤ ε := by
    have hmin := min_le_right F.safeAmplitude (ε / (1 + A * sqrt E))
    have hp := lt_min F.safeAmplitude_pos (div_pos hε hden)
    have hτbound : τ ≤ ε / (1 + A * sqrt E) := by dsimp [τ]; linarith
    have hm := (le_div_iff₀ hden).mp hτbound
    nlinarith only [hm, hτ.le]
  let K := perturbedCap hP hbox F τ hτ.le hτsafe
  have hK := perturbedCap_isCap hP hbox F τ hτ.le hτsafe
  have henergy : capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 K = τ ^ 2 * E :=
    (perturbedCap_data_energy hP hbox F hτ hτsafe).2
  have hsqrt : sqrt (τ ^ 2 * E) = τ * sqrt E := by
    rw [sqrt_mul (sq_nonneg τ), sqrt_sq hτ.le]
  have hmid := perturbedCap_midpoint hP hbox F hτ.le hτsafe
  have href : centeredReference P.cap K.1 = P.cap := by
    simp [centeredReference, horizontalReference, hmid]
  have hclose := centered_energy P.φ hφ (wideGerverTriple hP hbox).1.1 K
    (wideGerverTriple hP hbox).2.1 hK
  rw [henergy, hsqrt, href] at hclose
  have hlower := perturbedCap_width_lower hP hbox F hτ.le hτsafe
  rw [hF0, abs_neg, abs_of_nonneg (sq_nonneg A)] at hlower
  refine ⟨K, hK, hclose.mono ?_, ?_, ?_⟩
  · change A * (τ * sqrt E) ≤ ε
    nlinarith only [hτnear]
  · rw [henergy]
    exact mul_pos (sq_pos_of_pos hτ) hEpos
  · rw [henergy, hsqrt]
    have hm := mul_lt_mul_of_pos_left hCE hτ
    exact (by nlinarith only [hm] : C * (τ * sqrt E) < τ * A ^ 2).trans_le hlower

end MovingSofaQuantitative
