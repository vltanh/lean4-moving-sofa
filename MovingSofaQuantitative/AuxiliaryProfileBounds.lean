module

public import MovingSofaQuantitative.ShortArcBounds

/-!
# Actual auxiliary profiles near the active endpoints

Uncompiled proof source. The bounds are obtained from their genuine tangent
residuals and exact contact values. No pointwise bound on an arbitrary auxiliary
body is assumed. The two coefficients 5 and 4 are deliberately coarse and leave
room for the endpoint derivative-energy argument.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

def rightAuxiliaryDerivative {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  auxiliaryDerivative (wideGerverTriple hP hbox).1.2.1.1 x.1.2.1.1
    (supp x.1.1.1 π - supp P.cap π)

def leftAuxiliaryDerivative {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  auxiliaryDerivative (wideGerverTriple hP hbox).1.2.2.1 x.1.2.2.1
    (supp x.1.1.1 π - supp P.cap π)

def rightAuxiliaryResidual {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  tangentResidual (π / 2) (rightAuxiliaryProfile hP hbox x)
    (rightAuxiliaryDerivative hP hbox x)

def leftAuxiliaryResidual {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ → ℝ :=
  tangentResidual (π - P.φ) (leftAuxiliaryProfile hP hbox x)
    (leftAuxiliaryDerivative hP hbox x)

theorem rightAuxiliary_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    Continuous (rightAuxiliaryProfile hP hbox x) ∧
    (∀ t, HasDerivWithinAt (rightAuxiliaryProfile hP hbox x)
      (rightAuxiliaryDerivative hP hbox x t) (Ioi t) t) ∧
    IntervalIntegrable (rightAuxiliaryResidual hP hbox x) volume P.φ (π / 2) ∧
    IntervalIntegrable (fun t => rightAuxiliaryResidual hP hbox x t ^ 2) volume P.φ (π / 2) ∧
    arcSquare P.φ (π / 2) (rightAuxiliaryResidual hP hbox x) =
      2 * rightResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1 := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  let B₀ := (wideGerverTriple hP hbox).1.2.1
  let B₁ := x.1.2.1
  let a := supp x.1.1.1 π - supp P.cap π
  obtain ⟨hi, hi2, he⟩ := auxiliaryResidual_data B₀ B₁ a
    (a := P.φ) (b := π / 2) (T := π / 2)
    (by linarith) (by linarith [pi_pos]) (by linarith [pi_pos]) le_rfl
  refine ⟨auxiliaryDifference_continuous B₀ B₁ a,
    fun t => auxiliaryDifference_rightDeriv B₀ B₁ a t, hi, hi2, ?_⟩
  simpa only [rightResidualEnergy, show π + π / 2 = 3 * π / 2 by ring] using he

theorem leftAuxiliary_data {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    Continuous (leftAuxiliaryProfile hP hbox x) ∧
    (∀ t, HasDerivWithinAt (leftAuxiliaryProfile hP hbox x)
      (leftAuxiliaryDerivative hP hbox x t) (Ioi t) t) ∧
    IntervalIntegrable (leftAuxiliaryResidual hP hbox x) volume (π / 2) (π - P.φ) ∧
    IntervalIntegrable (fun t => leftAuxiliaryResidual hP hbox x t ^ 2) volume (π / 2) (π - P.φ) ∧
    arcSquare (π / 2) (π - P.φ) (leftAuxiliaryResidual hP hbox x) =
      2 * leftResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2 := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  let D₀ := (wideGerverTriple hP hbox).1.2.2
  let D₁ := x.1.2.2
  let a := supp x.1.1.1 π - supp P.cap π
  obtain ⟨hi, hi2, he⟩ := auxiliaryResidual_data D₀ D₁ a
    (a := π / 2) (b := π - P.φ) (T := π - P.φ)
    (by linarith) (by linarith [pi_pos]) (by linarith [pi_pos]) le_rfl
  refine ⟨auxiliaryDifference_continuous D₀ D₁ a,
    fun t => auxiliaryDifference_rightDeriv D₀ D₁ a t, hi, hi2, ?_⟩
  simpa only [leftResidualEnergy, show π + π / 2 = 3 * π / 2 by ring,
    show π + (π - P.φ) = 3 * π / 2 + (π / 2 - P.φ) by ring] using he

/-- Every auxiliary arc has squared residual norm at most twice Delta. -/
theorem auxiliary_energies_le_deficit {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) :
    arcSquare P.φ (π / 2) (rightAuxiliaryResidual hP hbox x) ≤ 2 * qDeficit P x ∧
    arcSquare (π / 2) (π - P.φ) (leftAuxiliaryResidual hP hbox x) ≤ 2 * qDeficit P x := by
  have h := q_energy_component_bounds hP hbox x
  have hn : 0 ≤ capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 := by
    have he := tripleResidualVector_norm_sq hP hbox x
    nlinarith [sq_nonneg ‖tripleResidualVector hP hbox x‖]
  rw [(rightAuxiliary_data hP hbox x).2.2.2.2,
    (leftAuxiliary_data hP hbox x).2.2.2.2]
  constructor <;> linarith [h.2.2.2.1, h.2.2.2.2]

/-- The B integrating factor on the entire interval used by endpoint averaging. -/
theorem rightAuxiliaryProfile_bound {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) {t : ℝ}
    (ht : t ∈ Icc P.φ (criticalLeft P + 1 / 8)) :
    |rightAuxiliaryProfile hP hbox x t| ≤ 5 * sqrt (qDeficit P x) := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hloc := endpoint_short_arc_locations hP hbox
  have htv : t < π / 2 := ht.2.trans_lt (hloc.1.trans hb)
  have htshort : t ∈ Icc 0 (51 / 50) := ⟨hp.le.trans ht.1, ht.2.trans hloc.2.1.le⟩
  have hc : ∀ u ∈ Icc P.φ t, 0 < cos u := by
    intro u hu
    have h := short_cos_lower ⟨hp.le.trans hu.1, hu.2.trans htshort.2⟩
    linarith
  obtain ⟨hcont, hder, hi, hi2, he⟩ := rightAuxiliary_data hP hbox x
  have hit := intervalIntegrable_subinterval hi le_rfl ht.1 htv.le
  have hit2 := intervalIntegrable_subinterval hi2 le_rfl ht.1 htv.le
  have hk : ContinuousOn (fun u => 1 / cos u) (Icc P.φ t) :=
    continuousOn_const.div continuous_cos.continuousOn (fun u hu => (hc u hu).ne')
  have hcs := integral_square_control ht.1 hk hit hit2
  have hker : (∫ u in P.φ..t, (1 / cos u) ^ 2) ≤ 2 := by
    rw [secant_sq_integral ht.1 (fun u hu => (hc u hu).ne')]
    have hh := short_tan_bounds htshort
    have hpTan := (cap_angle_parameters (gm_φ_mem_Ioo hP hbox)).2.2.1
    linarith
  have hE := (arcSquare_mono hi2 le_rfl ht.1 htv.le).trans
    (auxiliary_energies_le_deficit hP hbox x).1
  have hI : |∫ u in P.φ..t, (1 / cos u) * rightAuxiliaryResidual hP hbox x u| ≤
      2 * sqrt (qDeficit P x) := by
    apply abs_le_mul_sqrt_of_sq_le (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hker hcs.energy_nonneg
    nlinarith only [hcs.bound, hm, hE]
  have hrec := tangent_reconstruct_right (T := π / 2) ht.1 hcont.continuousOn
    (fun u _ => hder u)
    (fun u hu => by rw [sin_pi_div_two_sub]; exact (hc u hu).ne')
    (by
      simpa only [sin_pi_div_two_sub, div_eq_mul_inv, mul_comm] using
        hit.mul_continuousOn (by simpa only [uIcc_of_le ht.1] using hk))
  have htop := (auxiliaryProfile_contacts hP hbox x).1
  have hcut := (auxiliaryProfile_contacts hP hbox x).2.2.1
  have hformula : rightAuxiliaryProfile hP hbox x t = cos t *
      (rightAuxiliaryProfile hP hbox x P.φ / cos P.φ -
        ∫ u in P.φ..t, (1 / cos u) * rightAuxiliaryResidual hP hbox x u) := by
    simpa only [tangentQuotient, htop, zero_mul, sub_zero, zero_add,
      sin_pi_div_two_sub, rightAuxiliaryResidual, div_eq_mul_inv, mul_comm] using hrec
  rw [hformula, abs_mul]
  have hc₀ : |rightAuxiliaryProfile hP hbox x P.φ / cos P.φ| ≤
      3 * sqrt (qDeficit P x) := by
    rw [hcut, neg_div, abs_neg]
    exact first_cap_contact_bound hP hbox x
  have hsum := (abs_sub _ _).trans (add_le_add hc₀ hI)
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one t)).trans
    (hsum.trans_eq (by ring))

/-- The D profile on its active arc. This proof integrates before estimating;
its endpoint coefficient is -cos(t)/cos(phi), not a sum of two coarse terms. -/
theorem leftAuxiliaryProfile_bound {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) {t : ℝ}
    (ht : t ∈ Icc (π / 2) (criticalRight P)) :
    |leftAuxiliaryProfile hP hbox x t| ≤ 4 * sqrt (qDeficit P x) := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  obtain ⟨hcont, hder, hi, hi2, he⟩ := leftAuxiliary_data hP hbox x
  have htt : t ≤ π - P.φ := ht.2.trans hdT.le
  have hs : ∀ u ∈ Icc (π / 2) t, 0 < sin (π - P.φ - u) := by
    intro u hu
    have hh := (active_sine_bounds hP hbox ⟨hu.1, hu.2.trans ht.2⟩).2
    linarith
  have hk : ContinuousOn (fun u => 1 / sin (π - P.φ - u)) (Icc (π / 2) t) :=
    continuousOn_const.div (by fun_prop) (fun u hu => (hs u hu).ne')
  have hit := intervalIntegrable_subinterval hi le_rfl ht.1 htt
  have hit2 := intervalIntegrable_subinterval hi2 le_rfl ht.1 htt
  have hcs := integral_square_control ht.1 hk hit hit2
  have hker : (∫ u in (π / 2)..t, (1 / sin (π - P.φ - u)) ^ 2) ≤ 3 := by
    have hm := intervalIntegral.integral_mono_on ht.1
      ((hk.pow 2).intervalIntegrable_of_Icc ht.1)
      (intervalIntegrable_const (c := (4 : ℝ))) (fun u hu => by
        have hh := (active_cot_bounds hP hbox ⟨hu.1, hu.2.trans ht.2⟩).2.2
        have hn : 0 ≤ 1 / sin (π - P.φ - u) := by
          have hh := (active_sine_bounds hP hbox ⟨hu.1, hu.2.trans ht.2⟩).2
          positivity
        nlinarith)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    have hθ := hbox.2
    unfold criticalRight at ht
    linarith [ht.2]
  have hE := (arcSquare_mono hi2 le_rfl ht.1 htt).trans
    (auxiliary_energies_le_deficit hP hbox x).2
  have hI : |∫ u in (π / 2)..t,
      (1 / sin (π - P.φ - u)) * leftAuxiliaryResidual hP hbox x u| ≤
      (5 / 2) * sqrt (qDeficit P x) := by
    apply abs_le_mul_sqrt_of_sq_le (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hker hcs.energy_nonneg
    have hΔ := (q_energy_component_bounds hP hbox x).1
    nlinarith only [hcs.bound, hm, hE, hΔ]
  have hrec := tangent_reconstruct_right (T := π - P.φ) ht.1 hcont.continuousOn
    (fun u _ => hder u) (fun u hu => (hs u hu).ne')
    (by
      simpa only [div_eq_mul_inv, mul_comm] using
        hit.mul_continuousOn (by simpa only [uIcc_of_le ht.1] using hk))
  have htop := (auxiliaryProfile_contacts hP hbox x).2.1
  have hcut := (auxiliaryProfile_contacts hP hbox x).2.2.2
  have hcφ := cos_phi_ge_five_sixths hbox
  have hcφp : 0 < cos P.φ := by linarith
  have hcoeff : cos (π - P.φ - t) -
      sin (π - P.φ - t) * (sin P.φ / cos P.φ) = -cos t / cos P.φ := by
    have hh : cos (π - P.φ - t) * cos P.φ -
        sin (π - P.φ - t) * sin P.φ = -cos t := by
      rw [← cos_add, show π - P.φ - t + P.φ = π - t by ring, cos_pi_sub]
    field_simp [hcφp.ne']
    exact hh
  have hq : tangentQuotient (π - P.φ) (leftAuxiliaryProfile hP hbox x) (π / 2) =
      -leftAuxiliaryProfile hP hbox x (π - P.φ) * (sin P.φ / cos P.φ) := by
    simp only [tangentQuotient, htop, zero_sub,
      show π - P.φ - π / 2 = π / 2 - P.φ by ring,
      cos_pi_div_two_sub, sin_pi_div_two_sub]
    ring
  have hformula : leftAuxiliaryProfile hP hbox x t =
      (-cos t / cos P.φ) * leftAuxiliaryProfile hP hbox x (π - P.φ) -
      sin (π - P.φ - t) * (∫ u in (π / 2)..t,
        (1 / sin (π - P.φ - u)) * leftAuxiliaryResidual hP hbox x u) := by
    rw [hq] at hrec
    have hIeq : (∫ u in (π / 2)..t,
        tangentResidual (π - P.φ) (leftAuxiliaryProfile hP hbox x)
          (leftAuxiliaryDerivative hP hbox x) u / sin (π - P.φ - u)) =
        ∫ u in (π / 2)..t, (1 / sin (π - P.φ - u)) * leftAuxiliaryResidual hP hbox x u := by
      apply intervalIntegral.integral_congr
      intro u _
      unfold leftAuxiliaryResidual
      ring
    rw [hIeq] at hrec
    calc
      _ = (cos (π - P.φ - t) - sin (π - P.φ - t) * (sin P.φ / cos P.φ)) *
          leftAuxiliaryProfile hP hbox x (π - P.φ) -
          sin (π - P.φ - t) * (∫ u in (π / 2)..t,
            (1 / sin (π - P.φ - u)) * leftAuxiliaryResidual hP hbox x u) := by
        rw [hrec]
        ring
      _ = _ := by rw [hcoeff]
  have hcoef : |-cos t / cos P.φ| ≤ 6 / 5 := by
    rw [abs_div, abs_neg, abs_of_pos hcφp]
    apply (div_le_iff₀ hcφp).2
    linarith [abs_cos_le_one t]
  have hvalue : |leftAuxiliaryProfile hP hbox x (π - P.φ)| ≤ sqrt (qDeficit P x) := by
    rw [hcut, abs_neg]
    exact last_cap_profile_bound hP hbox x ⟨hvd.le.trans hdT.le, hTp.le⟩
  rw [hformula]
  have h1 := mul_le_mul hcoef hvalue (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6 / 5)
  have h2 := mul_le_mul (abs_sin_le_one (π - P.φ - t)) hI
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have habs := abs_sub
    ((-cos t / cos P.φ) * leftAuxiliaryProfile hP hbox x (π - P.φ))
    (sin (π - P.φ - t) * (∫ u in (π / 2)..t,
      (1 / sin (π - P.φ - u)) * leftAuxiliaryResidual hP hbox x u))
  simp only [abs_mul] at habs
  nlinarith only [habs, h1, h2, sqrt_nonneg (qDeficit P x)]

end MovingSofaQuantitative
