module

public import MovingSofaQuantitative.TrialEnergyCertificate
public import MovingSofaQuantitative.TrialActiveArc
public import MovingSofaQuantitative.FullQCertificate

/-!
# The continuously feasible lower family for the intrinsic full-Q coefficient

UNCOMPILED SOURCE.  This is the final packaging of the concrete Hermite cap,
the actual active-arc auxiliary convex bodies, exact zero first variation, and
the closed trial-energy certificate.

The fixed constant is deliberately 9221/10000, strictly above 461/500.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

theorem critical_trial_energy_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    0 < CriticalTrial.trialEnergy (CriticalTrial.profile hP) (CriticalTrial.c P) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hq : 0 < CriticalTrial.q := by norm_num [CriticalTrial.q]
  have ht : 0 < tan P.φ := tan_pos_of_pos_of_lt_pi_div_two hφ.1 (by linarith [hφ.2])
  have hscalar := CriticalTrial.trialEnergy_eq_scalar hP hbox
    (CriticalTrial.trial_residual_integrable_B hP hbox)
    (by
      have hi := CriticalTrial.trial_residual_integrable_D hP hbox
      exact hi.comp_sub_left π)
  rw [hscalar]
  unfold CriticalTrial.scalarEnergy
  have h2 := arcSquare_nonneg (by linarith [hφ.2]) (CriticalTrial.r2 P)
  have h3 := arcSquare_nonneg (by linarith [hφ.1]) (CriticalTrial.r3 P)
  have h4 := arcSquare_nonneg (by linarith [hφ.2]) (CriticalTrial.r4 P)
  have hB := arcSquare_nonneg (CriticalTrial.positions hP).2.le (CriticalTrial.rB P)
  have hD := arcSquare_nonneg (CriticalTrial.positions hP).2.le (CriticalTrial.rD P)
  have hgap : 0 ≤ CriticalTrial.bridgeSineCoefficient P^2 *
      (tan (CriticalTrial.c P)-tan P.φ) := by
    have hc : P.φ < CriticalTrial.c P := (CriticalTrial.positions hP).1
    have htan := strictMonoOn_tan
      ⟨by linarith [hφ.1,pi_pos], by linarith [hc,pi_pos]⟩
      ⟨by linarith [hφ.1,pi_pos], by linarith [(CriticalTrial.positions hP).2,pi_pos]⟩
      (by linarith [hc])
    positivity
  nlinarith [sq_pos_of_pos hq, mul_pos (sq_pos_of_pos hq) ht]

/-- Exact paper target G.4: actual feasible zero-slack triples at arbitrarily
small positive deficit, with one fixed strict ratio margin. -/
theorem feasible_critical_lower : Targets.FeasibleCriticalLower := by
  intro P hP hbox
  let F := CriticalTrial.profile hP
  let E := CriticalTrial.trialEnergy F (CriticalTrial.c P)
  have hEpos : 0 < E := critical_trial_energy_pos hP hbox
  have hEupper : E < 147/125 :=
    CriticalTrialCertificate.critical_trial_energy_lt_147_125 hP hbox
  have hmargin := feasible_trial_uniform_margin hEpos.le hEupper.le
  refine ⟨9221/10000, hmargin.1, ?_⟩
  intro η hη
  have hjet : F.first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) (π/2-P.θ) := by
    simpa [F,CriticalTrial.c] using CriticalTrial.contact_jet hP
  obtain ⟨τ₀,hτ₀,hτsafe,hfamily⟩ :=
    exists_perturbed_active_arc hP hbox F hjet
  let τ := min (τ₀/2) (sqrt (η/E)/2)
  have hηE : 0 < η/E := div_pos hη hEpos
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτ₀' : τ ≤ τ₀ := (min_le_left _ _).trans (by linarith [hτ₀])
  have hsafe : τ ≤ F.safeAmplitude := hτ₀'.trans hτsafe
  obtain ⟨D,hcurve⟩ := hfamily τ hτ.le hτ₀' hsafe
  let x : WideTriple P.φ :=
    D.wideTriple (fun t ht => perturbedCap_reflection_support hP hbox F hτ.le hsafe ht)
  have hzero : wideDualSlack hP hbox x=0 := by
    exact activeArc_trial_zero_slack hP hbox F hτ.le hsafe D
  have hdef : qDeficit P x=τ^2*E := by
    simpa [x,E,CriticalTrial.c] using
      activeArc_trial_deficit hP hbox F hτ hsafe hjet D hcurve
  have hdefpos : 0 < qDeficit P x := by
    rw [hdef]
    exact mul_pos (sq_pos_of_pos hτ) hEpos
  have hsmall : qDeficit P x < η := by
    rw [hdef]
    have ht : τ ≤ sqrt (η/E)/2 := min_le_right _ _
    have hs := sq_sqrt hηE.le
    have hm := mul_le_mul_of_nonneg_left (sq_le_sq₀ hτ.le ht) hEpos.le
    have he : E*(η/E)=η := by field_simp [hEpos.ne']
    nlinarith only [hm,hs,he,hη]
  have hlower : τ ≤ capTranslationDistance P.cap x.1.1.1 := by
    have hw := perturbedCap_width_lower hP hbox F hτ.le hsafe
    have hz : F.value 0=-1 := by simpa [F] using CriticalTrial.profile_zero hP
    rw [hz,abs_neg,abs_one,mul_one] at hw
    simpa [x] using hw
  have hsqrt : sqrt (qDeficit P x)=τ*sqrt E := by
    rw [hdef,sqrt_mul (sq_nonneg τ),sqrt_sq hτ.le]
  refine ⟨x,hzero,hdefpos,hsmall,?_⟩
  rw [hsqrt]
  have hm := mul_lt_mul_of_pos_left hmargin.2 hτ
  exact (hm.le.trans hlower)

theorem intrinsic_interval : Targets.IntrinsicInterval :=
  intrinsic_interval_of_bounds full_q_finite feasible_critical_lower

end MovingSofaQuantitative
