module

public import MovingSofaQuantitative.WallDerivative
public import MovingSofaQuantitative.CriticalTransfer

/-!
# The actual endpoint wall-slack bound

Uncompiled proof source. This discharges the endpoint hypothesis of the full-Q
transfer using the actual reference measure densities and actual auxiliary
residual energies. Both endpoints are treated on their correct one-sided
intervals. No symmetry of the competing triple is assumed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

/-- The right-endpoint version of the averaging estimate. -/
theorem right_endpoint_average_bound {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivWithinAt f (d t) (Ioi t) t)
    (hd : IntervalIntegrable d volume a b)
    (hd2 : IntervalIntegrable (fun t => d t ^ 2) volume a b)
    {A B : ℝ} (hB : 0 ≤ B) (hmass : (∫ t in a..b, f t) ≤ A)
    (henergy : arcSquare a b d ≤ B ^ 2) :
    f b ≤ A / (b - a) + sqrt (b - a) * B := by
  have hpoint : ∀ t ∈ Icc a b, f b - sqrt (b - a) * B ≤ f t := by
    intro t ht
    have hi := intervalIntegrable_subinterval hd ht.1 ht.2 le_rfl
    have hi2 := intervalIntegrable_subinterval hd2 ht.1 ht.2 le_rfl
    have hE := (arcSquare_mono hd2 ht.1 ht.2 le_rfl).trans henergy
    have hcs := integral_subinterval_abs_le (a := t) (b := b) (t := b)
      ⟨ht.2, le_rfl⟩ hi hi2 hB hE
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2
      (hf.mono (Icc_subset_Icc_left ht.1))
      (fun u hu => hder u ⟨ht.1.trans_lt hu.1, hu.2⟩) hi
    rw [hFTC] at hcs
    have hlen := mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by linarith [ht.1] : b - t ≤ b - a)) hB
    linarith [(abs_le.mp hcs).2]
  have hi := hf.intervalIntegrable_of_Icc hab.le
  have hm := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hi hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hdiv : f b - sqrt (b - a) * B ≤ A / (b - a) := by
    apply (le_div_iff₀ hlen).mpr
    nlinarith only [hm, hmass]
  linarith

/-- Wall slack at the beginning of the B active arc. -/
theorem right_wall_endpoint_bound {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) (hΔ : 0 < qDeficit P x)
    (hsmall : qDeficit P x ≤ 1 / 512) :
    |rightWallSlack x (criticalLeft P)| ≤ 16 * (qDeficit P x) ^ (2 / 3 : ℝ) := by
  let w := (qDeficit P x) ^ (1 / 3 : ℝ)
  have hw : 0 < w := rpow_pos_of_pos hΔ _
  have hw8 : w ≤ 1 / 8 := cube_root_fits_eighth hΔ.le hsmall
  have hloc := endpoint_short_arc_locations hP hbox
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hcv : criticalLeft P + w ≤ π / 2 := by linarith [hloc.1]
  have hcont := rightWallSlack_continuous x
  have hfull := hcont.intervalIntegrable (criticalLeft P) (π / 2)
  have hmass := nonnegative_integral_subinterval hfull
    (fun t ht => rightWallSlack_nonneg x ⟨hpc.le.trans ht.1, ht.2⟩)
    (c := criticalLeft P) (d := criticalLeft P + w) le_rfl (by linarith) hcv
  have hweighted := (wall_slack_mass_bounds hP hbox x).1
  have hL := (q_energy_component_bounds hP hbox x).2.2.1
  have hmass' : (∫ t in (criticalLeft P)..(criticalLeft P + w), rightWallSlack x t) ≤
      8 * qDeficit P x := by linarith
  obtain ⟨hi, hi2, hE⟩ := right_wall_derivative_energy hP hbox x
    (a := criticalLeft P) (b := criticalLeft P + w) le_rfl (by linarith) (by linarith)
  have he := endpoint_slack_from_energy hΔ hcont.continuousOn
    (fun t ht => rightWallDerivative_hasDeriv hP hbox x
      ⟨ht.1.le, ht.2.trans_le hcv⟩) hi hi2 hmass' hE
  rw [abs_of_nonneg (rightWallSlack_nonneg x ⟨hpc.le, hcb.le.trans hb.le⟩)]
  exact he

/-- Wall slack at the end of the D active arc. This is not obtained by
reflecting the competitor or assuming it symmetric. -/
theorem left_wall_endpoint_bound {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) (hΔ : 0 < qDeficit P x)
    (hsmall : qDeficit P x ≤ 1 / 512) :
    |leftWallSlack x (criticalRight P)| ≤ 16 * (qDeficit P x) ^ (2 / 3 : ℝ) := by
  let w := (qDeficit P x) ^ (1 / 3 : ℝ)
  have hw : 0 < w := rpow_pos_of_pos hΔ _
  have hw8 : w ≤ 1 / 8 := cube_root_fits_eighth hΔ.le hsmall
  have hloc := endpoint_short_arc_locations hP hbox
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hva : π / 2 ≤ criticalRight P - w := by linarith [hloc.2.2.1]
  have hcont := leftWallSlack_continuous x
  have hfull := hcont.intervalIntegrable (π / 2) (criticalRight P)
  have hmass := nonnegative_integral_subinterval hfull
    (fun t ht => leftWallSlack_nonneg x ⟨ht.1, ht.2.trans hdT.le⟩)
    (c := criticalRight P - w) (d := criticalRight P) hva (by linarith) le_rfl
  have hweighted := (wall_slack_mass_bounds hP hbox x).2
  have hL := (q_energy_component_bounds hP hbox x).2.2.1
  have hmass' : (∫ t in (criticalRight P - w)..(criticalRight P), leftWallSlack x t) ≤
      8 * qDeficit P x := by linarith
  obtain ⟨hi, hi2, hE⟩ := left_wall_derivative_energy hP hbox x
    (a := criticalRight P - w) (b := criticalRight P) (by linarith) (by linarith) le_rfl
  have hE' : arcSquare (criticalRight P - w) (criticalRight P) (leftWallDerivative hP hbox x) ≤
      (8 * sqrt (qDeficit P x)) ^ 2 := by
    rw [mul_pow, sq_sqrt hΔ.le]
    norm_num
    exact hE
  have he := right_endpoint_average_bound (by linarith : criticalRight P - w < criticalRight P)
    hcont.continuousOn (fun t ht => leftWallDerivative_hasDeriv hP hbox x
      ⟨hva.trans ht.1.le, ht.2⟩) hi hi2 (by positivity) hmass' hE'
  rw [show criticalRight P - (criticalRight P - w) = w by ring] at he
  change leftWallSlack x (criticalRight P) ≤
    (8 * qDeficit P x) / (qDeficit P x) ^ (1 / 3 : ℝ) +
      sqrt ((qDeficit P x) ^ (1 / 3 : ℝ)) * (8 * sqrt (qDeficit P x)) at he
  rw [endpoint_cube_root_arithmetic hΔ] at he
  rw [abs_of_nonneg (leftWallSlack_nonneg x ⟨hvd.le, hdT.le⟩)]
  exact he

/-- The endpoint input to the full-Q theorem is now supplied by the actual
feasible triple, with no derivative or mass certificate left as a hypothesis. -/
theorem actual_endpoint_slacks {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    EndpointSlackBound hP hbox := by
  intro x hΔ hsmall
  exact ⟨right_wall_endpoint_bound hP hbox x hΔ hsmall,
    left_wall_endpoint_bound hP hbox x hΔ hsmall⟩

/-- The only remaining input here is the concrete continuum operator certificate;
endpoint regularity and wall feasibility are not delegated to that certificate. -/
theorem fullQ_upper_package_of_operator
    (hop : ∀ (P : GerverParams) (hP : P.IsSolution) (hbox : P.InBox),
      CriticalOperatorBound hP hbox) :
    Targets.CriticalFaceUpper ∧ Targets.FullQFinite ∧ Targets.FullQ094 :=
  fullQ_upper_package_of_inputs hop (fun _ hP hbox => actual_endpoint_slacks hP hbox)

end MovingSofaQuantitative
