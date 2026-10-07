module

public import MovingSofaQuantitative.DualSlack
public import MovingSofaQuantitative.ScalarTaylor

/-!
# A numerical density bound from the exact reference phases

Uncompiled proof source. The bound 1/8 uses only the already enclosed b₁ and θ.
The derivative at a phase junction need not equal either one-sided derivative;
all measure comparisons remove the finitely many junctions explicitly.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

def referenceDensityB (P : GerverParams) (t : ℝ) : ℝ :=
  dot (-deriv P.curveB t) (vvec t)

def referenceDensityD (P : GerverParams) (t : ℝ) : ℝ :=
  dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2))

/-- On the long active B phase the density is affine, and on the final phase it
is exactly one half. Neither formula depends on an approximate optimizer. -/
theorem referenceDensityB_formula {P : GerverParams} (hP : P.IsSolution)
    {t : ℝ} (ht : t ∈ Ioo (criticalLeft P) (π / 2))
    (hne : t ≠ π / 2 - P.φ) :
    referenceDensityB P t = if t < π / 2 - P.φ then
      1 + P.b₁ - (π / 2 - t) / 2 else 1 / 2 := by
  unfold referenceDensityB
  change dot (-deriv (contactB P.path) t) (vvec t) = _
  split_ifs with h
  · have hd := gs_hasDerivAt_contactB hP (i := 3)
      (show gs_opiece P 3 t from ⟨ht.1, h⟩)
    rw [hd.deriv, dot_neg_left, dot_smul_left, dot_vvec_self, mul_one]
    simp only [gs_phase, gs_Phase.ρA, gs_ph4, gs_d₁ hP]
    ring
  · have hd := gs_hasDerivAt_contactB hP (i := 4)
      (show gs_opiece P 4 t from lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne))
    rw [hd.deriv, dot_neg_left, dot_smul_left, dot_vvec_self, mul_one]
    simp only [gs_phase, gs_Phase.ρA, gs_ph5]
    ring

theorem referenceDensityD_formula {P : GerverParams} (hP : P.IsSolution)
    {t : ℝ} (ht : t ∈ Ioo (π / 2) (criticalRight P))
    (hne : t ≠ π / 2 + P.φ) :
    referenceDensityD P t = if t < π / 2 + P.φ then 1 / 2 else
      1 + P.b₁ - (t - π / 2) / 2 := by
  unfold referenceDensityD
  change dot (deriv (contactD P.path) (t - π / 2)) (uvec (t - π / 2)) = _
  split_ifs with h
  · have hd := gs_hasDerivAt_contactD hP (i := 0)
      (show gs_opiece P 0 (t - π / 2) from by linarith)
    rw [hd.deriv, dot_smul_left, dot_uvec_self, mul_one]
    simp only [gs_phase, gs_Phase.ρC, gs_ph1]
    ring
  · have hd := gs_hasDerivAt_contactD hP (i := 1)
      (show gs_opiece P 1 (t - π / 2) from
        ⟨by
          have hn := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
          linarith,
        by unfold criticalRight at ht; linarith [ht.2]⟩)
    rw [hd.deriv, dot_smul_left, dot_uvec_self, mul_one]
    simp only [gs_phase, gs_Phase.ρC, gs_ph2]
    ring

/-- The full reference parameter box supplies a strict positive density margin. -/
theorem reference_density_affine_bounds {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {s : ℝ} (hs : s ∈ Icc 0 P.θ) :
    (1 / 8 : ℝ) ≤ 1 + P.b₁ - s / 2 ∧ 1 + P.b₁ - s / 2 ≤ 1 := by
  have hB := romik_bounds hP hbox
  have hbLo := gs_b₁_lo hB
  have hbHi := gs_b₁_hi hB
  have hθ := hbox.2.2
  constructor <;> linarith [hs.1, hs.2]

theorem referenceDensityB_bounds_ae {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∀ᵐ t ∂volume.restrict (Ico (criticalLeft P) (π / 2)),
      (1 / 8 : ℝ) ≤ referenceDensityB P t ∧ referenceDensityB P t ≤ 1 := by
  apply gm_ae_restrict_of_countable measurableSet_Ico
    ((countable_singleton (criticalLeft P)).insert (π / 2 - P.φ))
  intro t ht hne
  have ht' : t ∈ Ioo (criticalLeft P) (π / 2) :=
    ⟨lt_of_le_of_ne ht.1 (by
      intro h
      exact hne (Or.inr h.symm)), ht.2⟩
  have hj : t ≠ π / 2 - P.φ := fun h => hne (Or.inl h)
  rw [referenceDensityB_formula hP ht' hj]
  split_ifs
  · exact reference_density_affine_bounds hP hbox
      ⟨by linarith [ht.2], by unfold criticalLeft at ht; linarith [ht.1]⟩
  · norm_num

theorem referenceDensityD_bounds_ae {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∀ᵐ t ∂volume.restrict (Ioc (π / 2) (criticalRight P)),
      (1 / 8 : ℝ) ≤ referenceDensityD P t ∧ referenceDensityD P t ≤ 1 := by
  apply gm_ae_restrict_of_countable measurableSet_Ioc
    ((countable_singleton (criticalRight P)).insert (π / 2 + P.φ))
  intro t ht hne
  have ht' : t ∈ Ioo (π / 2) (criticalRight P) :=
    ⟨ht.1, lt_of_le_of_ne ht.2 (fun h => hne (Or.inr h))⟩
  have hj : t ≠ π / 2 + P.φ := fun h => hne (Or.inl h)
  rw [referenceDensityD_formula hP ht' hj]
  split_ifs
  · norm_num
  · exact reference_density_affine_bounds hP hbox
      ⟨by linarith [ht.1], by unfold criticalRight at ht; linarith [ht.2]⟩

/-- A positive density lower bound converts its nonnegative integral into an
unweighted mass bound. All integrability requirements remain visible. -/
theorem mass_le_eight_weighted {μ : Measure ℝ} {f ρ : ℝ → ℝ}
    (hf : Integrable f μ) (hρf : Integrable (fun t => ρ t * f t) μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hρ : ∀ᵐ t ∂μ, (1 / 8 : ℝ) ≤ ρ t) :
    (∫ t, f t ∂μ) ≤ 8 * ∫ t, ρ t * f t ∂μ := by
  have hm : (∫ t, (1 / 8 : ℝ) * f t ∂μ) ≤ ∫ t, ρ t * f t ∂μ := by
    apply integral_mono_ae (hf.const_mul _) hρf
    filter_upwards [hf0, hρ] with t ht hr
    exact mul_le_mul_of_nonneg_right hr ht
  rw [integral_const_mul] at hm
  linarith

/-- The density integral of a continuous function is exactly its integral for
the active reference B measure. -/
theorem activeMeasureB_integral {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂activeMeasureB P) =
      ∫ t in Ico (criticalLeft P) (π / 2), referenceDensityB P t * f t := by
  rw [activeMeasureB, gm_prop844_two hP hbox,
    integral_withDensity_eq_integral_toReal_smul gm_measurable_rhoB
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [referenceDensityB_bounds_ae hP hbox] with t ht
  simp only [referenceDensityB, ENNReal.toReal_ofReal (by linarith [ht.1]), smul_eq_mul]

theorem activeMeasureD_integral {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (f : ℝ → ℝ) :
    (∫ t, f t ∂activeMeasureD P) =
      ∫ t in Ioc (π / 2) (criticalRight P), referenceDensityD P t * f t := by
  rw [activeMeasureD, gm_prop844_four hP hbox,
    integral_withDensity_eq_integral_toReal_smul gm_measurable_rhoD
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [referenceDensityD_bounds_ae hP hbox] with t ht
  simp only [referenceDensityD, ENNReal.toReal_ofReal (by linarith [ht.1]), smul_eq_mul]

/-- Bounded measurable densities on a finite interval preserve integrability. -/
theorem integrable_bounded_density_mul {μ : Measure ℝ} {f ρ : ℝ → ℝ}
    (hf : Integrable f μ) (hρ : Measurable ρ)
    (hbound : ∀ᵐ t ∂μ, 0 ≤ ρ t ∧ ρ t ≤ 1) :
    Integrable (fun t => ρ t * f t) μ := by
  apply hf.norm.mono' (hρ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [hbound] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) ht.2

/-- Each active wall has unweighted mass at most eight times the ACTUAL dual
slack. This is the numerical mass input to the endpoint-averaging theorem. -/
theorem wall_slack_mass_bounds {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    (∫ t in (criticalLeft P)..(π / 2), rightWallSlack x t) ≤ 8 * wideDualSlack hP hbox x ∧
    (∫ t in (π / 2)..(criticalRight P), leftWallSlack x t) ≤ 8 * wideDualSlack hP hbox x := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hBcont := rightWallSlack_continuous x
  have hDcont := leftWallSlack_continuous x
  have hBi : IntegrableOn (rightWallSlack x) (Ico (criticalLeft P) (π / 2)) :=
    hBcont.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hDi : IntegrableOn (leftWallSlack x) (Ioc (π / 2) (criticalRight P)) :=
    hDcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hB0 : 0 ≤ᵐ[volume.restrict (Ico (criticalLeft P) (π / 2))] rightWallSlack x :=
    ae_restrict_of_forall_mem measurableSet_Ico fun t ht =>
      rightWallSlack_nonneg x ⟨hpc.le.trans ht.1, ht.2.le⟩
  have hD0 : 0 ≤ᵐ[volume.restrict (Ioc (π / 2) (criticalRight P))] leftWallSlack x :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      leftWallSlack_nonneg x ⟨ht.1.le, ht.2.trans hdT.le⟩
  have hmB : Measurable (referenceDensityB P) :=
    gm_measurable_dot (measurable_deriv _).neg (by unfold vvec; fun_prop)
  have hmD : Measurable (referenceDensityD P) :=
    gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _)) (by unfold uvec; fun_prop)
  have hBbounds := referenceDensityB_bounds_ae hP hbox
  have hDbounds := referenceDensityD_bounds_ae hP hbox
  have hBprod := integrable_bounded_density_mul hBi hmB (hBbounds.mono fun _ ht => ⟨by linarith [ht.1], ht.2⟩)
  have hDprod := integrable_bounded_density_mul hDi hmD (hDbounds.mono fun _ ht => ⟨by linarith [ht.1], ht.2⟩)
  have hBm := mass_le_eight_weighted hBi hBprod hB0 (hBbounds.mono fun _ h => h.1)
  have hDm := mass_le_eight_weighted hDi hDprod hD0 (hDbounds.mono fun _ h => h.1)
  rw [← activeMeasureB_integral hP hbox] at hBm
  rw [← activeMeasureD_integral hP hbox] at hDm
  have hL := active_integrals_le_slack hP hbox x
  constructor
  · rw [intervalIntegral.integral_of_le (by linarith : criticalLeft P ≤ π / 2),
      ← integral_Ico_eq_integral_Ioc]
    linarith [hL.2.1]
  · rw [intervalIntegral.integral_of_le hvd.le]
    linarith [hL.2.2.2]

end MovingSofaQuantitative
