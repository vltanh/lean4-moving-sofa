module

public import MovingSofaQuantitative.CriticalKernels
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Dual slack and the exact critical face

Uncompiled proof source. The cancellation below is the equality underlying the
integrated first-variation sign proof, not a new assumption about the functional.
Strict positivity of the reference auxiliary curvature density shows that zero
slack forces the two wall gaps to vanish on their full active arcs, including
the endpoints by continuity. No numerical lower density bound is needed for
this exact zero-slack statement.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

def activeMeasureB (P : GerverParams) : Measure ℝ :=
  (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (criticalLeft P) (π / 2))

def activeMeasureD (P : GerverParams) : Measure ℝ :=
  (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (criticalRight P))

theorem rightWallSlack_continuous {P : GerverParams} (x : WideTriple P.φ) :
    Continuous (rightWallSlack x) := by
  exact (continuous_const.sub x.1.1.2.continuous_supp).sub
    (x.1.2.1.2.continuous_supp.comp (continuous_const.add continuous_id))

theorem leftWallSlack_continuous {P : GerverParams} (x : WideTriple P.φ) :
    Continuous (leftWallSlack x) := by
  exact (continuous_const.sub x.1.1.2.continuous_supp).sub
    (x.1.2.2.2.continuous_supp.comp (continuous_const.add continuous_id))

/-- Every continuous function is integrable for the two finite reference
measures, by their occurrence in the integrated surface-area decomposition. -/
theorem activeMeasures_integrable {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (activeMeasureB P) ∧ Integrable f (activeMeasureD P) := by
  have hi : Integrable f ((sigma P.cap).restrict (Icc 0 π)) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [gm_sigma_decomp hP hbox] at hi
  simp only [integrable_add_measure] at hi
  exact ⟨hi.1.1.2, hi.1.2⟩

/-- Exact first variation as the sum of the two nonnegative wall-gap integrals. -/
theorem wideDualSlack_eq_active_integrals {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    wideDualSlack hP hbox x =
      (∫ t, rightWallSlack x t ∂activeMeasureB P) +
      (∫ t, leftWallSlack x t ∂activeMeasureD P) := by
  obtain ⟨h1, -, -, -, h4, -, -, -⟩ := theorem8_4_3_two hP hbox
  rw [wideDualSlack, wide_reference_firstVariation (gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox) x (gerverTriple hP hbox).2.1 h4.symm h1.symm]
  have hp := gm_φ_pos hP
  have hpt := gm_φ_lt_θ hP
  have ht := gm_θ_lt_c hP
  have hpi := pi_pos
  let f : ℝ → ℝ := fun t => supp x.1.1.1 t - supp P.cap t
  let gB : ℝ → ℝ := fun t => suppBreve x.1.2.1.1 t - suppBreve (rightBody P.φ P.cap) t
  let gD : ℝ → ℝ := fun t => suppBreve x.1.2.2.1 t - suppBreve (leftBody P.φ P.cap) t
  have hfc : Continuous f := x.1.1.2.continuous_supp.sub (gm_isConvexBody_cap hP hbox).continuous_supp
  have hBc : Continuous gB :=
    (x.1.2.1.2.continuous_supp.comp (continuous_id.add continuous_const)).sub
      ((gm_isConvexBody_B hP hbox).continuous_supp.comp (continuous_id.add continuous_const))
  have hDc : Continuous gD :=
    (x.1.2.2.2.continuous_supp.comp (continuous_id.add continuous_const)).sub
      ((gm_isConvexBody_D hP hbox).continuous_supp.comp (continuous_id.add continuous_const))
  let Sι := Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ)
  let ι := (iota P.cap).restrict Sι
  let β := activeMeasureB P
  let δ := activeMeasureD P
  let τ := (sigma P.cap).restrict {π / 2}
  have hdec : (sigma P.cap).restrict (Icc 0 π) = ι + β + δ + τ := gm_sigma_decomp hP hbox
  have hint : ∀ g : ℝ → ℝ, Continuous g →
      Integrable g ι ∧ Integrable g β ∧ Integrable g δ ∧ Integrable g τ := by
    intro g hg
    have h : Integrable g (ι + β + δ + τ) := by
      rw [← hdec]
      exact hg.continuousOn.integrableOn_compact isCompact_Icc
    simp only [integrable_add_measure] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  obtain ⟨iι, iβ, iδ, iτ⟩ := hint f hfc
  have eI1 : (∫ t in Icc 0 π, f t ∂sigma P.cap) =
      (∫ t, f t ∂ι) + (∫ t, f t ∂β) + (∫ t, f t ∂δ) := by
    have hz : ∫ t, f t ∂τ = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      simp only [f, mem_singleton_iff.mp ht, x.2.1.2.2.2.1,
        gm_supp_cap_pi_div_two hP hbox, sub_self]
    rw [hdec, integral_add_measure ((iι.add_measure iβ).add_measure iδ) iτ,
      integral_add_measure (iι.add_measure iβ) iδ, integral_add_measure iι iβ, hz, add_zero]
  have eI2 : (∫ t in Sι, f t * iFun P.cap t) = ∫ t, f t ∂ι := by
    have hm : Measurable (fun t => ENNReal.ofReal (iFun P.cap t)) := by
      unfold iFun
      exact (Measurable.ite measurableSet_Iic
        (gm_measurable_dot (measurable_deriv _) (by unfold vvec; fun_prop))
        (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
          (by unfold uvec; fun_prop)).neg).ennreal_ofReal
    rw [show ι = (volume.restrict Sι).withDensity (fun t => ENNReal.ofReal (iFun P.cap t)) from
        gm_iota_restrict (measurableSet_Icc.union measurableSet_Icc) (by
          rintro t (h | h) <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩),
      integral_withDensity_eq_integral_toReal_smul hm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply setIntegral_congr_fun (measurableSet_Icc.union measurableSet_Icc)
    intro t h
    have hpos : 0 ≤ iFun P.cap t := by
      rcases h with h | h
      · have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [iFun, ite_eq_left hlo.2.le]
        exact ((theorem6_1_2 hP hbox).2.2 t hlo).2.le
      · have hlo : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [iFun, ite_eq_right (not_le.mpr (by linarith [h.1]))]
        linarith [((theorem6_1_2 hP hbox).2.2 _ hlo).1]
    simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  have eB : (∫ t, rightWallSlack x t ∂β) = -((∫ t, f t ∂β) + ∫ t, gB t ∂β) := by
    rw [← integral_add iβ (hint gB hBc).2.1, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ico
    intro t htB
    have href := (theorem8_4_3_three hP hbox).2 t ⟨htB.1, htB.2.le⟩
    simp only [f, gB, suppBreve, rightWallSlack, Pi.add_apply, Pi.neg_apply]
    rw [add_comm t π]
    linarith
  have eD : (∫ t, leftWallSlack x t ∂δ) = -((∫ t, f t ∂δ) + ∫ t, gD t ∂δ) := by
    rw [← integral_add iδ (hint gD hDc).2.2.1, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t htD
    have href := (theorem8_4_3_three hP hbox).1 (t - π / 2)
      ⟨by linarith [htD.1], by linarith [htD.2]⟩
    rw [show π / 2 + (t - π / 2) = t by ring,
      show 3 * π / 2 + (t - π / 2) = π + t by ring] at href
    simp only [f, gD, suppBreve, leftWallSlack, Pi.add_apply, Pi.neg_apply]
    rw [add_comm t π]
    linarith
  change -((∫ t in Icc 0 π, f t ∂sigma P.cap) - (∫ t in Sι, f t * iFun P.cap t) +
      (∫ t in Ioo P.φ (π / 2), gB t ∂sigmaBreve (rightBody P.φ P.cap)) +
      (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t ∂sigmaBreve (leftBody P.φ P.cap))) = _
  rw [eI1, eI2, gm_sigmaBreve_B_restrict hP hbox, gm_sigmaBreve_D_restrict hP hbox]
  change -(_ - _ + _ + _) = (∫ t, rightWallSlack x t ∂β) + ∫ t, leftWallSlack x t ∂δ
  rw [eB, eD]
  ring

/-- Each nonnegative active-wall integral is at most the dual slack. -/
theorem active_integrals_le_slack {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    0 ≤ (∫ t, rightWallSlack x t ∂activeMeasureB P) ∧
    (∫ t, rightWallSlack x t ∂activeMeasureB P) ≤ wideDualSlack hP hbox x ∧
    0 ≤ (∫ t, leftWallSlack x t ∂activeMeasureD P) ∧
    (∫ t, leftWallSlack x t ∂activeMeasureD P) ≤ wideDualSlack hP hbox x := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hB : 0 ≤ ∫ t, rightWallSlack x t ∂activeMeasureB P :=
    setIntegral_nonneg measurableSet_Ico fun t ht =>
      rightWallSlack_nonneg x ⟨hpc.le.trans ht.1, ht.2.le⟩
  have hD : 0 ≤ ∫ t, leftWallSlack x t ∂activeMeasureD P :=
    setIntegral_nonneg measurableSet_Ioc fun t ht =>
      leftWallSlack_nonneg x ⟨ht.1.le, ht.2.trans hdT.le⟩
  rw [wideDualSlack_eq_active_integrals hP hbox]
  exact ⟨hB, by linarith, hD, by linarith⟩

/-- A positive density does not hide a nonzero continuous wall gap. -/
theorem continuous_zero_from_positive_density {a b : ℝ} (hab : a < b)
    {I : Set ℝ} (hI : I = Ico a b ∨ I = Ioc a b)
    {f : ℝ → ℝ} (hf : Continuous f) {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (hpositive : ∀ᵐ t ∂volume.restrict I, w t ≠ 0)
    (hzero : f =ᵐ[(volume.restrict I).withDensity w] 0) :
    EqOn f (fun _ => 0) (Icc a b) := by
  rw [EventuallyEq, ae_withDensity_iff hw] at hzero
  have he : f =ᵐ[volume.restrict I] 0 := by
    filter_upwards [hzero, hpositive] with t hz hp
    exact hz hp
  have hreg : I ⊆ closure (interior I) := by
    rcases hI with rfl | rfl <;>
      simp only [interior_Ico, interior_Ioc, closure_Ioo hab.ne] <;>
      exact fun _ h => ⟨h.1.le, h.2.le⟩
  have hon : EqOn f (fun _ => 0) I :=
    Measure.eqOn_of_ae_eq he hf.continuousOn continuousOn_const hreg
  have hc : IsClosed {t : ℝ | f t = 0} := isClosed_eq hf continuous_const
  have hsub : closure I ⊆ {t : ℝ | f t = 0} := closure_minimal hon hc
  have hcl : closure I = Icc a b := by
    rcases hI with rfl | rfl
    · exact closure_Ico hab.ne
    · exact closure_Ioc hab.ne
  rw [hcl] at hsub
  exact hsub

/-- The whole critical face, derived from the actual surface-area densities. -/
theorem zero_dual_slack_profiles {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (hzero : wideDualSlack hP hbox x = 0) :
    (∀ t ∈ Icc (criticalLeft P) (π / 2), rightWallSlack x t = 0) ∧
      (∀ t ∈ Icc (π / 2) (criticalRight P), leftWallSlack x t = 0) := by
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  obtain ⟨hB0, hB, hD0, hD⟩ := active_integrals_le_slack hP hbox x
  rw [hzero] at hB hD
  have hBint := (activeMeasures_integrable hP hbox (rightWallSlack_continuous x)).1
  have hDint := (activeMeasures_integrable hP hbox (leftWallSlack_continuous x)).2
  have hBae : rightWallSlack x =ᵐ[activeMeasureB P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ico fun t ht =>
        rightWallSlack_nonneg x ⟨hpc.le.trans ht.1, ht.2.le⟩) hBint).mp (hB.antisymm hB0)
  have hDae : leftWallSlack x =ᵐ[activeMeasureD P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
        leftWallSlack_nonneg x ⟨ht.1.le, ht.2.trans hdT.le⟩) hDint).mp (hD.antisymm hD0)
  rw [activeMeasureB, gm_prop844_two hP hbox] at hBae
  rw [activeMeasureD, gm_prop844_four hP hbox] at hDae
  constructor
  · apply continuous_zero_from_positive_density (by linarith) (Or.inl rfl)
      (rightWallSlack_continuous x) gm_measurable_rhoB _ hBae
    apply gm_ae_restrict_of_countable measurableSet_Ico
      ((countable_singleton (criticalLeft P)).insert (π / 2 - P.φ))
    intro t ht hne
    have hc : t ≠ criticalLeft P := fun he => hne (Or.inr he)
    have hj : t ≠ π / 2 - P.φ := fun he => hne (Or.inl he)
    obtain ⟨c, hcneg, hder⟩ := (theorem8_4_1_tangents hP hbox).1 t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hc), ht.2⟩ hj
    have hrho : 0 < dot (-deriv P.curveB t) (vvec t) := by
      rw [hder.deriv, dot_neg_left, dot_smul_left, dot_vvec_self, mul_one]
      linarith
    exact (ENNReal.ofReal_pos.mpr hrho).ne'
  · apply continuous_zero_from_positive_density hvd (Or.inr rfl)
      (leftWallSlack_continuous x) gm_measurable_rhoD _ hDae
    apply gm_ae_restrict_of_countable measurableSet_Ioc
      ((countable_singleton (criticalRight P)).insert (π / 2 + P.φ))
    intro t ht hne
    have hc : t ≠ criticalRight P := fun he => hne (Or.inr he)
    have hj : t - π / 2 ≠ P.φ := by
      intro he
      apply hne
      left
      linarith
    obtain ⟨c, hcpos, hder⟩ := (theorem8_4_1_tangents hP hbox).2.1 (t - π / 2)
      ⟨by linarith [ht.1], by
        have hlt := lt_of_le_of_ne ht.2 hc
        unfold criticalRight at hlt
        linarith⟩ hj
    have hrho : 0 < dot (deriv P.curveD (t - π / 2)) (uvec (t - π / 2)) := by
      rw [hder.deriv, dot_smul_left, dot_uvec_self, mul_one]
      exact hcpos
    exact (ENNReal.ofReal_pos.mpr hrho).ne'

end MovingSofaQuantitative
