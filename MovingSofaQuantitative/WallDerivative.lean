module

public import MovingSofaQuantitative.AuxiliaryProfileBounds
public import MovingSofaQuantitative.EndpointAveraging

/-!
# Short-interval derivatives of the actual wall slacks

Uncompiled proof source. The residual energy is shared: the cap and one
auxiliary body together spend at most Delta. The pointwise inequality
(u+r+s)^2 <= 3(u^2+r^2+s^2) then gives 60 Delta on a length-1/8
interval, which is stronger than the 64 Delta needed by endpoint averaging.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability GerverParams

namespace MovingSofaQuantitative

/-- A convenient L2 budget with no differentiability assumption on the residuals. -/
theorem short_three_term_energy {a b Δ : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 1 / 8)
    (hΔ : 0 ≤ Δ) {u r s d : ℝ → ℝ} (hu : ContinuousOn u (Icc a b))
    (huBound : ∀ t ∈ Icc a b, |u t| ≤ 12 * sqrt Δ)
    (hr : IntervalIntegrable r volume a b) (hs : IntervalIntegrable s volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hs2 : IntervalIntegrable (fun t => s t ^ 2) volume a b)
    (hbudget : arcSquare a b r + arcSquare a b s ≤ 2 * Δ)
    (heq : EqOn d (fun t => u t + r t + s t) (Ioo a b)) :
    IntervalIntegrable d volume a b ∧
      IntervalIntegrable (fun t => d t ^ 2) volume a b ∧ arcSquare a b d ≤ 64 * Δ := by
  have hui := hu.intervalIntegrable_of_Icc hab
  have hui2 := (hu.pow 2).intervalIntegrable_of_Icc hab
  let μ := volume.restrict (Ioo a b)
  have huμ : Integrable u μ := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hui
  have hrμ : Integrable r μ := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hr
  have hsμ : Integrable s μ := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hs
  have huLp : MemLp u 2 μ := (memLp_two_iff_integrable_sq huμ.aestronglyMeasurable).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hui2)
  have hrLp : MemLp r 2 μ := (memLp_two_iff_integrable_sq hrμ.aestronglyMeasurable).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hr2)
  have hsLp : MemLp s 2 μ := (memLp_two_iff_integrable_sq hsμ.aestronglyMeasurable).mpr
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hs2)
  have hsumLp : MemLp (fun t => u t + r t + s t) 2 μ := (huLp.add hrLp).add hsLp
  have hsum2 : IntervalIntegrable (fun t => (u t + r t + s t) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
      ((memLp_two_iff_integrable_sq hsumLp.aestronglyMeasurable).mp hsumLp)
  have hd := intervalIntegrable_of_eqOn_Ioo hab ((hui.add hr).add hs) heq
  have hd2 := intervalIntegrable_of_eqOn_Ioo hab hsum2
    (fun t ht => by rw [heq ht])
  refine ⟨hd, hd2, ?_⟩
  have huSq : ∀ t ∈ Icc a b, u t ^ 2 ≤ 144 * Δ := by
    intro t ht
    have hh := sq_le_sq₀ (abs_nonneg (u t)) (by positivity) |>.mpr (huBound t ht)
    simpa only [sq_abs, mul_pow, sq_sqrt hΔ, show (12 : ℝ) ^ 2 = 144 by norm_num] using hh
  have hUint := intervalIntegral.integral_mono_on hab hui2 intervalIntegrable_const huSq
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hUint
  have hpoint : ∀ t ∈ Icc a b,
      (u t + r t + s t) ^ 2 ≤ 3 * (u t ^ 2 + r t ^ 2 + s t ^ 2) := by
    intro t _
    nlinarith [sq_nonneg (u t - r t), sq_nonneg (u t - s t), sq_nonneg (r t - s t)]
  have hint := intervalIntegral.integral_mono_on hab hsum2
    (((hui2.add hr2).add hs2).const_mul 3) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hui2.add hr2) hs2,
    intervalIntegral.integral_add hui2 hr2] at hint
  have heIntegral : arcSquare a b d = ∫ t in a..b, (u t + r t + s t) ^ 2 :=
    intervalIntegral_eq_of_eqOn_Ioo hab (fun t ht => by rw [heq ht])
  have hscaled := mul_le_mul_of_nonneg_right hlen (by positivity : 0 ≤ 144 * Δ)
  unfold arcSquare at hbudget
  rw [heIntegral]
  nlinarith only [hint, hUint, hscaled, hbudget, hΔ]

/-- Integral of a nonnegative function on a subinterval is bounded by the full integral. -/
theorem nonnegative_integral_subinterval {a b c d : ℝ} {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume a b) (hf : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (∫ t in c..d, f t) ≤ ∫ t in a..b, f t := by
  have h1 := intervalIntegrable_subinterval hi le_rfl hac (hcd.trans hdb)
  have h2 := intervalIntegrable_subinterval hi hac hcd hdb
  have h3 := intervalIntegrable_subinterval hi (hac.trans hcd) hdb le_rfl
  have hsum : (∫ t in a..c, f t) + (∫ t in c..d, f t) + (∫ t in d..b, f t) =
      ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_add_adjacent_intervals h1 h2,
      intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3]
  have hn1 := intervalIntegral.integral_nonneg hac (fun t ht => hf t ⟨ht.1, ht.2.trans (hcd.trans hdb)⟩)
  have hn3 := intervalIntegral.integral_nonneg hdb (fun t ht => hf t ⟨(hac.trans hcd).trans ht.1, ht.2⟩)
  linarith

/-- Two actual residual components share, rather than each duplicate, the full deficit. -/
theorem cap_auxiliary_subarc_budget {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) {a b : ℝ}
    (hab : a ≤ b) :
    (P.φ ≤ a → b ≤ π / 2 - P.φ →
      arcSquare a b (cornerResidual (capDifference P.cap x.1.1.1)
        (capDifferenceDeriv P.cap x.1.1.1)) +
      arcSquare a b (rightAuxiliaryResidual hP hbox x) ≤ 2 * qDeficit P x) ∧
    (π / 2 ≤ a → b ≤ π - P.φ →
      arcSquare a b (tangentResidual π (capDifference P.cap x.1.1.1)
        (capDifferenceDeriv P.cap x.1.1.1)) +
      arcSquare a b (leftAuxiliaryResidual hP hbox x) ≤ 2 * qDeficit P x) := by
  let f := capDifference P.cap x.1.1.1
  let df := capDifferenceDeriv P.cap x.1.1.1
  have hf := tripleResidualData hP hbox x
  have henergy := (capDifference_data (gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox).1.1 x.1.1 (wideGerverTriple hP hbox).2.1 x.2.1).2
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hn1 := arcSquare_nonneg hp.le (tangentResidual (π / 2) f df)
  have hn2 := arcSquare_nonneg (hpc.le.trans hcb.le) (cornerResidual f df)
  have hn3 := arcSquare_nonneg hb.le (tangentResidual (π - P.φ) f df)
  have hn4 := arcSquare_nonneg (by linarith [pi_pos] : π / 2 ≤ π) (tangentResidual π f df)
  have hparts := q_energy_component_bounds hP hbox x
  unfold fourResidualEnergy at henergy
  constructor
  · intro ha hb'
    have hcap := arcSquare_mono hf.middle_sq ha hab hb'
    have haux := arcSquare_mono (rightAuxiliary_data hP hbox x).2.2.2.1
      ha hab (hb'.trans hb.le)
    rw [(rightAuxiliary_data hP hbox x).2.2.2.2] at haux
    linarith [hparts.2.2.2.1]
  · intro ha hb'
    have hcap := arcSquare_mono hf.last_sq ha hab (hb'.trans hTp.le)
    have haux := arcSquare_mono (leftAuxiliary_data hP hbox x).2.2.2.1 ha hab hb'
    rw [(leftAuxiliary_data hP hbox x).2.2.2.2] at haux
    linarith [hparts.2.2.2.2]

/-- Transfer a right derivative through equality on a one-sided neighborhood. -/
theorem rightDeriv_of_eqOn_interval {a b t : ℝ} {f g : ℝ → ℝ} {d : ℝ}
    (ht : t ∈ Ico a b) (he : EqOn f g (Icc a b))
    (hg : HasDerivWithinAt g d (Ioi t) t) : HasDerivWithinAt f d (Ioi t) t := by
  apply hg.congr_of_eventuallyEq _ (he ⟨ht.1, ht.2.le⟩)
  have hnb : Iio b ∈ 𝓝[Ioi t] t := mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds ht.2)
  filter_upwards [self_mem_nhdsWithin, hnb] with u hu hub
  exact he ⟨ht.1.trans hu.le, hub.le⟩

def rightWallDerivative {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (t : ℝ) : ℝ :=
  -capDifferenceDeriv P.cap x.1.1.1 t - rightAuxiliaryDerivative hP hbox x t

def leftWallDerivative {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (t : ℝ) : ℝ :=
  -capDifferenceDeriv P.cap x.1.1.1 t - leftAuxiliaryDerivative hP hbox x t

theorem rightWallDerivative_hasDeriv {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Ico (criticalLeft P) (π / 2)) :
    HasDerivWithinAt (rightWallSlack x) (rightWallDerivative hP hbox x t) (Ioi t) t := by
  have hf := tripleResidualData hP hbox x
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  apply rightDeriv_of_eqOn_interval ht (g := fun u =>
    -capDifference P.cap x.1.1.1 u - rightAuxiliaryProfile hP hbox x u)
  · intro u hu
    have he := rightProfile_on_active hP hbox x hu
    linarith
  · exact (hf.rightDeriv t ⟨(hp.trans hpc).trans_le ht.1, by linarith [ht.2, pi_pos]⟩).neg.sub
      ((rightAuxiliary_data hP hbox x).2.1 t)

theorem leftWallDerivative_hasDeriv {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Ico (π / 2) (criticalRight P)) :
    HasDerivWithinAt (leftWallSlack x) (leftWallDerivative hP hbox x t) (Ioi t) t := by
  have hf := tripleResidualData hP hbox x
  obtain ⟨hp, hpc, hcb, hb, hvd, hdT, hTp⟩ := critical_arc_order hP
  apply rightDeriv_of_eqOn_interval ht (g := fun u =>
    -capDifference P.cap x.1.1.1 u - leftAuxiliaryProfile hP hbox x u)
  · intro u hu
    have he := leftProfile_on_active hP hbox x hu
    linarith
  · exact (hf.rightDeriv t ⟨by linarith [ht.1, pi_pos], ht.2.trans (hdT.trans hTp)⟩).neg.sub
      ((leftAuxiliary_data hP hbox x).2.1 t)

/-- The right endpoint interval lies in the middle cap arc. -/
theorem right_wall_derivative_energy {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) {a b : ℝ}
    (ha : criticalLeft P ≤ a) (hab : a ≤ b) (hb : b ≤ criticalLeft P + 1 / 8) :
    IntervalIntegrable (rightWallDerivative hP hbox x) volume a b ∧
    IntervalIntegrable (fun t => rightWallDerivative hP hbox x t ^ 2) volume a b ∧
    arcSquare a b (rightWallDerivative hP hbox x) ≤ 64 * qDeficit P x := by
  let f := capDifference P.cap x.1.1.1
  let B := rightAuxiliaryProfile hP hbox x
  let u := fun t => tan t * B t - f (t + π / 2)
  have hloc := endpoint_short_arc_locations hP hbox
  obtain ⟨hp, hpc, hcb, hbot, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hpa : P.φ ≤ a := hpc.le.trans ha
  have hbb : b ≤ π / 2 - P.φ := hb.trans hloc.1.le
  have hbc : b ≤ 51 / 50 := hb.trans hloc.2.1.le
  have hcos : ∀ t ∈ Icc a b, cos t ≠ 0 := by
    intro t ht
    have he := short_cos_lower ⟨hp.le.trans (hpa.trans ht.1), ht.2.trans hbc⟩
    linarith
  have hf := tripleResidualData hP hbox x
  have hB := rightAuxiliary_data hP hbox x
  have hu : ContinuousOn u (Icc a b) :=
    ((continuous_sin.continuousOn.div continuous_cos.continuousOn hcos).mul hB.1.continuousOn).sub
      (hf.continuous.comp (continuous_id.add continuous_const)).continuousOn
  have hbound : ∀ t ∈ Icc a b, |u t| ≤ 12 * sqrt (qDeficit P x) := by
    intro t ht
    have htan := short_tan_bounds ⟨hp.le.trans (hpa.trans ht.1), ht.2.trans hbc⟩
    have hBv := rightAuxiliaryProfile_bound hP hbox x ⟨hpa.trans ht.1, ht.2.trans hb⟩
    have hfv := last_cap_profile_bound hP hbox x (t := t + π / 2)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm := mul_le_mul (show |tan t| ≤ 2 by rwa [abs_of_nonneg htan.1]) hBv
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hh := abs_sub (tan t * B t) (f (t + π / 2))
    rw [abs_mul] at hh
    dsimp [u]
    nlinarith only [hh, hm, hfv, sqrt_nonneg (qDeficit P x)]
  apply short_three_term_energy hab (by linarith) (q_energy_component_bounds hP hbox x).1 hu hbound
    (intervalIntegrable_subinterval hf.middle hpa hab hbb)
    (intervalIntegrable_subinterval hB.2.2.1 hpa hab (hbb.trans hbot.le))
    (intervalIntegrable_subinterval hf.middle_sq hpa hab hbb)
    (intervalIntegrable_subinterval hB.2.2.2.1 hpa hab (hbb.trans hbot.le))
    ((cap_auxiliary_subarc_budget hP hbox x hab).1 hpa hbb)
  intro t ht
  have htop := (auxiliaryProfile_contacts hP hbox x).1
  unfold rightWallDerivative rightAuxiliaryResidual tangentResidual cornerResidual u
  rw [htop, zero_sub, cos_pi_div_two_sub, sin_pi_div_two_sub, tan_eq_sin_div_cos]
  ring

/-- The left active interval is contained in the last cap arc. -/
theorem left_wall_derivative_energy {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) {a b : ℝ}
    (ha : criticalRight P - 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ criticalRight P) :
    IntervalIntegrable (leftWallDerivative hP hbox x) volume a b ∧
    IntervalIntegrable (fun t => leftWallDerivative hP hbox x t ^ 2) volume a b ∧
    arcSquare a b (leftWallDerivative hP hbox x) ≤ 64 * qDeficit P x := by
  let f := capDifference P.cap x.1.1.1
  let D := leftAuxiliaryProfile hP hbox x
  let u := fun t => -(cos t / sin t) * f t +
    f (π - P.φ) / sin (π - P.φ - t) + (cos (π - P.φ - t) / sin (π - P.φ - t)) * D t
  have hloc := endpoint_short_arc_locations hP hbox
  obtain ⟨hp, hpc, hcb, hbot, hvd, hdT, hTp⟩ := critical_arc_order hP
  have hva : π / 2 ≤ a := hloc.2.2.1.le.trans ha
  have hbT : b ≤ π - P.φ := hb.trans hdT.le
  have hs : ∀ t ∈ Icc a b, sin t ≠ 0 ∧ sin (π - P.φ - t) ≠ 0 := by
    intro t ht
    obtain ⟨h1, h2⟩ := active_sine_bounds hP hbox ⟨hva.trans ht.1, ht.2.trans hb⟩
    constructor <;> linarith
  have hf := tripleResidualData hP hbox x
  have hD := leftAuxiliary_data hP hbox x
  have hu : ContinuousOn u (Icc a b) := by
    apply ContinuousOn.add
    · exact ((continuous_cos.continuousOn.div continuous_sin.continuousOn
        (fun t ht => (hs t ht).1)).neg.mul hf.continuous.continuousOn).add
        (continuousOn_const.div (by fun_prop) (fun t ht => (hs t ht).2))
    · exact ((show ContinuousOn (fun t => cos (π - P.φ - t)) (Icc a b) by fun_prop).div
        (by fun_prop) (fun t ht => (hs t ht).2)).mul hD.1.continuousOn
  have hbound : ∀ t ∈ Icc a b, |u t| ≤ 12 * sqrt (qDeficit P x) := by
    intro t ht
    have htv : t ∈ Icc (π / 2) (criticalRight P) := ⟨hva.trans ht.1, ht.2.trans hb⟩
    obtain ⟨hc, hcT, hsT⟩ := active_cot_bounds hP hbox htv
    have hf1 := last_cap_profile_bound hP hbox x ⟨htv.1, htv.2.trans (hdT.le.trans hTp.le)⟩
    have hfT := last_cap_profile_bound hP hbox x (t := π - P.φ)
      ⟨hvd.le.trans hdT.le, hTp.le⟩
    have hDv := leftAuxiliaryProfile_bound hP hbox x htv
    have hsT' : |1 / sin (π - P.φ - t)| ≤ 2 := by
      rw [abs_of_nonneg (by have hh := (active_sine_bounds hP hbox htv).2; positivity)]
      exact hsT
    have h1 := mul_le_mul hc hf1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul hsT' hfT (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have h3 := mul_le_mul hcT hDv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hh := (abs_add_le (-(cos t / sin t) * f t + f (π - P.φ) / sin (π - P.φ - t))
      ((cos (π - P.φ - t) / sin (π - P.φ - t)) * D t)).trans
      (add_le_add_right (abs_add_le _ _) _)
    simp only [abs_mul, abs_neg, abs_div, one_div] at hh h1 h2 h3
    dsimp [u]
    nlinarith only [hh, h1, h2, h3]
  apply short_three_term_energy hab (by linarith) (q_energy_component_bounds hP hbox x).1 hu hbound
    (intervalIntegrable_subinterval hf.last hva hab (hbT.trans hTp.le))
    (intervalIntegrable_subinterval hD.2.2.1 hva hab hbT)
    (intervalIntegrable_subinterval hf.last_sq hva hab (hbT.trans hTp.le))
    (intervalIntegrable_subinterval hD.2.2.2.1 hva hab hbT)
    ((cap_auxiliary_subarc_budget hP hbox x hab).2 hva hbT)
  intro t ht
  have hcut := (auxiliaryProfile_contacts hP hbox x).2.2.2
  rw [tangentResidual_left hf.left_zero]
  unfold leftWallDerivative leftAuxiliaryResidual tangentResidual u
  rw [hcut]
  dsimp [D, f]
  ring

end MovingSofaQuantitative
