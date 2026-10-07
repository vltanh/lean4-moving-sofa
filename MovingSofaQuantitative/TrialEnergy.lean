module

public import MovingSofaQuantitative.TrialSupport
public import MovingSofaQuantitative.AuxiliaryData

/-!
# Exact quadratic deficit of the continuously feasible trial

Uncompiled proof source. The comparison uses actual supports and their unique
right derivatives on the energy arcs. Mamikon's theorem supplies integrability.
The quadratic identity is exact for every admitted positive amplitude, not only
an asymptotic expansion or a Hessian inferred from samples.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- Equality of profiles on a closed interval fixes their right derivatives
at every interior point, independently of what happens outside the interval. -/
theorem rightDerivative_eq_of_interval {a b : ℝ} {f df g dg : ℝ→ℝ}
    (hf : ∀ t∈Ioo a b,HasDerivWithinAt f (df t) (Ioi t) t)
    (hg : ∀ t∈Ioo a b,HasDerivWithinAt g (dg t) (Ioi t) t)
    (he : EqOn f g (Icc a b)) {t : ℝ} (ht : t∈Ioo a b) : df t=dg t := by
  have hfg : HasDerivWithinAt g (df t) (Ioi t) t := by
    apply (hf t ht).congr_of_eventuallyEq
    · have hn : Ioo a b∈𝓝[Ioi t] t := mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)
      filter_upwards [hn] with u hu
      exact he (Ioo_subset_Icc_self hu)
    · exact he (Ioo_subset_Icc_self ht)
  exact hfg.unique (uniqueDiffWithinAt_Ioi t) (hg t ht)

/-- Pinning changes no cap residual energy. Endpoint singularities are removed
only by the open-arc integral identity, never by an improper integral. -/
theorem fourResidualEnergy_pinning {φ : ℝ} (hφ : φ∈Ioo (0 : ℝ) (π/4)) (f df : ℝ→ℝ) :
    fourResidualEnergy φ (pinnedDifference f) (pinnedDerivative f df)=fourResidualEnergy φ f df := by
  have arc {a b T : ℝ} (hab : a≤b) (hs : ∀ t∈Ioo a b,sin(T-t)≠0) :
      arcSquare a b (tangentResidual T (pinnedDifference f) (pinnedDerivative f df))=
      arcSquare a b (tangentResidual T f df) := by
    unfold arcSquare
    exact intervalIntegral_eq_of_eqOn_Ioo hab (fun t ht => by rw [tangentResidual_pinned T f df t (hs t ht)])
  unfold fourResidualEnergy
  rw [arc (a := 0) (b := φ) (T := π/2) hφ.1.le
      (fun t ht => (sin_pos_of_pos_of_lt_pi (by linarith [ht.2,hφ.2,pi_pos]) (by linarith [ht.1,pi_pos])).ne'),
    arc (a := π/2-φ) (b := π/2) (T := π-φ) (by linarith [hφ.1])
      (fun t ht => (sin_pos_of_pos_of_lt_pi (by linarith [ht.2,hφ.2,pi_pos]) (by linarith [ht.1])).ne'),
    arc (a := π/2) (b := π) (T := π) (by linarith [pi_pos])
      (fun t ht => (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1,pi_pos])).ne')]
  simp only [cornerResidual_pinned]

/-- The matched auxiliary profile is C1, including its active endpoint. -/
theorem trialAuxiliary_hasDeriv {φ c : ℝ} (F : HalfCapProfile φ)
    (hs : sin(c-φ)≠0)
    (hjet : F.first c=harmonicBridgeFirst φ c (F.value φ) (F.value c) c) (t : ℝ) :
    HasDerivAt (trialAuxiliaryProfile F c) (trialAuxiliaryDerivative F c t) t := by
  have hvalue := (harmonicBridge_endpoints (ya := F.value φ) (yb := F.value c) hs).2
  have he : trialAuxiliaryProfile F c=rightJoin c
      (fun t => -harmonicBridge φ c (F.value φ) (F.value c) t) (fun t => -F.value t) := by
    funext u
    unfold trialAuxiliaryProfile rightJoin
    split_ifs <;> try rfl
    · have hu : u=c := by linarith
      subst u
      rw [hvalue]
    · exfalso
      linarith
  rw [he]
  exact hasDerivAt_rightJoin
    (fun u => (harmonicBridge_derivative φ c (F.value φ) (F.value c) u).neg)
    (fun u => (F.derivative u).neg) (by rw [hvalue]) (by rw [hjet]) t

/-- Exact auxiliary energy when its genuine lower support difference is tau
 times a scalar profile. No cap or wall assumptions are hidden here. -/
theorem auxiliaryEnergy_of_profile (B₀ B₁ : ConvexBodySet) {a b T τ : ℝ}
    (hab : a<b) (hb : b<a+π) (haT : T-π<a) (hbT : b≤T)
    (hT : T∈Icc a b) {g dg : ℝ→ℝ}
    (hder : ∀ t∈Ioo a b,HasDerivWithinAt g (dg t) (Ioi t) t)
    (hsupport : ∀ t∈Icc a b,supp B₁.1 (π+t)-supp B₀.1 (π+t)=τ*g t) :
    displacementEnergy (π+a) (π+b) (fun B => tangentParam B.1 (π+T)) B₀ B₁ =
      (τ^2/2)*arcSquare a b (tangentResidual T g dg) := by
  let f := auxiliaryDifference B₀.1 B₁.1 0
  let df := auxiliaryDerivative B₀.1 B₁.1 0
  have hf : ∀ t∈Icc a b,f t=τ*g t := by
    intro t ht
    simpa only [f,auxiliaryDifference,zero_mul,sub_zero] using hsupport t ht
  have hd : ∀ t∈Ioo a b,df t=τ*dg t := by
    intro t ht
    exact rightDerivative_eq_of_interval
      (fun u _ => auxiliaryDifference_rightDeriv B₀ B₁ 0 u)
      (fun u hu => (hder u hu).const_mul τ) (fun u hu => hf u hu) ht
  have hr : ∀ t∈Ioo a b,tangentResidual T f df t=τ*tangentResidual T g dg t := by
    intro t ht
    unfold tangentResidual
    rw [hf T hT,hf t (Ioo_subset_Icc_self ht),hd t ht]
    ring
  have he := (auxiliaryResidual_data B₀ B₁ 0 hab hb haT hbT).2.2
  have hs := arcSquare_eq_smul_on hab.le hr
  change arcSquare a b (tangentResidual T f df)=_ at he
  rw [hs] at he
  linarith

/-- Scalar quadratic form associated with a symmetric half profile and its two
actual active-arc auxiliaries. All terms are the Mamikon residual energies. -/
def trialEnergy {φ : ℝ} (F : HalfCapProfile φ) (c : ℝ) : ℝ :=
  fourResidualEnergy φ F.symmetricValue F.symmetricDerivative +
    (1/2)*arcSquare φ (π/2)
      (tangentResidual (π/2) (trialAuxiliaryProfile F c) (trialAuxiliaryDerivative F c)) +
    (1/2)*arcSquare (π/2) (π-φ)
      (tangentResidual (π-φ) (fun t => trialAuxiliaryProfile F c (π-t))
        (fun t => -trialAuxiliaryDerivative F c (π-t)))

theorem trialEnergy_nonneg {φ : ℝ} (hφ : φ∈Ioo (0 : ℝ) (π/4))
    (F : HalfCapProfile φ) (c : ℝ) : 0≤trialEnergy F c := by
  unfold trialEnergy
  have h0 := fourResidualEnergy_nonneg' hφ F.symmetricValue F.symmetricDerivative
  have h1 := arcSquare_nonneg (by linarith [hφ.2,pi_pos] : φ≤π/2)
    (tangentResidual (π/2) (trialAuxiliaryProfile F c) (trialAuxiliaryDerivative F c))
  have h2 := arcSquare_nonneg (by linarith [hφ.2,pi_pos] : π/2≤π-φ)
    (tangentResidual (π-φ) (fun t => trialAuxiliaryProfile F c (π-t))
      (fun t => -trialAuxiliaryDerivative F c (π-t)))
  linarith

/-- Exact Q deficit for each continuously feasible trial amplitude. -/
theorem activeArc_trial_deficit {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ : ℝ} (hτ : 0<τ) (hsmall : τ≤F.safeAmplitude)
    (hjet : F.first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) (π/2-P.θ))
    (D : ActiveArcData P.φ (π/2-P.θ) (perturbedCap hP hbox F τ hτ.le hsmall).1)
    (hcurve : D.curve=perturbedInnerCurve P F τ) :
    qDeficit P (D.wideTriple (fun t ht => perturbedCap_reflection_support hP hbox F hτ.le hsmall ht))=
      τ^2*trialEnergy F (π/2-P.θ) := by
  let x := D.wideTriple (fun t ht => perturbedCap_reflection_support hP hbox F hτ.le hsmall ht)
  let B₀ := (wideGerverTriple hP hbox).1.2.1
  let B₁ := x.1.2.1
  let D₀ := (wideGerverTriple hP hbox).1.2.2
  let D₁ := x.1.2.2
  have hφ := gm_φ_mem_Ioo hP hbox
  have hO := gs_ord hP
  have hsin : sin((π/2-P.θ)-P.φ)≠0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith [hO.2.1,hO.2.2]) (by linarith [hO.1,pi_pos])).ne'
  have hB := auxiliaryEnergy_of_profile B₀ B₁
    (a := P.φ) (b := π/2) (T := π/2)
    (by linarith [hφ.2,pi_pos]) (by linarith [hφ.1,pi_pos]) (by linarith [hφ.1,pi_pos]) le_rfl
    ⟨by linarith [hφ.2,pi_pos],le_rfl⟩
    (fun t _ => (trialAuxiliary_hasDeriv F hsin hjet t).hasDerivWithinAt)
    (fun t ht => trial_B_support_difference hP hbox F hτ.le hsmall hjet D hcurve ht)
  have hD := auxiliaryEnergy_of_profile D₀ D₁
    (a := π/2) (b := π-P.φ) (T := π-P.φ)
    (by linarith [hφ.2,pi_pos]) (by linarith [hφ.1,pi_pos]) (by linarith [hφ.1,pi_pos]) le_rfl
    ⟨by linarith [hφ.2,pi_pos],le_rfl⟩
    (fun t _ => by
      convert ((trialAuxiliary_hasDeriv F hsin hjet (π-t)).comp t
        ((hasDerivAt_id t).const_sub π)).hasDerivWithinAt using 1 <;> ring)
    (fun t ht => trial_D_support_difference hP hbox F hτ.le hsmall hjet D hcurve ht)
  have hcap := (perturbedCap_data_energy hP hbox F hτ hsmall).2
  rw [HalfCapProfile.pinnedProfile,HalfCapProfile.pinnedProfileDerivative,
    fourResidualEnergy_pinning hφ] at hcap
  have hzero := activeArc_trial_zero_slack hP hbox F hτ.le hsmall D
  change qDeficit P x=_
  unfold qDeficit
  rw [wide_deficit_eq_slack_add_integrals hP hbox x,hzero,zero_add,wideResidualEnergy]
  change _ + displacementEnergy (π+P.φ) (3*π/2) (fun B => tangentParam B.1 (3*π/2)) B₀ B₁ +
    displacementEnergy (3*π/2) (π+(π-P.φ)) (fun B => tangentParam B.1 (π+(π-P.φ))) D₀ D₁ = _
  rw [show 3*π/2=π+π/2 by ring,hB,hD,hcap]
  unfold trialEnergy
  ring

end MovingSofaQuantitative
