module

public import MovingSofaQuantitative.ReferenceReflection
public import MovingSofaQuantitative.EndpointGapControl
public import MovingSofaQuantitative.DualSlack

/-!
# The active inner curve remains feasible under a matched support perturbation

Uncompiled proof source. Positive reference curvature, the strict outer-cap
margin, and the weighted inactive-wall gap give one amplitude valid over every
angle. The compactness used here bounds a fixed scalar trial profile; it is not
an assumed neighborhood theorem for arbitrary moving sofas.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology MeasureTheory
open MovingSofaOptimality MovingSofaStability MovingSofaOptimality.GerverParams

namespace MovingSofaQuantitative

theorem contactB_eq_contactA_sub (P : GerverParams) (t : ℝ) :
    contactB P.path t=contactA P.path t-uvec t := by
  unfold contactB contactA
  abel

def perturbedInnerCurve (P : GerverParams) (F : HalfCapProfile P.φ) (τ t : ℝ) : Point :=
  contactB P.path t+τ • F.rightOffset t

def perturbedInnerDensity (P : GerverParams) (F : HalfCapProfile P.φ) (τ t : ℝ) : ℝ :=
  1-outerDensityR P t-τ*(F.secondR t+F.value t)

theorem perturbedInnerCurve_continuous {P : GerverParams} (hP : P.IsSolution)
    (F : HalfCapProfile P.φ) (τ : ℝ) : Continuous (perturbedInnerCurve P F τ) :=
  (gs_continuous_contactB hP).add (F.rightOffset_continuous.const_smul τ)

theorem perturbedInnerCurve_derivative {P : GerverParams} (hP : P.IsSolution)
    (F : HalfCapProfile P.φ) (τ t : ℝ) :
    HasDerivWithinAt (perturbedInnerCurve P F τ)
      (-(perturbedInnerDensity P F τ t) • vvec t) (Ici t) t := by
  have hB := (gs_hasDerivWithinAt_contactA hP (gs_rpiece_ridx t)).sub
    (hasDerivAt_uvec t).hasDerivWithinAt
  have hF := (F.rightOffset_derivative t).const_smul τ
  convert hB.add hF using 1
  · funext u
    rw [perturbedInnerCurve,contactB_eq_contactA_sub]
  · simp only [perturbedInnerDensity,outerDensityR,neg_sub,sub_smul,
      add_smul,mul_smul,one_smul]
    abel

/-- On the active B arc the reference inner curve turns with a positive reserve. -/
theorem active_inner_density_margin {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {t : ℝ} (ht : t∈Icc (π/2-P.θ) (π/2)) : outerDensityR P t ≤ 7/8 := by
  have hO := gs_ord hP
  have hB := romik_bounds hP hbox
  have hb : -(528/1000 : ℝ) ≤ P.b₁ := by linarith [hB.b₁_mem.1]
  have hθ : P.θ ≤ 682/1000 := by linarith [hB.θ_mem.2]
  have hn0 : ¬t<P.φ := by linarith [ht.1,hO.2.1,hO.2.2]
  have hn1 : ¬t<P.θ := by linarith [ht.1,hO.2.2]
  have hn2 : ¬t<π/2-P.θ := not_lt.mpr ht.1
  unfold outerDensityR gs_ridx
  simp only [if_neg hn0,if_neg hn1,if_neg hn2]
  by_cases hn3 : t<π/2-P.φ
  · simp only [if_pos hn3,gs_ρA₄_eq' hP]
    linarith [ht.1]
  · simp only [if_neg hn3,gs_ρA₅_eq hP]
    norm_num

theorem perturbedInnerDensity_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ t : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude)
    (ht : t∈Icc (π/2-P.θ) (π/2)) : 0 ≤ perturbedInnerDensity P F τ t := by
  have hO := gs_ord hP
  have href := active_inner_density_margin hP hbox ht
  have hF := F.central_right t ⟨by linarith [ht.1,hO.2.1,hO.2.2],ht.2⟩
  have hm := mul_le_mul_of_nonneg_left (abs_le.mp hF).2 hτ
  have hA := F.amplitude_curvature hτ hsmall
  unfold perturbedInnerDensity
  linarith

theorem perturbedInnerCurve_floor_end {P : GerverParams} (hP : P.IsSolution)
    (F : HalfCapProfile P.φ) (τ : ℝ) : (perturbedInnerCurve P F τ (π/2)).2=0 := by
  simp only [perturbedInnerCurve,Prod.snd_add,Prod.smul_snd,smul_eq_mul,
    gs_contactB_pi_div_two_snd hP,HalfCapProfile.rightOffset,F.top_zero,zero_smul,
    zero_add,Prod.smul_snd,vvec,cos_pi_div_two,mul_zero,add_zero]

theorem perturbedInnerCurve_above_floor {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ) {τ t : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ F.safeAmplitude)
    (ht : t∈Icc (π/2-P.θ) (π/2)) : 0 ≤ (perturbedInnerCurve P F τ t).2 := by
  have hO := gs_ord hP
  have h := le_of_right_deriv_nonpos ht.2
    ((perturbedInnerCurve_continuous hP F τ).snd.continuousOn)
    (fun u hu => (perturbedInnerCurve_derivative hP F τ u).snd.mono Ioi_subset_Ici_self)
    (fun u hu => by
      have hd := perturbedInnerDensity_nonneg hP hbox F hτ hsmall
        ⟨ht.1.trans hu.1,hu.2.le⟩
      have hc : 0 ≤ cos u := cos_nonneg_of_mem_Icc
        ⟨by linarith [hu.1,ht.1,hO.2.2,pi_pos],hu.2.le⟩
      simpa only [Prod.smul_snd,smul_eq_mul,vvec] using
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hc)
  rw [perturbedInnerCurve_floor_end hP F τ] at h
  exact h

theorem gerver_closed_niche_margin {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ μ : ℝ, 0<μ ∧ ∀ p∈closure(niche P.cap (π/2)), ∀ s∈Icc (0 : ℝ) π,
      μ ≤ supp P.cap s-dot p (uvec s) := by
  obtain ⟨H,L,γ,hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨μ,hμ,hmargin⟩ := hroof.outer_margin
  refine ⟨μ,hμ,?_⟩
  intro p hp s hs
  have hsub : closure(niche P.cap (π/2)) ⊆ {q | μ ≤ supp P.cap s-dot q (uvec s)} :=
    closure_minimal (fun q hq => hmargin q hq s hs)
      (isClosed_le continuous_const (by unfold dot; fun_prop))
  exact hsub hp

theorem HalfCapProfile.bridge_projection {φ c : ℝ} (F : HalfCapProfile φ)
    (hs : sin(c-φ) ≠ 0)
    (hjet : F.first c=harmonicBridgeFirst φ c (F.value φ) (F.value c) c) (t : ℝ) :
    dot (F.rightOffset c) (uvec t)=harmonicBridge φ c (F.value φ) (F.value c) t := by
  have hcc : dot (F.rightOffset c) (uvec c)=F.value c := by
    simp [HalfCapProfile.rightOffset,dot_add_left,dot_smul_left]
  have hφc : dot (F.rightOffset c) (uvec φ)=F.value φ := by
    rw [HalfCapProfile.rightOffset,dot_add_left,dot_smul_left,dot_smul_left,hjet]
    simp only [harmonicBridgeFirst,sub_self,cos_zero,mul_one]
    have hu : dot (uvec c) (uvec φ)=cos(c-φ) := by simp [dot,uvec,cos_sub]; ring
    have hv : dot (vvec c) (uvec φ)=-sin(c-φ) := by simp [dot,uvec,vvec,sin_sub]; ring
    rw [hu,hv]
    field_simp [hs]
    ring
  have hcomb := dot_uvec_comb (F.rightOffset c) φ c t
  rw [hφc,hcc] at hcomb
  unfold harmonicBridge
  apply (eq_div_iff hs).mpr
  linarith

/-- The explicit amplitude proof is bound as an argument, so no proof term is
implicitly obtained from the left side of a conjunction. -/
theorem exists_perturbed_active_arc {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (F : HalfCapProfile P.φ)
    (hjet : F.first (π/2-P.θ)=harmonicBridgeFirst P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) (π/2-P.θ)) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ τ₀≤F.safeAmplitude ∧
      ∀ (τ : ℝ) (hτ : 0≤τ) (hτ₀ : τ≤τ₀) (hsafe : τ≤F.safeAmplitude),
      ∃ D : ActiveArcData P.φ (π/2-P.θ)
          (perturbedCap hP hbox F τ hτ hsafe).1,
        D.curve=perturbedInnerCurve P F τ := by
  have hO := gs_ord hP
  have hφc : P.φ<π/2-P.θ := by linarith [hO.2.1,hO.2.2]
  have hcv : π/2-P.θ<π/2 := by linarith [hO.1,hO.2.1]
  have hs : sin((π/2-P.θ)-P.φ) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (sub_pos.mpr hφc) (by linarith [pi_pos])).ne'
  obtain ⟨B,hB,hgap⟩ := F.bridge_error_bound hO.1 hφc hcv hjet
  obtain ⟨μ,hμ,hmargin⟩ := gerver_closed_niche_margin hP hbox
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun t => norm2(F.rightOffset t))
    ((show Continuous (fun t => norm2(F.rightOffset t)) by unfold norm2 dot; fun_prop).continuousOn)
  obtain ⟨V,hV⟩ := isCompact_Icc.exists_bound_of_continuousOn F.continuous_value.continuousOn
  let L := 1+|R|+|V|
  have hL : 0<L := by dsimp [L]; positivity
  let τ₀ := min F.safeAmplitude (min (1/(250*B)) (μ/(2*L)))
  have hτ₀ : 0<τ₀ := lt_min F.safeAmplitude_pos (lt_min (by positivity) (by positivity))
  have hτsafe : τ₀≤F.safeAmplitude := min_le_left _ _
  refine ⟨τ₀,hτ₀,hτsafe,?_⟩
  intro τ hτ hsmall hcapSmall
  let K := perturbedCap hP hbox F τ hτ hcapSmall
  have hgapτ : τ*B≤1/250 := by
    have ht := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (show 0<250*B by positivity)).mp ht
    linarith
  have hτμ : τ*L≤μ/2 := by
    have ht := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (show 0<2*L by positivity)).mp ht
    linarith
  have hvalue : ∀ t∈Icc (0 : ℝ) π, |F.symmetricValue t|≤|V| := by
    intro t ht
    unfold HalfCapProfile.symmetricValue
    split_ifs with htv
    · exact (hV t ⟨ht.1,htv⟩).trans (le_abs_self _)
    · exact (hV (π-t) ⟨by linarith [ht.2],by linarith⟩).trans (le_abs_self _)
  have hoff : ∀ t∈Icc (π/2-P.θ) (π/2), norm2(F.rightOffset t)≤|R| := by
    intro t ht
    have hr := hR t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm2_nonneg _)] using hr.trans (le_abs_self R)
  have hcurveK : ∀ t∈Icc (π/2-P.θ) (π/2), perturbedInnerCurve P F τ t∈K.1 := by
    intro t ht
    apply (cap_mem_iff_upper (perturbedCap_isCap hP hbox F τ hτ hcapSmall) _).mpr
    refine ⟨perturbedInnerCurve_above_floor hP hbox F hτ hcapSmall ht,?_⟩
    intro s hsu
    have hmem := (theorem8_4_1_niche hP hbox).1 t ht
    have hm := hmargin _ hmem s hsu
    have hd := (dot_uvec_le_norm2 (F.rightOffset t) s).trans (hoff t ht)
    have hδ := (abs_le.mp (hvalue s hsu)).1
    have hmul := mul_le_mul_of_nonneg_left hd hτ
    have hmul' := mul_le_mul_of_nonneg_left hδ hτ
    rw [perturbedCap_support hP hbox F τ hτ hcapSmall hsu]
    simp only [perturbedInnerCurve,dot_add_left,dot_smul_left]
    dsimp [L] at hτμ
    linarith
  have hcontact : ∀ t∈Icc (π/2-P.θ) (π/2),
      dot (perturbedInnerCurve P F τ t) (uvec t)=supp K.1 t-1 := by
    intro t ht
    rw [perturbedCap_support hP hbox F τ hτ hcapSmall
      ⟨by linarith [ht.1,hO.2.2,pi_pos],by linarith [ht.2,pi_pos]⟩]
    rw [(gerver_support_path_pair hP hbox
      ⟨by linarith [ht.1,hO.2.2,pi_pos],ht.2⟩).1]
    simp only [perturbedInnerCurve,contactB,HalfCapProfile.rightOffset,
      HalfCapProfile.symmetricValue,if_pos ht.2,dot_add_left,dot_smul_left,
      dot_vvec_uvec,dot_uvec_self,mul_zero,mul_one,add_zero]
    ring
  have hgapactual : ∀ t∈Icc P.φ (π/2-P.θ),
      supp K.1 t-1≤dot (perturbedInnerCurve P F τ (π/2-P.θ)) (uvec t) := by
    intro t ht
    have htupper : t∈Icc (0 : ℝ) (π/2) := ⟨hO.1.le.trans ht.1,ht.2.trans hcv.le⟩
    have hg := referenceRightGap_lower hP hbox ht
    have hp := (le_abs_self (F.value t-harmonicBridge P.φ (π/2-P.θ)
      (F.value P.φ) (F.value (π/2-P.θ)) t)).trans (hgap t ht)
    have hweight : 0≤(t-P.φ)*(π/2-P.θ-t)^2 := mul_nonneg (sub_nonneg.mpr ht.1) (sq_nonneg _)
    have htau := mul_le_mul_of_nonneg_left hp hτ
    have hcoeff := mul_le_mul_of_nonneg_right hgapτ hweight
    rw [perturbedCap_support hP hbox F τ hτ hcapSmall
      ⟨htupper.1,by linarith [htupper.2,pi_pos]⟩,
      (gerver_support_path_pair hP hbox htupper).1]
    simp only [perturbedInnerCurve,dot_add_left,dot_smul_left,
      HalfCapProfile.symmetricValue,if_pos htupper.2]
    rw [F.bridge_projection hs hjet]
    unfold referenceRightGap at hg
    rw [dot_sub_left] at hg
    nlinarith only [hg,htau,hcoeff]
  have hcut : dot (perturbedInnerCurve P F τ (π/2-P.θ)) (uvec P.φ)=supp K.1 P.φ-1 := by
    rw [perturbedCap_support hP hbox F τ hτ hcapSmall
      ⟨hO.1.le,by linarith [hO.2.1,hO.2.2,pi_pos]⟩,
      (gerver_support_path_pair hP hbox ⟨hO.1.le,by linarith [hO.2.1,hO.2.2,pi_pos]⟩).1]
    simp only [perturbedInnerCurve,gs_contactB_t₃ hP,dot_add_left,dot_smul_left,
      HalfCapProfile.symmetricValue,if_pos (show P.φ≤π/2 by linarith [hO.2.1,hO.2.2,pi_pos])]
    rw [F.bridge_projection hs hjet,(harmonicBridge_endpoints hs).1]
    ring
  refine ⟨⟨perturbedCap_isCap hP hbox F τ hτ hcapSmall,
    ⟨hO.1,hφc,hcv⟩,perturbedInnerCurve P F τ,perturbedInnerDensity P F τ,
    (perturbedInnerCurve_continuous hP F τ).continuousOn,
    (fun t _ => perturbedInnerCurve_derivative hP F τ t),
    (fun t ht => perturbedInnerDensity_nonneg hP hbox F hτ hcapSmall ⟨ht.1,ht.2.le⟩),
    hcurveK,hcontact,hgapactual,hcut⟩,rfl⟩

end MovingSofaQuantitative
