module

public import MovingSofaQuantitative.EffectiveEntry
public import MovingSofaQuantitative.ExplicitStability
public import MovingSofaQuantitative.ExplicitReferenceScales

/-!
# The explicit 10^-600 cutoff

UNCOMPILED SOURCE.  This is the final proposition of Appendix G.

The coarse global entry theorem is used only to enter the fixed local support
and angle neighborhoods.  After entry, the sharper centered cap estimate,
terminal budget, Euclidean-normal recovery, whole-sector recovery, and direct
area comparison give the 2.3 / 50 / 3.1 conclusions.

No existential radius occurs in the theorem statement or in its final
activation hypotheses.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

theorem epsilonStar_pos : 0<Targets.epsilonStar := by
  norm_num [Targets.epsilonStar]

theorem epsilonStar_le_144 :
    Targets.epsilonStar≤1/(10:ℝ)^144 := by
  norm_num [Targets.epsilonStar]
  positivity

theorem epsilonStar_le_30 :
    Targets.epsilonStar≤1/(10:ℝ)^30 := by
  norm_num [Targets.epsilonStar]
  positivity

theorem epsilonStar_sqrt_bound {ε : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar) :
    sqrt ε≤1/(10:ℝ)^300 := by
  have hs:=sqrt_le_sqrt hstar
  have hcalc : sqrt Targets.epsilonStar=1/(10:ℝ)^300 := by
    unfold Targets.epsilonStar
    rw [show (10:ℝ)^600=((10:ℝ)^300)^2 by ring]
    rw [one_div,sqrt_inv,sqrt_sq_eq_abs,abs_of_pos (by positivity)]
  simpa [hcalc] using hs

theorem epsilonStar_twelfth_bound {ε : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar) :
    ε^(1/12:ℝ)≤1/(10:ℝ)^50 := by
  rcases hε.eq_or_lt with rfl|hp
  · norm_num
  · have hr:=rpow_le_rpow hε hstar (by norm_num : (0:ℝ)≤1/12)
    have hcalc :
        Targets.epsilonStar^(1/12:ℝ)=1/(10:ℝ)^50 := by
      unfold Targets.epsilonStar
      rw [div_rpow (by norm_num : (0:ℝ)≤1) (by positivity)]
      simp only [one_rpow]
      rw [←Real.rpow_natCast,←Real.rpow_mul (show (0:ℝ)≤10 by norm_num)]
      norm_num
    simpa [hcalc] using hr

theorem epsilonStar_sixth_bound {ε : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar) :
    ε^(1/6:ℝ)≤1/(10:ℝ)^100 := by
  rcases hε.eq_or_lt with rfl|hp
  · norm_num
  · have hr:=rpow_le_rpow hε hstar (by norm_num : (0:ℝ)≤1/6)
    have hcalc :
        Targets.epsilonStar^(1/6:ℝ)=1/(10:ℝ)^100 := by
      unfold Targets.epsilonStar
      rw [div_rpow (by norm_num : (0:ℝ)≤1) (by positivity)]
      simp only [one_rpow]
      rw [←Real.rpow_natCast,←Real.rpow_mul (show (0:ℝ)≤10 by norm_num)]
      norm_num
    simpa [hcalc] using hr

/-- The coarse entry theorem lands strictly inside the fixed 1e-40 support
neighborhood at the explicit cutoff. -/
theorem cutoff_global_entry_radius {ε : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar) :
    3000000*ε^(1/12:ℝ)<localSupportRadius := by
  have h12:=epsilonStar_twelfth_bound hε hstar
  unfold localSupportRadius
  nlinarith

/-- The coarse angle theorem lands strictly inside the fixed 1e-20 terminal
neighborhood. -/
theorem cutoff_angle_entry_radius {ε : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar) :
    500*ε^(1/6:ℝ)<localAngleRadius := by
  have h6:=epsilonStar_sixth_bound hε hstar
  unfold localAngleRadius
  nlinarith

/-- Fixed terminal certificate in the exact shape expected by LocalData, with
R=4 so that 4 R alpha = 16 alpha. -/
theorem cutoff_terminal_adapter {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∀ K : Set Point, IsCap K (π/2) →
      UpperSupportClose localSupportRadius K P.cap →
      ∀ S : Set Point, MeasurableSet S → ∀ ω∈Icc (0:ℝ) (π/2),
      π/2-ω≤localAngleRadius → PartialSofaConstraints K S ω →
      let U:=capShape K
      let ε:=area (gerverSofa P)-area S
      let e:=area (gerverSofa P)-area U
      0≤e ∧ e≤ε ∧
      π/2-ω≤(31/10)*(ε-e) ∧
      area(S\U)≤(31/10000)*(ε-e) ∧
      area(U\S)≤lambdaMissing*(ε-e) ∧
      ApproxHallways K S (4*4*(π/2-ω)) := by
  intro K hK hclose S hS ω hω hα hcon
  have h:=explicit_terminal_certificate hP hbox hK hclose hS hω hα hcon
  simpa [lambdaMissing] using h

/-- At the cutoff the refined cap error plus full-angle hallway slack lies
inside the explicit 1e-10 normal-recovery radius. -/
theorem cutoff_normal_error {ε e α : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar)
    (he : 0≤e) (heε : e≤ε)
    (hα : 0≤α) (hangle : α≤(31/10)*(ε-e)) :
    kCenter*sqrt e+16*α≤explicitNormalError := by
  have hs:=epsilonStar_sqrt_bound hε hstar
  have hse:=sqrt_le_sqrt heε
  have heps : ε≤sqrt ε := by
    have h1 : ε≤1 := hstar.trans (by
      unfold Targets.epsilonStar
      positivity)
    exact self_le_sqrt_of_unit ⟨hε,h1⟩
  unfold kCenter explicitNormalError
  nlinarith

/-- The whole 2.3-sector fits inside the fixed 1e-20 chart radius. -/
theorem cutoff_sector_scale {ε e : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar)
    (he : 0≤e) (heε : e≤ε) :
    CHaus*sqrt ε+sqrt 2*(kCenter*sqrt e)≤explicitSectorRadius := by
  have hs:=epsilonStar_sqrt_bound hε hstar
  have hse:=sqrt_le_sqrt heε
  have hroot : sqrt 2<3/2 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  unfold CHaus kCenter explicitSectorRadius
  nlinarith

/-- The forward normal estimate already fits below 2.3 sqrt(epsilon). -/
theorem cutoff_forward_23 {ε e α : ℝ}
    (hε : 0≤ε) (hstar : ε≤Targets.epsilonStar)
    (he : 0≤e) (heε : e≤ε)
    (hα : 0≤α) (hangle : α≤(31/10)*(ε-e)) :
    (100/49)*(kCenter*sqrt e+16*α)≤CHaus*sqrt ε := by
  have hs:=sqrt_nonneg ε
  have hse:=sqrt_le_sqrt heε
  have heps : ε≤sqrt ε := by
    have h1 : ε≤1 := hstar.trans (by
      unfold Targets.epsilonStar
      positivity)
    exact self_le_sqrt_of_unit ⟨hε,h1⟩
  unfold kCenter CHaus
  nlinarith

/-- Positive-deficit cutoff assembly. -/
theorem explicit_cutoff_positive {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point}
    (hS : IsMovingSofa S)
    (hpos : 0<sofaDeficit P S)
    (hstar : sofaDeficit P S≤Targets.epsilonStar) :
    Targets.SofaConclusions P S ∧ Targets.AngleConclusions P S := by
  have h144:=hstar.trans epsilonStar_le_144
  have hentry:=effective_entry P hP hbox S hS hpos.le h144
  have hentryLocal :
      EuclideanClose localSupportRadius
        (midpointNormalizedSofa P S) (gerverSofa P) :=
    hentry.mono (cutoff_global_entry_radius hpos.le hstar).le
  have h22 : 2.2≤area S := by
    have hM: (2219/1000:ℝ)<area (gerverSofa P):=
      (gerverSofa_area_mem hP hbox).1.trans (by norm_num)
    unfold sofaDeficit at hpos hstar
    nlinarith
  obtain ⟨ω,hω,hSω⟩:=theorem1_5_1 hS h22
  have h30:=hstar.trans epsilonStar_le_30
  obtain ⟨hα0,hαstrict⟩:=
    effective_angle_entry P hP hbox S ω hSω hω hpos h30
  have hαlocal : π/2-ω≤localAngleRadius :=
    (hαstrict.trans (cutoff_angle_entry_radius hpos.le hstar)).le
  have hNcloseCap :
      UpperSupportClose localSupportRadius
        (sofaCap (midpointNormalizedSofa P S)) P.cap := by
    have hNm:=midpointNormalizedSofa_movingWithAngle P hSω
    have hNc:=ms_isCompact_of_isMovingSofaWithAngle hNm
    have hNn:=hNm.2.1.nonempty
    have htop:=midpointNormalizedSofa_top P
      (ms_isCompact_of_isMovingSofaWithAngle hSω) hSω.2.1.nonempty
    have hstrip:=moving_strip_of_top ⟨ω,hNm⟩ htop
    exact sofaCap_close_to_gerver hP hbox hNc hNn hstrip htop hentryLocal
  obtain ⟨D,hDR⟩:=build_local_data hP hbox hSω hω rfl hpos
    (δT:=localSupportRadius) (αT:=localAngleRadius) (R:=4)
    (cutoff_terminal_adapter hP hbox)
    (δQ:=localSupportRadius)
    (fun K hK hclose=>explicit_local_cap_certificate hP hbox hK hclose)
    hentryLocal hαlocal
  have hDR' : D.R=4:=hDR
  have hcones : ∀p∈gerverSofa P,
      ∃θ,interiorSector p θ sectorHalfAngle explicitSectorRadius⊆gerverSofa P :=
    gerver_sector_radius_explicit hP hbox
  have hscale:=cutoff_sector_scale hpos.le hstar D.e_nonneg D.e_le
  have hnormalSmall:=cutoff_normal_error hpos.le hstar
    D.e_nonneg D.e_le D.angle.1 D.angle.2
  have hsubset : D.N⊆D.K := by
    rw [D.K_eq]
    exact subset_sofaCap D.Ncompact D.strip
  have hnormal0:=directed_to_gerver_explicit hP hbox D.Kcap hsubset
    (δ:=kCenter*sqrt D.e) (ζ:=16*(π/2-ω))
    (by positivity) (by positivity)
    D.support_close
    (by
      rw [hDR']
      simpa using D.hallways)
    hnormalSmall
  have hnormal :
      DirectedClose ((100/49)*(kCenter*sqrt D.e+
        16*(π/2-ω))) D.N (gerverSofa P) := by
    simpa using hnormal0
  have hforward:=cutoff_forward_23 hpos.le hstar
    D.e_nonneg D.e_le D.angle.1 D.angle.2
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hmargin:=gerver_roof_slack_explicit hP hbox hroof
  have hδτ : kCenter*sqrt D.e<explicitRoofClip := by
    have hs:=epsilonStar_sqrt_bound hpos.le hstar
    have hse:=sqrt_le_sqrt D.e_le
    unfold kCenter explicitRoofClip
    nlinarith
  have hareaSmall : sqrt (sofaDeficit P S)≤1/200 := by
    have hs:=epsilonStar_sqrt_bound hpos.le hstar
    nlinarith
  have hsofa:=recover_local_23_50 hP hbox D hpos
    (R₀:=explicitSectorRadius)
    (by norm_num [explicitSectorRadius])
    hcones hscale hnormal hforward
    hroof (τ:=explicitRoofClip)
    (by norm_num [explicitRoofClip]) hmargin hδτ hareaSmall
  have hangleAll : Targets.AngleConclusions P S := by
    intro ω' hSω' hred'
    have ha30:=hstar.trans epsilonStar_le_30
    obtain ⟨ha0,haeff⟩:=
      effective_angle_entry P hP hbox S ω' hSω' hred' hpos ha30
    have halocal : π/2-ω'≤localAngleRadius :=
      (haeff.trans (cutoff_angle_entry_radius hpos.le hstar)).le
    have hNm:=midpointNormalizedSofa_movingWithAngle P hSω'
    have hNc:=ms_isCompact_of_isMovingSofaWithAngle hNm
    have hNn:=hNm.2.1.nonempty
    have htop:=midpointNormalizedSofa_top P
      (ms_isCompact_of_isMovingSofaWithAngle hSω') hSω'.2.1.nonempty
    have hstrip:=moving_strip_of_top ⟨ω',hNm⟩ htop
    let K:=sofaCap (midpointNormalizedSofa P S)
    have hK:=sofaCap_isCap hNc hNn hstrip htop
    have hcon:=sofaCap_partial_constraints hNm
      ⟨(arccos_nonneg _).trans hred'.1,hred'.2⟩ htop
    have ht:=explicit_terminal_certificate hP hbox hK
      hNcloseCap hNc.measurableSet
      ⟨(arccos_nonneg _).trans hred'.1,hred'.2⟩ halocal hcon
    dsimp at ht
    have he:=ht.1
    have hang:=ht.2.1
    exact ⟨sub_nonneg.mpr hred'.2,
      hang.trans (mul_le_mul_of_nonneg_left
        (show sofaDeficit P S-
          (area (gerverSofa P)-area (capShape K))≤sofaDeficit P S by
            linarith [he])
        (by norm_num))⟩
  exact ⟨hsofa,hangleAll⟩

/-- Exact final Appendix G target. -/
theorem explicit_cutoff : Targets.ExplicitCutoff := by
  intro P hP hbox S hS hnonneg hstar
  rcases hnonneg.eq_or_lt with hz|hp
  · have hpin:=normalizedSofa_eq_gerver_of_zero_deficit hP hbox hS hz.symm
    have hc:=isCompact_of_isMovingSofa hS
    have hn:=hS.choose_spec.2.1.nonempty
    have hm:=midpoint_eq_translate_normalized (P:=P) hc hn
    rw [hpin] at hm
    have hmid : horizontalMidpoint (gerverSofa P)-
        horizontalMidpoint (gerverSofa P)=0 := by ring
    simp [hmid] at hm
    refine ⟨?_,?_⟩
    · rw [Targets.SofaConclusions,hz,hm]
      simp [symmetricDifferenceArea,EuclideanClose.refl]
    · intro ω hSω hred
      have hNm:=midpointNormalizedSofa_movingWithAngle P hSω
      rw [hm] at hNm
      have he:=gerver_reduced_angle_eq hP hbox hred hNm
      rw [Targets.AngleConclusions]
      rw [he,hz]
      norm_num
  · exact explicit_cutoff_positive hP hbox hS hp hstar

end MovingSofaQuantitative
