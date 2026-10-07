module

public import MovingSofaQuantitative.PartialAngleCompletion
public import MovingSofaQuantitative.EffectiveRightAngle
public import MovingSofaQuantitative.ExplicitReferenceScales

/-!
# Effective global entry modulus

UNCOMPILED SOURCE.  This is the final source assembly of note 27.

For an arbitrary original moving sofa with deficit epsilon <= 10^-144,
midpoint/top normalization is within
  3,000,000 * epsilon^(1/12)
of Gerver's sofa.

The proof does not use the local 2.3 theorem.  Its purpose is only to enter a
prescribed quantitative neighborhood.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def coarseEntryCoefficient : ℝ := 3000000

/-- Elementary conversion of the angle estimate into the partial-completion
deficit budget. -/
theorem effective_ebar_bound {ε α : ℝ}
    (hε : 0<ε) (hε1 : ε≤1)
    (hα : 0≤α) (hangle : α<500*ε^(1/6:ℝ)) :
    ε+144*α < 72001*ε^(1/6:ℝ) := by
  have hpow : ε≤ε^(1/6:ℝ) := by
    have h:=rpow_le_rpow_of_exponent_ge hε hε1
      (by norm_num : (1/6:ℝ)≤1)
    simpa using h
  nlinarith

/-- Square-root conversion used in the final modulus. -/
theorem sqrt_ebar_lt_269 {ε E : ℝ}
    (hε : 0<ε) (hE : 0≤E)
    (hEbound : E<72001*ε^(1/6:ℝ)) :
    sqrt E<269*ε^(1/12:ℝ) := by
  have hs : 0<ε^(1/12:ℝ):=rpow_pos_of_pos hε _
  have hp12 : (ε^(1/12:ℝ))^2=ε^(1/6:ℝ) := by
    rw [←Real.rpow_two]
    rw [←Real.rpow_mul hε.le]
    norm_num
  have hsq:=sq_sqrt hE
  have h269 : 72001<(269:ℝ)^2 := by norm_num
  nlinarith

theorem epsilon_twelfth_le_1e12 {ε : ℝ}
    (hε : 0≤ε) (hε144 : ε≤1/(10:ℝ)^144) :
    ε^(1/12:ℝ)≤1/(10:ℝ)^12 := by
  rcases hε.eq_or_lt with rfl|hp
  · norm_num
  · have hr:=rpow_le_rpow hε hε144 (by norm_num : (0:ℝ)≤1/12)
    have hpow :
        (1/(10:ℝ)^144)^(1/12:ℝ)=1/(10:ℝ)^12 := by
      rw [div_rpow (by norm_num : (0:ℝ)≤1) (by positivity)]
      simp only [one_rpow]
      rw [←Real.rpow_natCast,←Real.rpow_mul (show (0:ℝ)≤10 by norm_num)]
      norm_num
    simpa [hpow] using hr

/-- Coarse recovery at the exact ebar scale used in the global entry theorem.
This is a specialization of the same roof/erosion/interior-ball argument as
\`effective_coarse_recovery\`, with the sharper ebar bound rather than the
round threshold 10^-20. -/
theorem recover_from_effective_ebar {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K S : Set Point} (hK : IsCap K (π/2)) (hSK : S⊆K)
    {ε E δ ζ : ℝ}
    (hε : 0<ε) (hε144 : ε≤1/(10:ℝ)^144)
    (hE : 0<E) (hEbound : E<72001*ε^(1/6:ℝ))
    (hδ : 0≤δ) (hδbound : δ≤514*sqrt E)
    (hζ : 0≤ζ) (hζbound : ζ≤sqrt E)
    (hclose : UpperSupportClose δ K P.cap)
    (hhall : ApproxHallways K S ζ)
    (hmissing : area (capShape K\S)≤E) :
    EuclideanClose (10300*sqrt E) S (gerverSofa P) := by
  have hsE:=sqrt_ebar_lt_269 hε hE.le hEbound
  have hsε:=epsilon_twelfth_le_1e12 hε.le hε144
  have hsSmall : sqrt E<269/(10:ℝ)^12 := by
    nlinarith [mul_le_mul_of_nonneg_left hsε (by norm_num : (0:ℝ)≤269)]
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hslack:=gerver_roof_slack_explicit hP hbox hroof
  have houter:=gerver_outer_margin_one_fifth hP hbox
  have hballs:=gerver_interior_balls_explicit hP hbox
  have hδsmall : δ<1/5 := hδbound.trans_lt (by
    nlinarith [hsSmall])
  have hroofsmall : δ+ζ<explicitRoofClip := by
    have hsum : δ+ζ≤515*sqrt E := by nlinarith [hδbound,hζbound]
    dsimp [explicitRoofClip]
    nlinarith [hsSmall]
  have hfront:=directed_to_reference_of_margins hroof hK
    (show (0:ℝ)<5/51 by norm_num) hδ hζ hclose
    (fun q hq t ht=>houter q hq t) hδsmall hroofsmall
    hslack hSK hhall
  have hfront' : DirectedClose (10300*sqrt E) S (gerverSofa P) := by
    rw [gerver_shape_eq hP hbox] at hfront
    have hc : max 1 (1/(5/51:ℝ))=51/5 := by norm_num
    rw [hc] at hfront
    exact hfront.mono (by nlinarith [hδbound,hζbound,sqrt_nonneg E])
  let ρ:=20*(δ+sqrt E)
  let r:=sqrt 2*δ
  have hρ : 0<ρ := by
    dsimp [ρ]
    positivity
  have hρ0 : ρ≤1/24 := by
    dsimp [ρ]
    nlinarith [hδbound,hsSmall]
  have hr : r≤(100/1051:ℝ)*ρ/2 := by
    have hsqrt2 : sqrt 2<3/2 := by
      nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
    dsimp [r,ρ]
    have hcoef : (3/2:ℝ)*514<
        (100/1051)*10*(514+1) := by norm_num
    nlinarith [hδbound,sqrt_nonneg E]
  have hmissingSmall : E<((100/1051:ℝ)*ρ/2)^2 := by
    have hs:=sqrt_pos.mpr hE
    have hs2:=sq_sqrt hE.le
    dsimp [ρ]
    have hcoef : 1<(100/1051:ℝ)*10 := by norm_num
    nlinarith [hδbound]
  have herode : euclideanErosion r (gerverSofa P)⊆capShape K := by
    rw [←gerver_shape_eq hP hbox]
    exact orthogonal_reference_erosion hδ
      (gm_isCap hP hbox) hK hclose
  have hUf : volume (capShape K)≠⊤ :=
    volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne
  have hback:=directedClose_of_missing_area
    (show (0:ℝ)<100/1051 by norm_num) hρ hρ0 hballs
    herode hr hUf hmissing hmissingSmall
  have hback' : DirectedClose (10300*sqrt E) (gerverSofa P) S :=
    hback.mono (by
      dsimp [ρ]
      nlinarith [hδbound,sqrt_nonneg E])
  exact ⟨hfront',hback'⟩

/-- Positive-deficit effective global entry. -/
theorem effective_entry_positive {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point}
    (hS : IsMovingSofa S)
    (hpos : 0<sofaDeficit P S)
    (h144 : sofaDeficit P S≤1/(10:ℝ)^144) :
    EuclideanClose
      (coarseEntryCoefficient*(sofaDeficit P S)^(1/12:ℝ))
      (midpointNormalizedSofa P S) (gerverSofa P) := by
  have h22 : 2.2≤area S := by
    have hM: (2219/1000:ℝ)<area (gerverSofa P):=
      (gerverSofa_area_mem hP hbox).1.trans (by norm_num)
    unfold sofaDeficit at hpos h144
    nlinarith
  obtain ⟨ω,hω,hSω⟩:=theorem1_5_1 hS h22
  have h30 : sofaDeficit P S≤1/(10:ℝ)^30 :=
    h144.trans (by norm_num)
  obtain ⟨hα0,hα⟩:=effective_angle_entry P hP hbox S ω hSω hω hpos h30
  let α:=π/2-ω
  let E:=sofaDeficit P S+144*α
  have hα4 : α≤1/4 := by
    have hs:=epsilon_twelfth_le_1e12 hpos.le h144
    have h6 : (sofaDeficit P S)^(1/6:ℝ)≤1/(10:ℝ)^24 := by
      have hsq : (sofaDeficit P S)^(1/6:ℝ)=
          ((sofaDeficit P S)^(1/12:ℝ))^2 := by
        rw [←Real.rpow_two,←Real.rpow_mul hpos.le]
        norm_num
      rw [hsq]
      nlinarith
    dsimp [α]
    nlinarith
  obtain ⟨D,-⟩:=build_partial_completion hP hbox hSω hω rfl hα4
  have hEpos : 0<E := by
    dsimp [E,α]
    nlinarith
  have hEbound : E<72001*(sofaDeficit P S)^(1/6:ℝ) := by
    dsimp [E,α]
    exact effective_ebar_bound hpos
      (h144.trans (by norm_num))
      hα0 hα
  have hE4 : E≤1/(10:ℝ)^4 := by
    have hs:=sqrt_ebar_lt_269 hpos hEpos.le hEbound
    have h12:=epsilon_twelfth_le_1e12 hpos.le h144
    have hsE : sqrt E<269/(10:ℝ)^12 := by
      nlinarith [mul_le_mul_of_nonneg_left h12 (by norm_num : (0:ℝ)≤269)]
    have hs2:=sq_sqrt hEpos.le
    nlinarith
  let eK:=area (gerverSofa P)-sofaArea (π/2) D.K
  have heK0 : 0≤eK:=D.cap_deficit.1
  have heKE : eK≤E := by
    dsimp [eK,E,α]
    simpa using D.cap_deficit.2
  have heK4 : eK≤1/(10:ℝ)^4:=heKE.trans hE4
  have hcap:=effective_right_angle_cap hP hbox D.K D.Kcap rfl heK0 heK4
  have href : centeredReference P.cap D.K=P.cap :=
    centeredReference_eq_of_midpoint D.midpoint
  rw [href] at hcap
  have hδ : 0≤514*sqrt E := by positivity
  have hcapE : EuclideanClose (514*sqrt E) D.K P.cap :=
    hcap.mono (mul_le_mul_of_nonneg_left
      (sqrt_le_sqrt heKE) (by norm_num))
  have hsupport : UpperSupportClose (514*sqrt E) D.K P.cap := fun t ht =>
    hcapE.abs_supp_sub_le D.Kcap.2.1.2.1
      (gm_isConvexBody_cap hP hbox).2.1
      D.Kcap.2.1.1 (gm_isConvexBody_cap hP hbox).1 t
  have hζ : 16*α≤sqrt E := by
    have hE1 : E≤1 := hE4.trans (by norm_num)
    have hs:=self_le_sqrt_of_unit ⟨hEpos.le,hE1⟩
    dsimp [E]
    nlinarith [hα0]
  have hrecover:=recover_from_effective_ebar hP hbox D.Kcap D.subset_cap
    hpos h144 hEpos hEbound hδ le_rfl
    (show 0≤16*α by positivity) hζ hsupport D.hallways
    (by simpa [D.U_eq,E,α] using D.missing)
  have hsE:=sqrt_ebar_lt_269 hpos hEpos.le hEbound
  exact hrecover.mono (by
    unfold coarseEntryCoefficient
    nlinarith [mul_lt_mul_of_pos_left hsE (show (0:ℝ)<10300 by norm_num)])

/-- Exact paper target G.5: coarse effective global entry. -/
theorem effective_entry : Targets.EffectiveEntry := by
  intro P hP hbox S hS hnonneg h144
  rcases hnonneg.eq_or_lt with hz|hp
  · have hpin:=normalizedSofa_eq_gerver_of_zero_deficit hP hbox hS hz.symm
    have hc:=isCompact_of_isMovingSofa hS
    have hn:=hS.choose_spec.2.1.nonempty
    have hm:=midpoint_eq_translate_normalized (P:=P) hc hn
    rw [hpin] at hm
    have hmid : horizontalMidpoint (gerverSofa P)-
        horizontalMidpoint (gerverSofa P)=0 := by ring
    simp [hmid] at hm
    rw [hz]
    simp [hm,EuclideanClose.refl,coarseEntryCoefficient]
  · simpa [coarseEntryCoefficient] using
      effective_entry_positive hP hbox hS hp h144

end MovingSofaQuantitative
