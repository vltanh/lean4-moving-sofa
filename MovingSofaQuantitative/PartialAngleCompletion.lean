module

public import MovingSofaQuantitative.EffectiveAngleEntry
public import MovingSofaQuantitative.EffectiveRecovery
public import MovingSofaQuantitative.MidpointEntry
public import MovingSofaStability.Global

/-!
# Partial-angle sofa versus its full right-angle cap

UNCOMPILED SOURCE.  This is the geometric bridge in note 27, Section 6.
It is deliberately independent of the local Q certificate.

For a midpoint/top-normalized moving sofa with reduced angle
\`omega >= pi/4\`, let \`K = sofaCap S\` and \`U = capShape K\`.
Visited inner wedges lie in K by connectedness.  Only the omitted angular
interval can contribute either points of S outside U or niche points outside K.
The six-wide containing strip then gives the 72 alpha area bounds.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- Horizontal projection of a normalized reduced moving sofa has width at most six. -/
theorem midpoint_sofa_horizontal_width_six {P : GerverParams}
    {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : π/4≤ω) :
    ∀p∈midpointNormalizedSofa P S, ∀q∈midpointNormalizedSofa P S,
      |p.1-q.1|≤6 := by
  have hN:=midpointNormalizedSofa_movingWithAngle P hS
  have hc:=ms_isCompact_of_isMovingSofaWithAngle hS
  have hn:=hS.2.1.nonempty
  have htop:=midpointNormalizedSofa_top P hc hn
  intro p hp q hq
  have h1:=moving_horizontal_span_le_six hN hω htop hp hq
  have h2:=moving_horizontal_span_le_six hN hω htop hq hp
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- At every visited open angle whose full-cap inner corner lies above the
floor, connectedness of the actual sofa forces that corner into the full cap. -/
theorem visited_positive_innerCorner_mem_sofaCap {S : Set Point} {ω t : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : ω∈Icc (0:ℝ) (π/2))
    (ht : t∈Ioo (0:ℝ) ω)
    (htop : supp S (π/2)=1)
    (hxy : 0<(innerCorner (sofaCap S) t).2) :
    innerCorner (sofaCap S) t∈sofaCap S := by
  let K:=sofaCap S
  have hc:=ms_isCompact_of_isMovingSofaWithAngle hS
  have hn:=hS.2.1.nonempty
  have hstrip:=moving_strip_of_top ⟨ω,hS⟩ htop
  have hK:=sofaCap_isCap hc hn hstrip htop
  have htL : t∈Ioo (0:ℝ) (π/2):=⟨ht.1,ht.2.trans_le hω.2⟩
  have hs : 0<sin t:=sin_pos_of_pos_of_lt_pi ht.1 (by linarith [htL.2,pi_pos])
  have hco : 0<cos t:=cos_pos_of_mem_Ioo ⟨by linarith [ht.1,pi_pos],htL.2⟩
  have hsu : supp K t=supp S t :=
    sofaCap_upper_support hc hn hstrip htop
      ⟨ht.1.le,by linarith [htL.2,pi_pos]⟩
  have hsv : supp K (t+π/2)=supp S (t+π/2) :=
    sofaCap_upper_support hc hn hstrip htop
      ⟨by linarith [ht.1,pi_pos],by linarith [htL.2]⟩
  obtain ⟨qR,hqR,hqReq⟩:=exists_dot_eq_supp hc hn t
  obtain ⟨qL,hqL,hqLeq⟩:=exists_dot_eq_supp hc hn (t+π/2)
  have hqRstrip:=hstrip hqR
  have hqLstrip:=hstrip hqL
  have hqRx : wedgeRightFoot K t≤qR.1 := by
    rw [wedgeRightFoot,le_div_iff₀ hco,hsu,←hqReq]
    simp only [dot,uvec]
    have hys : qR.2*sin t≤1 := by
      exact (mul_le_mul hqRstrip.2 (sin_le_one t)
        (sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [htL.2,pi_pos]))
        zero_le_one).trans_eq (one_mul 1)
    linarith
  have hqLx : qL.1≤wedgeLeftFoot K t := by
    rw [wedgeLeftFoot,le_div_iff₀ hs,hsv,←hqLeq]
    rw [uvec_add_pi_div_two]
    simp only [dot,vvec]
    have hyc : qL.2*cos t≤1 := by
      exact (mul_le_mul hqLstrip.2 (cos_le_one t) hco.le zero_le_one).trans_eq
        (one_mul 1)
    linarith
  obtain ⟨hxU,hxV⟩:=cn_innerCorner_dot K t
  rw [uvec_add_pi_div_two] at hxV
  have hleft : wedgeLeftFoot K t<(innerCorner K t).1 := by
    rw [wedgeLeftFoot,div_lt_iff₀ hs]
    simp only [dot,vvec] at hxV
    nlinarith [mul_pos hxy hco]
  have hright : (innerCorner K t).1<wedgeRightFoot K t := by
    rw [wedgeRightFoot,lt_div_iff₀ hco]
    simp only [dot,uvec] at hxU
    nlinarith [mul_pos hxy hs]
  have hcross :
      (innerCorner K t).1∈Icc qL.1 qR.1 :=
    ⟨hqLx.trans hleft.le,hright.le.trans hqRx⟩
  have hfst : ContinuousOn (fun z : Point=>z.1) S:=continuous_fst.continuousOn
  obtain ⟨q,hq,hqx⟩:=
    hS.2.1.isPreconnected.intermediate_value hqL hqR hfst hcross
  by_contra hcorner
  have hqK : q∈K:=subset_sofaCap hc hstrip hq
  have hqy : q.2<(innerCorner K t).2 := by
    by_contra hnq
    have hdown:=opt_cap_down hK hqK hxy.le (not_lt.mp hnq)
    have heq : (q.1,(innerCorner K t).2)=innerCorner K t := by
      ext <;> simp [hqx]
    exact hcorner (heq ▸ hdown)
  have hu : innerSlackU K t q<0 := by
    unfold innerSlackU
    rw [←hxU]
    simp only [dot,uvec] at hxU ⊢
    nlinarith [mul_pos (sub_pos.mpr hqy) hs]
  have hv : innerSlackV K t q<0 := by
    unfold innerSlackV
    rw [←hxV]
    simp only [dot,vvec] at hxV ⊢
    nlinarith [mul_pos (sub_pos.mpr hqy) hco]
  have hcon:=sofaCap_partial_constraints hS hω htop
  have hfeas:=hcon.2.1 q hq t ⟨ht.1.le,ht.2.le⟩
  exact (not_lt_of_ge hfeas) (max_lt hu hv)

/-- Any full-angle niche point outside the full cap must come from an
angle not yet visited by the original motion. -/
theorem exterior_niche_omitted {S : Set Point} {ω : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : ω∈Icc (0:ℝ) (π/2))
    (htop : supp S (π/2)=1) :
    niche (sofaCap S) (π/2)\sofaCap S ⊆
      omittedFloorWedges (sofaCap S) ω := by
  intro p hp
  obtain ⟨hy,t,ht,hu,hv⟩:=(mem_niche_iff_slacks (sofaCap S) p).1 hp.1
  have hnotVisited : ω≤t := by
    by_contra hn
    have htv : t∈Ioo (0:ℝ) ω:=⟨ht.1,lt_of_not_ge hn⟩
    have hcornerPos : 0<(innerCorner (sofaCap S) t).2 := by
      have hb:=point_below_corner_of_negative_slacks ht hu hv
      linarith
    have hcorner:=visited_positive_innerCorner_mem_sofaCap hS hω htv htop hcornerPos
    have hw : p∈wedge (sofaCap S) (π/2) t := by
      refine ⟨?_,?_⟩
      · simpa [fan,halfPlus,dot_uvec_pi_div_two] using hy
      · exact (cn_mem_qMinus.2 ⟨hu,hv⟩)
    exact hp.2 (lemma2_5_6
      (sofaCap_isCap (ms_isCompact_of_isMovingSofaWithAngle hS)
        hS.2.1.nonempty (moving_strip_of_top ⟨ω,hS⟩ htop) htop)
      ht hcorner hw)
  exact ⟨hy,t,ht,hnotVisited,hu,hv⟩

theorem cot_eq_tan_complement (t : ℝ) :
    cot t=tan (π/2-t) := by
  rw [cot_eq_cos_div_sin,tan_eq_sin_div_cos,
    sin_pi_div_two_sub,cos_pi_div_two_sub]

/-- Omitted wedges of a six-wide, height-one cap lie below 12 alpha. -/
theorem omitted_wedges_box {K : Set Point} {ω α x₋ x₊ : ℝ}
    (hK : IsCap K (π/2))
    (hα : α=π/2-ω)
    (hα0 : 0≤α) (hα4 : α≤1/4)
    (hproj : -supp K π=x₋ ∧ supp K 0=x₊)
    (hwidth : x₊-x₋≤6) :
    omittedFloorWedges K ω⊆Icc x₋ x₊×ˢIcc (0:ℝ) (12*α) := by
  intro p hp
  obtain ⟨hy,t,ht,hωt,hu,hv⟩:=hp
  have htopen : t∈Ioo (0:ℝ) (π/2):=ht
  obtain ⟨hleft,hright⟩:=wedge_point_between_feet htopen hy hu hv
  have hgap:=theorem2_5_5_supp hK htopen
  have hs : 0<sin t:=sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,pi_pos])
  have hc : 0<cos t:=cos_pos_of_mem_Ioo ⟨by linarith [ht.1,pi_pos],ht.2⟩
  have hfootL : x₋<wedgeLeftFoot K t := by
    rw [hproj.1,wedgeLeftFoot,lt_div_iff₀ hs]
    have h2:=hgap.2
    rw [show π/2+π/2=π by ring,cos_pi_div_two_sub] at h2
    nlinarith
  have hfootR : wedgeRightFoot K t<x₊ := by
    rw [hproj.2,wedgeRightFoot,div_lt_iff₀ hc]
    exact hgap.1
  have hx : p.1∈Icc x₋ x₊ :=
    ⟨(hfootL.trans hleft).le,(hright.trans hfootR).le⟩
  have hheight : p.2≤(x₊-x₋)*cot t := by
    unfold innerSlackU at hu
    have hsu:=hK.dot_le (show (x₊,0)∈K by
      rw [←hproj.2]
      exact opt_cap_A_mem hK) t
    simp only [dot,uvec] at hu hsu
    rw [cot_eq_cos_div_sin]
    have hsin0:=hs.le
    rw [le_div_iff₀ hs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) hc.le]
  have hcomp : 0≤π/2-t ∧ π/2-t≤α := by
    constructor
    · linarith [ht.2]
    · rw [hα]
      linarith [hωt]
  have hcot : cot t≤tan α := by
    rw [cot_eq_tan_complement]
    exact strictMonoOn_tan.monotoneOn
      ⟨by linarith [hcomp.1,pi_pos],by linarith [hcomp.2,hα4,pi_pos]⟩
      ⟨by linarith [hα0,pi_pos],by linarith [hα4,pi_pos]⟩ hcomp.2
  have htan : tan α≤2*α := tan_le_two_mul hα0 hα4
  exact ⟨hx,hy,by nlinarith [hheight,hwidth,hcot,htan]⟩

/-- Area of the union of all omitted wedges is at most 72 alpha. -/
theorem omitted_wedges_area_72 {K : Set Point} {ω α x₋ x₊ : ℝ}
    (hK : IsCap K (π/2))
    (hα : α=π/2-ω)
    (hα0 : 0≤α) (hα4 : α≤1/4)
    (hproj : -supp K π=x₋ ∧ supp K 0=x₊)
    (hwidth : x₊-x₋≤6) :
    area (omittedFloorWedges K ω)≤72*α := by
  have hsub:=omitted_wedges_box hK hα hα0 hα4 hproj hwidth
  have hm:=area_mono_of_finite hsub
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  rw [area_closed_rectangle (by linarith) (by positivity)] at hm
  nlinarith

structure PartialCompletionData (P : GerverParams) (S : Set Point)
    (ω ε α : ℝ) where
  N : Set Point
  K : Set Point
  U : Set Point
  N_eq : N=midpointNormalizedSofa P S
  K_eq : K=sofaCap N
  U_eq : U=capShape K
  Nmove : IsMovingSofaWithAngle N ω
  Kcap : IsCap K (π/2)
  subset_cap : N⊆K
  top : supp N (π/2)=1
  midpoint : horizontalMidpoint K=horizontalMidpoint P.cap
  alpha_def : α=π/2-ω
  epsilon_def : ε=area (gerverSofa P)-area N
  alpha_nonneg : 0≤α
  sofa_surplus : area (N\U)≤72*α
  exterior_niche : area (niche K (π/2)\K)≤72*α
  cap_deficit :
    0≤area (gerverSofa P)-sofaArea (π/2) K ∧
    area (gerverSofa P)-sofaArea (π/2) K≤ε+144*α
  missing : area (U\N)≤ε+144*α
  hallways : ApproxHallways K N (16*α)

/-- Complete partial-to-full comparison of note 27, Section 6. -/
theorem build_partial_completion {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hω : ω∈Icc (arccos (5/11:ℝ)) (π/2))
    (hε : ε=sofaDeficit P S)
    (hα4 : π/2-ω≤1/4) :
    ∃D : PartialCompletionData P S ω ε (π/2-ω),True := by
  let N:=midpointNormalizedSofa P S
  have hNm:=midpointNormalizedSofa_movingWithAngle P hS
  have hNc:=ms_isCompact_of_isMovingSofaWithAngle hNm
  have hNn:=hNm.2.1.nonempty
  have htop:=midpointNormalizedSofa_top P
    (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty
  have hstrip:=moving_strip_of_top ⟨ω,hNm⟩ htop
  let K:=sofaCap N
  have hK:=sofaCap_isCap hNc hNn hstrip htop
  have hsub:=subset_sofaCap hNc hstrip
  let U:=capShape K
  have hwidthPoint:=midpoint_sofa_horizontal_width_six (P:=P)
    hS (quarter_le_reduced_angle.trans hω.1)
  obtain ⟨l,hl,hlS⟩:=exists_dot_eq_supp hNc hNn π
  obtain ⟨r,hr,hrS⟩:=exists_dot_eq_supp hNc hNn 0
  have hlx : l.1=-supp N π := by
    rw [dot_uvec_pi] at hlS
    linarith
  have hrx : r.1=supp N 0 := by
    rw [dot_uvec_zero] at hrS
    exact hrS
  have hW : supp N 0+supp N π≤6 := by
    have h:=hwidthPoint r hr l hl
    rw [hlx,hrx] at h
    simpa [abs_of_nonneg (by
      have:=support_width_nonneg hNc hNn 0
      simpa [uvec_add_pi] using this)] using h
  have hproj : ∀p∈K,p.1∈Icc (-supp N π) (supp N 0) := by
    intro p hp
    have h0:=dot_le_supp hK.2.1.2.1 hp 0
    have hπ:=dot_le_supp hK.2.1.2.1 hp π
    rw [sofaCap_upper_support hNc hNn hstrip htop
      ⟨le_rfl,pi_pos.le⟩,
      sofaCap_upper_support hNc hNn hstrip htop
      ⟨pi_pos.le,le_rfl⟩,
      dot_uvec_zero,dot_uvec_pi] at h0 hπ
    exact ⟨by linarith,by linarith⟩
  have hα0 : 0≤π/2-ω:=sub_nonneg.mpr hω.2
  have homit:=omitted_wedges_area_72 hK rfl hα0 hα4 hproj
    (by simpa using hW)
  have hsurSub : N\U⊆omittedFloorWedges K ω := by
    intro p hp
    have hpK:=hsub hp.1
    have hNiche : p∈niche K (π/2) := by
      by_contra hn
      exact hp.2 ⟨hpK,hn⟩
    obtain ⟨hy,t,ht,hu,hv⟩:=(mem_niche_iff_slacks K p).1 hNiche
    have hωt : ω≤t := by
      by_contra hn
      have htvis : t∈Icc (0:ℝ) ω:=⟨ht.1.le,(lt_of_not_ge hn).le⟩
      have hsupp1:=sofaCap_upper_support hNc hNn hstrip htop
        ⟨ht.1.le,by linarith [ht.2,pi_pos]⟩
      have hsupp2:=sofaCap_upper_support hNc hNn hstrip htop
        ⟨by linarith [ht.1,pi_pos],by linarith [ht.2]⟩
      have hh:=moving_hallway_slacks hNm hp.1 htvis
      simp only [innerSlackU,innerSlackV,hsupp1,hsupp2] at hu hv hh
      exact (not_lt_of_ge hh) (max_lt hu hv)
    exact ⟨hy,t,ht,hωt,hu,hv⟩
  have hsur : area (N\U)≤72*(π/2-ω) :=
    (area_mono_of_finite hsurSub
      (volume_ne_top_of_subset (omitted_wedges_box hK rfl hα0 hα4 hproj
        (by simpa using hW))
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)).trans homit
  have hextSub : niche K (π/2)\K⊆omittedFloorWedges K ω :=
    exterior_niche_omitted hNm
      ⟨(arccos_nonneg _).trans hω.1,hω.2⟩ htop
  have hext : area (niche K (π/2)\K)≤72*(π/2-ω) :=
    (area_mono_of_finite hextSub
      (volume_ne_top_of_subset (omitted_wedges_box hK rfl hα0 hα4 hproj
        (by simpa using hW))
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)).trans homit
  have hAupper:=right_angle_cap_area_le_gerver
    (gerver_maximizing_value hP hbox) hK
  have hAlower :
      area N-144*(π/2-ω)≤sofaArea (π/2) K := by
    have hbalance1:=area_sdiff_balance hNc.measurableSet
      (measurable_capShape hK) hNc.measure_lt_top.ne
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
    have hbalance2:=niche_exterior_area_identity hK
    unfold U at hsur
    nlinarith [hsur,hext,hbalance1,hbalance2]
  have hεN : ε=area (gerverSofa P)-area N := by
    rw [hε,sofaDeficit,area_midpointNormalizedSofa]
  have hdef0 : 0≤area (gerverSofa P)-sofaArea (π/2) K :=
    sub_nonneg.mpr hAupper
  have hdefB :
      area (gerverSofa P)-sofaArea (π/2) K≤ε+144*(π/2-ω) := by
    rw [hεN]
    linarith
  have hmissing : area (U\N)≤ε+144*(π/2-ω) := by
    have hb:=missing_area_identity hNc.measurableSet
      (measurable_capShape hK) hNc.measure_lt_top.ne
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
      (area (gerverSofa P))
    have hUdef : area (gerverSofa P)-area U≤
        area (gerverSofa P)-sofaArea (π/2) K+
          area (niche K (π/2)\K) := by
      exact capShape_deficit_le_sofaArea_deficit_plus_exterior_niche hK
    nlinarith [hb,hUdef,hdefB,hext,hsur]
  have hhall : ApproxHallways K N (16*(π/2-ω)) := by
    intro p hp t ht
    by_cases hvis : t≤ω
    · have h1:=sofaCap_upper_support hNc hNn hstrip htop
        ⟨ht.1.le,by linarith [ht.2,pi_pos]⟩
      have h2:=sofaCap_upper_support hNc hNn hstrip htop
        ⟨by linarith [ht.1,pi_pos],by linarith [ht.2]⟩
      simpa [innerSlackU,innerSlackV,h1,h2] using
        moving_hallway_slacks hNm hp ⟨ht.1.le,hvis⟩
    · have hspan : ∀q∈N,norm2 q≤8 := midpoint_normalized_radius_eight
        hP hbox hNm hω
      exact approximate_slack_after_terminal hNc hNn hspan hp ht
        (not_le.mp hvis) hω.2
  have hmid : horizontalMidpoint K=horizontalMidpoint P.cap := by
    unfold horizontalMidpoint K
    rw [sofaCap_upper_support hNc hNn hstrip htop
      ⟨le_rfl,pi_pos.le⟩,
      sofaCap_upper_support hNc hNn hstrip htop
      ⟨pi_pos.le,le_rfl⟩]
    exact (midpointNormalizedSofa_midpoint P
      (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty).trans
      (gerver_midpoint_cap hP hbox)
  refine ⟨{
    N:=N,K:=K,U:=U,N_eq:=rfl,K_eq:=rfl,U_eq:=rfl,
    Nmove:=hNm,Kcap:=hK,subset_cap:=hsub,top:=htop,midpoint:=hmid,
    alpha_def:=rfl,epsilon_def:=hεN,alpha_nonneg:=hα0,
    sofa_surplus:=hsur,exterior_niche:=hext,
    cap_deficit:=⟨hdef0,hdefB⟩,missing:=hmissing,hallways:=hhall},trivial⟩

end MovingSofaQuantitative
