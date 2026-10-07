module

public import MovingSofaQuantitative.ExplicitReferenceScales
public import MovingSofaQuantitative.OrthogonalErosion
public import MovingSofaStability.Recovery

/-!
# Coarse effective actual-set recovery

UNCOMPILED SOURCE.  This packages the explicit 51/5 roof factor and
100/1051 interior-ball ratio used in notes 26--27.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

/-- One coarse recovery lemma shared by the right-angle and partial-angle
effective arguments. -/
theorem effective_coarse_recovery {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K S : Set Point} (hK : IsCap K (π/2))
    (hSK : S⊆K)
    {E δ ζ : ℝ}
    (hE : 0<E) (hE20 : E≤1/(10:ℝ)^20)
    (hδ : 0≤δ) (hζ : 0≤ζ)
    (hδbound : δ≤514*sqrt E)
    (hζbound : ζ≤sqrt E)
    (hclose : UpperSupportClose δ K P.cap)
    (hhall : ApproxHallways K S ζ)
    (hmissing : area (capShape K\S)≤E) :
    EuclideanClose (10300*sqrt E) S (gerverSofa P) := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  have hslack:=gerver_roof_slack_explicit hP hbox hroof
  have houter:=gerver_outer_margin_one_fifth hP hbox
  have hballs:=gerver_interior_balls_explicit hP hbox
  have hs:=sqrt_pos.mpr hE
  have hs2:=sq_sqrt hE.le
  have hs10 : sqrt E≤1/(10:ℝ)^10 := by
    nlinarith [hE20,hs2,hs]
  have hδsmall : δ<1/5 := by
    exact hδbound.trans_lt (by nlinarith [hs10])
  have hroofsmall : δ+ζ<explicitRoofClip := by
    have hsum : δ+ζ≤515*sqrt E := by linarith
    exact hsum.trans_lt (by
      dsimp [explicitRoofClip]
      nlinarith [hs10])
  have hfront:=directed_to_reference_of_margins hroof hK
    (show (0:ℝ)<5/51 by norm_num) hδ hζ hclose
    (fun q hq t ht => houter q hq t)
    hδsmall hroofsmall hslack hSK hhall
  have hfront' : DirectedClose (10300*sqrt E) S (gerverSofa P) := by
    rw [gerver_shape_eq hP hbox] at hfront
    exact hfront.mono (by
      have hc : max 1 (1/(5/51:ℝ))=51/5 := by norm_num
      rw [hc]
      nlinarith [hδbound,hζbound,hs.le])
  let ρ:=20*(δ+sqrt E)
  let r:=sqrt 2*δ
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ0 : ρ≤1/24 := by
    dsimp [ρ]
    have hsum : δ+sqrt E≤515*sqrt E := by nlinarith [hδbound]
    nlinarith [hs10]
  have hr : r≤(100/1051:ℝ)*ρ/2 := by
    dsimp [r,ρ]
    have hsqrt2 : sqrt 2<3/2 := by
      nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
    have hrat : (3/2:ℝ)*δ<
        (100/1051)*10*(δ+sqrt E) := by
      nlinarith [hs]
    nlinarith [mul_le_mul_of_nonneg_right hδbound (sqrt_nonneg (2:ℝ))]
  have hmissSmall : E<((100/1051:ℝ)*ρ/2)^2 := by
    dsimp [ρ]
    have hcoef : 1<(100/1051:ℝ)*10 := by norm_num
    nlinarith [hs2,hs]
  have herode : euclideanErosion r (gerverSofa P)⊆capShape K := by
    rw [←gerver_shape_eq hP hbox]
    exact orthogonal_reference_erosion hδ
      (gm_isCap hP hbox) hK hclose
  have hUf : volume (capShape K)≠⊤ :=
    volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne
  have hback:=directedClose_of_missing_area
    (show (0:ℝ)<100/1051 by norm_num) hρ hρ0 hballs
    herode hr hUf hmissing hmissSmall
  have hback' : DirectedClose (10300*sqrt E) (gerverSofa P) S :=
    hback.mono (by
      dsimp [ρ]
      nlinarith [hδbound])
  exact ⟨hfront',hback'⟩

/-- The helper used by the right-angle module. -/
theorem effective_disk_recovery_10300 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K S : Set Point} {ε δ : ℝ}
    (hε0 : 0≤ε) (hε20 : ε≤1/(10:ℝ)^20)
    (hSK : S⊆capShape K)
    (herode : euclideanErosion (sqrt 2*δ) (gerverSofa P)⊆capShape K)
    (hmissing : area (capShape K\S)≤ε)
    (hcap : EuclideanClose δ K P.cap) :
    EuclideanClose (10300*sqrt ε) S (gerverSofa P) := by
  rcases hε0.eq_or_lt with hz|hp
  · subst ε
    have hm : area (capShape K\S)=0 := by
      exact le_antisymm (hmissing.trans (by norm_num)) ENNReal.toReal_nonneg
    have hsEq:=measurable_subset_eq_of_area_sdiff_zero
      (measurable_capShape hcap.left_cap) hcap.left_cap_compact.measure_lt_top.ne hSK hm
    subst S
    exact EuclideanClose.refl _ (by positivity)
  · have hK:=hcap.left_cap
    have hclose:=hcap.abs_supp_sub_le hK.2.1.2.1
      (gm_isConvexBody_cap hP hbox).2.1 hK.2.1.1
      (gm_isConvexBody_cap hP hbox).1
    have hδbound : δ≤514*sqrt ε := by
      have := hcap.radius_nonneg
      exact le_trans (le_mul_of_one_le_left this (by norm_num : (1:ℝ)≤514))
        (by simp)
    have hhall : ApproxHallways K (capShape K) 0 :=
      capShape_exact_hallways hK
    exact effective_coarse_recovery hP hbox hK
      (show capShape K⊆K from sdiff_subset)
      hp hε20 (by exact hcap.radius_nonneg) le_rfl hδbound
      (by simp) hclose hhall hmissing

end MovingSofaQuantitative
