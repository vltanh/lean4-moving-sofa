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

/-- Refined missing-area recovery.  The full interior ball of radius
\`κρ\` survives erosion after losing only radius \`r\`.  The earlier
\`directedClose_of_missing_area\` bound required \`r ≤ κρ/2\`, which loses
too much for the 10300 coefficient.  An inscribed square of side
\`κρ-r\` suffices; no convexity of S or G is used. -/
theorem directedClose_of_missing_area_full_ball
    {G U S : Set Point} {κ r₀ r ρ η : ℝ}
    (hκ : 0<κ) (hρ : 0<ρ) (hρ₀ : ρ≤r₀)
    (hballs : HasInteriorBalls G κ r₀)
    (hr : 0≤r) (hreserve : r<κ*ρ)
    (herosion : euclideanErosion r G⊆U)
    (hUf : volume U≠⊤) (hmissing : area (U\S)≤η)
    (hsmall : η<(κ*ρ-r)^2) :
    DirectedClose ρ G S := by
  intro p hp
  by_contra hnone
  obtain ⟨z,hz⟩:=hballs p hp ρ hρ hρ₀
  let a:=κ*ρ-r
  have ha : 0<a := sub_pos.mpr hreserve
  have hsq : centeredSquare z a ⊆ U\S := by
    intro q hq
    have hqz : euclideanDist z q≤a :=
      centeredSquare_subset_ball z hq
    have hqR : euclideanDist z q≤κ*ρ := by
      dsimp [a] at hqz
      linarith [hr]
    have hqG : q∈G := (hz hqR).1
    have hqP : euclideanDist p q≤ρ := (hz hqR).2
    refine ⟨herosion ?_,?_⟩
    · intro q' hqq'
      apply (hz ?_).1
      have htriangle:=euclideanDist_triangle z q q'
      dsimp [a] at hqz
      linarith
    · intro hqS
      exact hnone ⟨q,hqS,hqP⟩
  have hfinite : volume (U\S)≠⊤ :=
    volume_ne_top_of_subset sdiff_subset hUf
  have harea:=area_mono_of_finite hsq hfinite
  rw [area_centeredSquare z ha.le] at harea
  exact (not_lt_of_ge (harea.trans hmissing)) hsmall

/-- The exact scalar reserve used by both effective recovery theorems.
The coefficient \`20\` is large enough because \`2000/1051>sqrt 2\`.
In particular no assumption \`sqrt 2*delta <= kappa*rho/2\` is required. -/
theorem effective_recovery_ball_gap {δ E : ℝ}
    (hδ : 0≤δ) (hE : 0<E) :
    sqrt E <
      (100/1051:ℝ)*(20*(δ+sqrt E))-sqrt 2*δ := by
  have hs : 0<sqrt E := sqrt_pos.mpr hE
  have hroot : sqrt 2<3/2 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),
      sqrt_nonneg (2:ℝ)]
  have hcoef : 0≤((2000/1051:ℝ)-sqrt 2)*δ := by
    apply mul_nonneg
    · linarith [hroot]
    · exact hδ
  nlinarith [hcoef,hs]

theorem effective_recovery_ball_area_gap {δ E : ℝ}
    (hδ : 0≤δ) (hE : 0<E) :
    E < ((100/1051:ℝ)*(20*(δ+sqrt E))-sqrt 2*δ)^2 := by
  have hgap:=effective_recovery_ball_gap hδ hE
  have hs:=sq_sqrt hE.le
  have hpos : 0≤(100/1051:ℝ)*(20*(δ+sqrt E))-sqrt 2*δ :=
    le_of_lt (lt_trans (sqrt_pos.mpr hE) hgap)
  have hprod : 0 <
      (((100/1051:ℝ)*(20*(δ+sqrt E))-sqrt 2*δ)-sqrt E) *
      (((100/1051:ℝ)*(20*(δ+sqrt E))-sqrt 2*δ)+sqrt E) := by
    apply mul_pos
    · exact sub_pos.mpr hgap
    · exact add_pos_of_nonneg_of_pos hpos (sqrt_pos.mpr hE)
  nlinarith [hprod]

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
  have hgap : sqrt E < (100/1051:ℝ)*ρ-r := by
    simpa [ρ,r] using effective_recovery_ball_gap hδ hE
  have hreserve : r<(100/1051:ℝ)*ρ := by
    linarith [hgap,sqrt_pos.mpr hE]
  have hmissSmall : E<((100/1051:ℝ)*ρ-r)^2 := by
    simpa [ρ,r] using effective_recovery_ball_area_gap hδ hE
  have herode : euclideanErosion r (gerverSofa P)⊆capShape K := by
    rw [←gerver_shape_eq hP hbox]
    exact orthogonal_reference_erosion hδ
      (gm_isCap hP hbox) hK hclose
  have hUf : volume (capShape K)≠⊤ :=
    volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne
  have hback:=directedClose_of_missing_area_full_ball
    (show (0:ℝ)<100/1051 by norm_num) hρ hρ0 hballs
    (by dsimp [r]; positivity) hreserve
    herode hUf hmissing hmissSmall
  have hback' : DirectedClose (10300*sqrt E) (gerverSofa P) S :=
    hback.mono (by
      dsimp [ρ]
      nlinarith [hδbound])
  exact ⟨hfront',hback'⟩


end MovingSofaQuantitative
