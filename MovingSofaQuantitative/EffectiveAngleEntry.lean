module

public import MovingSofaQuantitative.CoarseAngleCertificate
public import MovingSofaQuantitative.EffectiveRightAngle
public import MovingSofaUniqueness.AngleExtension

/-!
# Effective entry of the terminal angle

UNCOMPILED SOURCE.  This is the source version of note 27, Sections 2--5.
It proves the target
  alpha < 500 epsilon^(1/6)
for every reduced motion with epsilon <= 10^-30.

The auxiliary penalized cap is never asserted to be a moving sofa.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def partialPenaltyLambda : ℝ := 1/(2:ℝ)^20

/-- Positive partial-angle sofa area forces a uniform width bound once the
angle has entered the coarse high-angle range. -/
theorem positive_partial_cap_width_lt_32 {K : Set Point} {ω : ℝ}
    (hK : IsCap K ω) (hω : 2*arctan (4/5:ℝ)<ω)
    (hA : 0<sofaArea ω K) :
    horizontalWidth K<32 := by
  have hcot : cot ω≤1/4 := by
    have ht : 4<tan ω := high_angle_tan_lower hω
    rw [cot_eq_one_div_tan]
    exact (one_div_le (by positivity) (by positivity)).2 ht.le
  let W:=horizontalWidth K
  have hniche : max 0 (W/4-sqrt 2)^2≤area (niche K ω) :=
    partial_inner_triangle_area_lower hK hcot
  have harea : sofaArea ω K≤W-max 0 (W/4-sqrt 2)^2 := by
    nlinarith [cap_area_le_width hK]
  by_contra hn
  have hW : 32≤W:=not_lt.mp hn
  have hs : sqrt 2<3/2 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  have hz : W-(W/4-3/2)^2<0 := by
    nlinarith [hW]
  have hm : (W/4-3/2)^2≤(W/4-sqrt 2)^2 := by nlinarith
  rw [max_eq_right (sq_nonneg _)] at harea
  linarith

/-- Every high-angle standard cap contains a common triangle whose inradius is
at least alpha/16. -/
theorem partial_cap_common_ball {K : Set Point} {ω α : ℝ}
    (hK : IsCap K ω) (hα : α=π/2-ω)
    (ha0 : 0<α) (ha1 : α≤1/100) :
    ∃p : Point,euclideanBall p (α/16)⊆K := by
  let c:=1/cos ω-tan ω
  have hc : c=tan(α/2) := by
    rw [hα]
    exact sec_sub_tan_eq_tan_half_complement ω
  have hc0 : α/4≤c := by
    rw [hc]
    exact half_angle_tan_lower ha0 (by linarith [ha1])
  have htri : convexHull ℝ {(0,0),(c,0),(c,1)}⊆K :=
    standard_cap_common_triangle hK
  refine ⟨(3*c/4,1/4),?_⟩
  exact (disk_in_common_triangle hc0 ha1).trans htri

def partialSupportPenalty (K C : Set Point) (ω : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(π/2+ω),(supp C t-supp K t)^2

/-- Integral-penalized comparison for a partial-angle cap. -/
theorem exists_partial_penalized_cap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} {ω ε : ℝ}
    (hK : IsCap K ω) (hω : 2*arctan (4/5:ℝ)<ω)
    (hA : area (gerverSofa P)-ε≤sofaArea ω K)
    (hε : 0<ε) :
    ∃ C : Set Point,IsCap C ω ∧
      area (gerverSofa P)-ε≤sofaArea ω C ∧
      partialSupportPenalty K C ω≤ε/partialPenaltyLambda := by
  let Θn:=dyadicAngleSet ω (by
    constructor
    · linarith [arctan_pos (by norm_num : (0:ℝ)<4/5)]
    · linarith [hω]) 
  choose Cn hCn hmax using fun n =>
    exists_penalizedMax
      (partialIntegralQuadratureSamples (Θn n) K partialPenaltyLambda)
      K (polyCap (Θn n) K)
      (partial_recovery_positive hK hA hε)
  obtain ⟨C,φ,hφ,hlim⟩ :=
    bounded_partial_penalized_subsequence hK hω hA hε Cn hCn
  have hcap:=capH_isCap_limit hφ hlim
  have harea:=partial_polyArea_limsup hφ
  have hpen:=partial_quadrature_tendsto_integral hK hcap hφ
  have hglobal:=fixed_angle_cap_le_gerver hP hbox hcap
  refine ⟨C,hcap,?_,?_⟩
  · exact penalized_recovery_area_lower hA harea hpen
  · have hobj:=penalized_recovery_objective hA harea hpen
    unfold partialPenaltyLambda
    nlinarith [hglobal]

/-- L2 penalty controls the support supremum by 1024 epsilon^(1/3). -/
theorem partial_penalty_support_bound {K C : Set Point} {ω ε : ℝ}
    (hK : IsCap K ω) (hC : IsCap C ω)
    (hKr : ∀p∈K,norm2 p<64) (hCr : ∀p∈C,norm2 p<64)
    (hε : 0≤ε)
    (hpen : partialSupportPenalty K C ω≤(2:ℝ)^20*ε) :
    ∀t∈Icc (0:ℝ) (π/2+ω),
      |supp C t-supp K t|≤1024*ε^(1/3:ℝ) := by
  have hLip : LipschitzWith 128 (fun t=>supp C t-supp K t) :=
    support_difference_lipschitz_of_radius hC.2.1 hK.2.1 hCr hKr
  have hcubic:=support_sup_cubic_bound_on_interval hLip hpen
  intro t ht
  have h:=point_le_support_sup ht
  have hp:=rpow_nonneg ε (1/3:ℝ)
  have hpow : (ε^(1/3:ℝ))^3=ε := by
    rcases hε.eq_or_lt with rfl|he
    · norm_num
    · rw [←rpow_natCast,←rpow_mul he.le]
      norm_num
  nlinarith

/-- Approximate pinned inequalities inherited from the penalized polygon
variation.  The error is D/(4 a0). -/
theorem partial_approx_pinned {K C : Set Point} {ω ε a₀ D : ℝ}
    (hK : IsCap K ω) (hC : IsCap C ω)
    (ha : 0<a₀) (ha100 : a₀≤1/100)
    (hball : ∃p,euclideanBall p (a₀/16)⊆C)
    (hmax : PartialPenalizedCapMax K C partialPenaltyLambda)
    (hD : ∀t∈Icc (0:ℝ) (π/2+ω),|supp C t-supp K t|≤D) :
    pinnedDefectRight C ω≤D/(4*a₀) ∧
    pinnedDefectLeft C ω≤D/(4*a₀) := by
  have hmove : pinned_height_move_support_cost C ω (a₀/16)≤4096/a₀ :=
    partial_cap_height_move_cost hC hball ha
  have hpenvar : penalty_height_derivative_bound K C ω
      partialPenaltyLambda D (4096/a₀) :=
    integral_penalty_variation_bound hD hmove
  have hfloat:=floating_defect_budget hmax hpenvar
  have hidentity:=completed_boundary_defect_identity hC
  exact solve_two_pinned_defects hfloat hidentity
    (partial_pin_sine_lower ha100)

/-- High-angle quantitative geometry: sufficiently small support and pinned
errors force the missing triangle into the candidate inner quadrant. -/
theorem approximate_remaining_angle_triangle {K C : Set Point}
    {ω α a₀ D ζ : ℝ}
    (hK : IsCap K ω) (hC : IsCap C ω)
    (hα : α=π/2-ω)
    (ha : a₀≤α) (ha0 : 0<a₀) (ha100 : a₀≤1/100)
    (hω : 2*arctan (4/5:ℝ)<ω)
    (hCarea : (22/10:ℝ)<area C)
    (hclose : UpperSupportClose D K C)
    (hD : D<a₀^2/64) (hζ : ζ<a₀/256)
    (hpinR : pinnedDefectRight C ω≤ζ)
    (hpinL : pinnedDefectLeft C ω≤ζ) :
    remainingAngleTriangle ω⊆innerQuadrant K α := by
  obtain hright|hleft:=large_outer_extent_of_area hC hCarea
  · let T:=tan ω
    let d:=rightExtent C
    let ry:=1-d/T
    let g:=sqrt(1-ry^2)
    have hd : 11/10≤d∧d≤T:=right_extent_bounds hC hright
    have hgeom:=high_angle_gap_inequalities hω hd
    have htop:=approx_right_top_contact hC hpinR hgeom
    have hfloor:=right_floor_contact hC
    exact triangle_inner_of_support_witnesses hK hclose hD hζ
      hα ha ha0 hgeom htop hfloor
  · have hreflect:=vertical_reflection_preserves_cap hC
    have hKreflect:=vertical_reflection_preserves_cap hK
    have hright':=reflect_left_extent hleft
    have hclose':=UpperSupportClose.reflect hclose
    have hpin':=reflect_pinned_defects hpinL hpinR
    have ht:=approximate_remaining_angle_triangle hKreflect hreflect
      hα ha ha0 ha100 hω (by simpa using hCarea)
      hclose' hD hζ hpin'.1 hpin'.2
    simpa [remainingAngleTriangle,innerQuadrant,verticalReflection] using
      reflect_triangle_inclusion ht

/-- If alpha is bounded below and the deficit is below a0^6/10^16, the
specified original sofa actually completes the right-angle motion. -/
theorem effective_angle_extension {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε a₀ : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hωred : ω∈Icc (arccos (5/11:ℝ)) (π/2))
    (hε : ε=sofaDeficit P S) (hεpos : 0<ε)
    (ha0 : 0<a₀) (ha100 : a₀≤1/100)
    (ha : a₀≤π/2-ω)
    (hsmall : ε≤a₀^6/(10:ℝ)^16) :
    ∃g : Rigid,IsMovingSofaWithAngle (g '' S) (π/2) := by
  have hcoarse:=CoarseAngleCertificate.coarse_angle_entry hP hbox hS hωred
    (by
      have hpow : a₀^6/(10:ℝ)^16<1/5000 := by
        have := pow_le_pow_left₀ ha0.le ha100 6
        norm_num at this ⊢
        nlinarith
      rw [←hε]
      exact hεpos.trans_le hsmall |>.trans_lt hpow)
  obtain ⟨v,hstd⟩:=proposition2_3_1_exists
    ⟨(arccos_nonneg _).trans hωred.1,hωred.2⟩ hS
  let K:=monotoneCap (Rigid.translate v '' S) ω
  have hK:=partial_cap_of_standard_sofa hS v hstd
  have hKA : area (gerverSofa P)-ε≤sofaArea ω K :=
    monotone_cap_area_lower hS v hstd hε
  obtain ⟨C,hC,hCA,hpen⟩:=
    exists_partial_penalized_cap hP hbox hK hcoarse hKA hεpos
  have hKr:=partial_positive_cap_radius64 hK hKA hεpos hsmall
  have hCr:=partial_positive_cap_radius64 hC hCA hεpos hsmall
  let D:=1024*ε^(1/3:ℝ)
  have hDsup:=partial_penalty_support_bound hK hC hKr hCr hεpos.le
    (by simpa [partialPenaltyLambda] using hpen)
  have hDsmall : D<a₀^2/64 := by
    have hr:=rpow_le_rpow hεpos.le hsmall (by norm_num : (0:ℝ)≤1/3)
    have hp:=rpow_pow_nat ha0.le 6 (1/3:ℝ)
    dsimp [D]
    norm_num at hr ⊢
    nlinarith
  have hball:=partial_cap_common_ball hC rfl
    (by linarith [ha,hωred.2]) ha100
  obtain ⟨hpinR,hpinL⟩:=partial_approx_pinned hK hC
    ha0 ha100 hball (partial_penalized_max hC hpen) hDsup
  let ζ:=D/(4*a₀)
  have hζ : ζ<a₀/256 := by
    dsimp [ζ]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hDsmall]
  have htri:=approximate_remaining_angle_triangle hK hC rfl ha
    ha0 ha100 hcoarse (by
      have hM: (2219/1000:ℝ)<area (gerverSofa P):=
        (gerverSofa_area_mem hP hbox).1.trans (by norm_num)
      have hcaparea:=sofaArea_le_area hC
      nlinarith [hCA,hsmall])
    (fun t ht=>hDsup t ht) hDsmall hζ hpinR hpinL
  have havoid:=moving_sofa_avoids_inner_quadrant hS v hstd
  have htruncated:=triangle_inside_inner_forces_truncated_para hK htri havoid
  have hextend:=prepend_missing_rotation hS v hstd htruncated
  exact ⟨Rigid.translate v,by simpa [Rigid.coe_translate] using hextend⟩

/-- A nonzero missing angle is bounded by the effective right-angle theorem. -/
theorem angle_gap_after_extension {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} {ω ε : ℝ}
    (hS : IsMovingSofaWithAngle S ω)
    (hωred : ω∈Icc (arccos (5/11:ℝ)) (π/2))
    (hε : ε=sofaDeficit P S) (hε20 : ε≤1/(10:ℝ)^20)
    (hext : ∃g : Rigid,IsMovingSofaWithAngle (g '' S) (π/2)) :
    π/2-ω≤41200*sqrt ε := by
  obtain ⟨g,hg⟩:=hext
  have hright:=effective_right_angle_sofa hP hbox hg hε
    (by have:=sofaDeficit_nonneg hP hbox ⟨ω,hS⟩; simpa [hε] using this)
    hε20
  have hwidthS:=terminal_normal_width_le_one hS
  have hwidthG:=gerver_four_point_width_lower hP hbox
    (α:=π/2-ω) (by linarith [hωred.2])
    (by
      have hc:=CoarseAngleCertificate.coarse_angle_entry hP hbox hS hωred
        (by rw [←hε]; exact lt_of_le_of_lt hε20 (by norm_num))
      linarith [hc,arctan_pos (by norm_num : (0:ℝ)<4/5)])
  have hwclose:=EuclideanClose.width_difference_le hright
    (π/2+(π/2-ω))
  nlinarith

/-- Exact target G.5 prerequisite: every reduced motion has alpha below
500 epsilon^(1/6). -/
theorem effective_angle_entry : Targets.EffectiveAngleEntry := by
  intro P hP hbox S ω hS hω hεpos hε30
  have hα0 : 0≤π/2-ω:=sub_nonneg.mpr hω.2
  refine ⟨hα0,?_⟩
  let a₀:=500*(sofaDeficit P S)^(1/6:ℝ)
  have ha₀ : 0<a₀:=mul_pos (by norm_num)
    (rpow_pos_of_pos hεpos _)
  have ha100 : a₀≤1/100 := by
    have hr:=rpow_le_rpow hεpos.le hε30 (by norm_num : (0:ℝ)≤1/6)
    dsimp [a₀]
    norm_num at hr ⊢
    nlinarith
  by_contra hn
  have ha : a₀≤π/2-ω:=not_lt.mp hn
  have hsmall : sofaDeficit P S≤a₀^6/(10:ℝ)^16 := by
    dsimp [a₀]
    have hs:=rpow_natInv_pow hεpos.le 6
    norm_num at *
    nlinarith
  have hext:=effective_angle_extension hP hbox hS hω rfl hεpos
    ha₀ ha100 ha hsmall
  have h20 : sofaDeficit P S≤1/(10:ℝ)^20 :=
    hε30.trans (by norm_num)
  have hgap:=angle_gap_after_extension hP hbox hS hω rfl h20 hext
  have hcontr : 41200*sqrt (sofaDeficit P S)<a₀ := by
    have hs:=sqrt_eq_rpow (sofaDeficit P S)
    have hp:=rpow_lt_rpow_of_exponent_lt hεpos (by norm_num : (1/6:ℝ)<1/2)
      (hε30.trans_lt (by norm_num : (1/(10:ℝ)^30)<1))
    dsimp [a₀]
    rw [hs]
    nlinarith
  linarith

end MovingSofaQuantitative
