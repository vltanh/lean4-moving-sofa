module

public import MovingSofaQuantitative.CenteredCap
public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.OrthogonalErosion
public import MovingSofaStability.Recovery
public import MovingSofaUniqueness.Selection
public import MovingSofaUniqueness.Maximizing

/-!
# Effective right-angle regularization

UNCOMPILED SOURCE.  This is the source version of note 26.  It keeps the
penalty error instead of sending it to zero.

The comparison cap is auxiliary.  The final estimates concern the specified
input cap and the original sofa.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def supportL2Penalty (K C : Set Point) : ℝ :=
  ∫ t in (0:ℝ)..π,(supp C t-supp K t)^2

def rightAnglePenaltyLambda (e : ℝ) : ℝ :=
  1/(65536*sqrt e)

/-- Every positive-area right-angle cap has width below nine. -/
theorem positive_cap_width_lt_nine {K : Set Point}
    (hK : IsCap K (π/2)) (hA : 0<sofaArea (π/2) K) :
    horizontalWidth K<9 := by
  let W:=horizontalWidth K
  have htri : max 0 (W/2-sqrt 2)^2≤area (niche K (π/2)) :=
    inner_floor_triangle_area_lower hK
  have harea : sofaArea (π/2) K≤W-max 0 (W/2-sqrt 2)^2 := by
    unfold sofaArea
    have hKarea:=cap_area_le_width hK
    nlinarith
  by_contra hn
  have hW : 9≤W:=not_lt.mp hn
  have hs : sqrt 2<3/2 := by
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  have hm : W-(W/2-sqrt 2)^2≤0 := by
    have hcoarse : (W/2-3/2)^2≤(W/2-sqrt 2)^2 := by
      nlinarith
    have hz : W-(W/2-3/2)^2≤0 := by
      ring_nf
      nlinarith [hW]
    nlinarith
  have hmax : max 0 (W/2-sqrt 2)^2=(W/2-sqrt 2)^2 := by
    rw [max_eq_right]
    positivity
  rw [hmax] at harea
  linarith

/-- Centering a positive-area cap puts it in the radius-five box. -/
theorem centered_positive_cap_radius_five {K : Set Point}
    (hK : IsCap K (π/2)) (hA : 0<sofaArea (π/2) K) :
    ∀p∈centeredReference K K,norm2 p<5 := by
  have hW:=positive_cap_width_lt_nine hK hA
  intro p hp
  have hx:=centered_cap_horizontal_bound hK hW p hp
  have hy:=hK.snd_le_one
    (centeredReference_self_mem hK p hp)
  have hy0:=hK.snd_nonneg
    (centeredReference_self_mem hK p hp)
  unfold norm2 dot
  nlinarith [Real.sq_sqrt (by positivity : 0≤p.1^2+p.2^2)]

/-- L2 closeness plus a Lipschitz bound controls the supremum by a cubic
one-dimensional estimate. -/
theorem sup_le_of_L2_lipschitz {f : ℝ→ℝ} {P L D : ℝ}
    (hP : supportSquareIntegral f≤P)
    (hL : LipschitzWith L f) (hL0 : 0≤L)
    (hD : ∀t∈Icc (0:ℝ) π,|f t|≤D) :
    (sSup (|f| '' Icc (0:ℝ) π))^3≤8*L*P := by
  obtain ⟨t,ht,hmax⟩:=compact_abs_max continuousOn_of_lipschitz hL
  let M:=|f t|
  rcases eq_or_lt_of_le (abs_nonneg (f t)) with hzero|hM
  · simp [hzero]
  · let r:=M/(2*L)
    have hside:=one_sided_interval_inside ht
    have hlower : ∀u∈hside.interval r, M/2≤|f u| := by
      intro u hu
      have hd:=hL.dist_le_mul u t
      rw [Real.dist_eq] at hd
      nlinarith [abs_sub_abs_le_abs_sub (f u) (f t)]
    have hmeasure : M/(2*L)≤volume.real (hside.interval r) :=
      one_sided_interval_length ht hM hL0
    have hint:=integral_square_lower_on_interval hlower hmeasure
    have hsup:=hint.trans hP
    rw [show sSup (|f| '' Icc (0:ℝ) π)=M by exact hmax] 
    nlinarith

/-- Compact existence of the integral-penalized comparison cap.  It is obtained
as the Hausdorff limit of the existing finite penalized polygon maximizers;
uniform convergence of supports turns sampled penalties into the integral
penalty. -/
theorem exists_integral_penalized_cap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    {e λ : ℝ} (he : 0<e) (hλ : 0<λ)
    (hAe : sofaArea (π/2) K=area (gerverSofa P)-e) :
    ∃ C : Set Point,IsCap C (π/2) ∧
      sofaArea (π/2) C-λ*supportL2Penalty K C≥sofaArea (π/2) K ∧
      supportL2Penalty K C≤e/λ := by
  let Θn:=dyadicAngleSet (π/2) (by positivity) 
  choose Cn hCn hmax using fun n =>
    exists_penalizedMax
      (integralQuadratureSamples (Θn n) K λ)
      K (polyCap (Θn n) K)
      (recovery_positive_from hK hAe he)
  obtain ⟨C,φ,hφ,hconv⟩ :=
    bounded_penalized_caps_subsequence hP hbox hK he hλ Cn hCn
  have hcap:=capH_isCap_limit hφ hconv
  have harea:=polyArea_limsup_to_sofaArea hφ
  have hpen:=quadrature_penalty_tendsto_integral hK hcap hφ
  refine ⟨C,hcap,?_,?_⟩
  · apply le_of_tendsto_of_tendsto
      (dyadic_recovery_ge_integral hK λ) harea hpen
  · have hglobal:=right_angle_cap_area_le_gerver
      (gerver_maximizing_value hP hbox) hcap
    nlinarith [hglobal]

/-- The comparison cap stays uniformly bounded even though the penalty target
is not centered at its own midpoint. -/
theorem penalized_cap_radius_bound {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K C : Set Point} (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    {e : ℝ} (he : 0<e) (he4 : e≤1/(10:ℝ)^4)
    (hA : sofaArea (π/2) C≥area (gerverSofa P)-e)
    (hpen : supportL2Penalty K C≤65536*e^(3/2:ℝ)) :
    ∀p∈C,norm2 p<26 := by
  have hCpos : 0<sofaArea (π/2) C := by
    have hM: (22/10:ℝ)<area (gerverSofa P):=(gerverSofa_area_mem hP hbox).1.trans (by norm_num)
    nlinarith
  have hW:=positive_cap_width_lt_nine hC hCpos
  let m:=horizontalMidpoint C
  have hm : |m|<21 := by
    have hL2:=center_shift_L2_lower hK hC
    have hroot:=sqrt_le_sqrt hpen
    have hpi:=pi_gt_three
    nlinarith [hL2,hroot]
  intro p hp
  have hx:=cap_fst_centered_bound hC hW p hp
  have hy0:=hC.snd_nonneg hp
  have hy1:=hC.snd_le_one hp
  unfold norm2 dot
  nlinarith

/-- Cubic support control from the comparison penalty. -/
theorem penalized_support_sup {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K C : Set Point} (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    {e : ℝ} (he : 0<e) (he4 : e≤1/(10:ℝ)^4)
    (hA : sofaArea (π/2) C≥area (gerverSofa P)-e)
    (hpen : supportL2Penalty K C≤65536*e^(3/2:ℝ)) :
    ∀t∈Icc (0:ℝ) π,|supp C t-supp K t|≤256*sqrt e := by
  have hCr:=penalized_cap_radius_bound hP hbox hK hC he he4 hA hpen
  have hKr:=arbitrary_positive_cap_radius_five hK (by
    have hglobal:=right_angle_cap_area_le_gerver
      (gerver_maximizing_value hP hbox) hK
    nlinarith [hA])
  have hLip : LipschitzWith 32 (fun t=>supp C t-supp K t) :=
    support_difference_lipschitz_of_radius hC.2.1 hK.2.1 hCr hKr
  have hcube:=sup_le_of_L2_lipschitz
    (f:=fun t=>supp C t-supp K t)
    (P:=65536*e^(3/2:ℝ)) (L:=32) (D:=32)
    (by simpa [supportL2Penalty] using hpen) hLip (by norm_num)
    (fun t ht=>support_difference_bound_of_radius hCr hKr t)
  have hs:=sqrt_nonneg e
  have hs2:=sq_sqrt he.le
  have hpow : e^(3/2:ℝ)=e*sqrt e := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,rpow_add he,Real.rpow_one,sqrt_eq_rpow]
  rw [hpow] at hcube
  intro t ht
  have hmax:=le_csSup (bounded_abs_support_difference hCr hKr)
    ⟨|supp C t-supp K t|,⟨t,ht,rfl⟩⟩
  nlinarith

/-- The retained polygon variation gives an approximate curvature inequality
for the integral-penalized cap. -/
theorem penalized_curvature_error {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K C : Set Point} (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    {e : ℝ} (he : 0<e) (he4 : e≤1/(10:ℝ)^4)
    (hmax : PenalizedCapMax K C (rightAnglePenaltyLambda e))
    (hD : ∀t∈Icc (0:ℝ) π,|supp C t-supp K t|≤256*sqrt e) :
    ApproxCurvatureArms C (1/32) := by
  let λ:=rightAnglePenaltyLambda e
  have hη : 8*λ*(256*sqrt e)≤1/32 := by
    unfold λ rightAnglePenaltyLambda
    field_simp [sqrt_pos.mpr he |>.ne']
    norm_num
  exact polygon_variation_to_approx_curvature hC hmax hD hη

/-- Robust arm bootstrap: the 1/32 error still forces every arm to exceed one
with a strict linear margin. -/
theorem approx_curvature_implies_Ki {K : Set Point}
    (hK : IsCap K (π/2))
    (hA : (22/10:ℝ)<sofaArea (π/2) K)
    (hcurv : ApproxCurvatureArms K (1/32)) :
    IsKi K := by
  obtain ⟨f,g,hfg,hcurvF,hcurvG⟩:=arms_from_approx_curvature hK hcurv
  have hnonneg:=cap_arms_nonnegative hK
  have hboot:=robust_arm_bootstrap hfg hcurvF hcurvG hnonneg
    (by norm_num : (1/32:ℝ)<1/29)
  exact ki_of_arm_bounds_and_curvature hK hA hcurv hboot

/-- Effective cap entry at right angle. -/
theorem effective_right_angle_cap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    {e : ℝ} (he : e=area (gerverSofa P)-sofaArea (π/2) K)
    (he0 : 0≤e) (he4 : e≤1/(10:ℝ)^4) :
    EuclideanClose (514*sqrt e) K (centeredReference P.cap K) := by
  rcases he0.eq_or_lt with hz|hp
  · have hmax : sofaArea (π/2) K=area (gerverSofa P) := by linarith [he]
    obtain ⟨s,hs,-⟩:=maximizing_cap_eq_gerver
      (gerver_maximizing_value hP hbox) hK hmax
    rw [hs]
    exact (centeredReference_translate_eq hK (gm_isCap hP hbox) s).symm ▸
      EuclideanClose.refl _ (by positivity)
  · let λ:=rightAnglePenaltyLambda e
    have hλ : 0<λ := by unfold λ rightAnglePenaltyLambda; positivity
    obtain ⟨C,hC,hobj,hPbound⟩ :=
      exists_integral_penalized_cap hP hbox hK hp hλ
        (by rw [he]; ring)
    have hCarea : sofaArea (π/2) C≥area (gerverSofa P)-e := by
      have hnon:=supportL2Penalty_nonneg K C
      unfold λ at hobj
      nlinarith
    have hpen : supportL2Penalty K C≤65536*e^(3/2:ℝ) := by
      have hs:=sq_sqrt hp.le
      unfold λ rightAnglePenaltyLambda at hPbound
      field_simp [sqrt_pos.mpr hp |>.ne'] at hPbound
      simpa [sqrt_eq_rpow,←Real.rpow_natCast] using hPbound
    have hD:=penalized_support_sup hP hbox hK hC hp he4 hCarea hpen
    have hcurv:=penalized_curvature_error hP hbox hK hC hp he4
      (penalized_max_of_global_objective hobj) hD
    have hCki:=approx_curvature_implies_Ki hC
      (by have hM: (2219/1000:ℝ)<area (gerverSofa P):=
            (gerverSofa_area_mem hP hbox).1.trans (by norm_num)
          nlinarith [hCarea,he4])
      hcurv
    have hCG:=centered_ki hP hbox C hCki
    have hCK : EuclideanClose (512*sqrt e)
        C (centeredReference K C) := by
      exact cap_close_of_support_sup hK hC hD |>.mono (by nlinarith)
    have hcenters : EuclideanClose (512*sqrt e)
        (centeredReference K K) (centeredReference K C) :=
      centered_reference_distance_from_support hK hC hD
    have htri:=hcenters.symm.trans hCG
    have href:=centeredReference_self hK
    rw [href] at htri
    exact htri.mono (by
      have hsec:=centeredNumeric P.φ hbox.1
      nlinarith [sqrt_nonneg e])

/-- Right-angle original sofa: coarse effective actual-set stability. -/
theorem effective_right_angle_sofa {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofaWithAngle S (π/2))
    {ε : ℝ} (hε : ε=sofaDeficit P S)
    (hε0 : 0≤ε) (hε20 : ε≤1/(10:ℝ)^20) :
    EuclideanClose (10300*sqrt ε)
      (midpointNormalizedSofa P S) (gerverSofa P) := by
  let N:=midpointNormalizedSofa P S
  have hNm:=midpointNormalizedSofa_movingWithAngle P hS
  have hNc:=ms_isCompact_of_isMovingSofaWithAngle hNm
  have hNn:=hNm.2.1.nonempty
  have htop:=midpointNormalizedSofa_top P
    (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty
  have hstrip:=moving_strip_of_top ⟨π/2,hNm⟩ htop
  let K:=sofaCap N
  have hK:=sofaCap_isCap hNc hNn hstrip htop
  have hpc:=sofaCap_partial_constraints hNm ⟨by positivity,le_rfl⟩ htop
  have hsub : N⊆capShape K := right_angle_sofa_subset_capShape hK hpc
  have hNK : niche K (π/2)⊆K := niche_subset_of_right_angle_movement hK hpc
  let e:=area (gerverSofa P)-sofaArea (π/2) K
  have he0 : 0≤e := sub_nonneg.mpr
    (right_angle_cap_area_le_gerver (gerver_maximizing_value hP hbox) hK)
  have heε : e≤ε := by
    rw [hε,sofaDeficit]
    have harea:=area_mono_of_finite hsub
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
    rw [area_capShape_of_niche_subset hK hNK] at harea
    linarith
  have he4 : e≤1/(10:ℝ)^4 := heε.trans (hε20.trans (by norm_num))
  have hcap:=effective_right_angle_cap hP hbox hK rfl he0 he4
  have href : centeredReference P.cap K=P.cap := by
    have hm:=sofaCap_midpoint_of_midpoint_normalized hP hbox hNm htop hstrip
    exact centeredReference_eq_of_midpoint hm
  rw [href] at hcap
  have hsupport:=hcap.abs_supp_sub_le hK.2.1.2.1
    (gm_isConvexBody_cap hP hbox).2.1 hK.2.1.1
    (gm_isConvexBody_cap hP hbox).1
  have hδ : (514:ℝ)*sqrt e≤514*sqrt ε :=
    mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) (by norm_num)
  have herode:=orthogonal_reference_erosion
    (show 0≤514*sqrt ε by positivity)
    (gm_isCap hP hbox) hK
    (fun t ht => (hsupport t).trans hδ)
  have hmissing : area (capShape K\N)≤ε := by
    rw [area_sdiff_balance hNc.measurableSet
      (measurable_capShape hK) hNc.measure_lt_top.ne
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)]
    rw [area_capShape_of_niche_subset hK hNK,hε,sofaDeficit]
    nlinarith [heε]
  exact effective_disk_recovery_10300 hP hbox hε0 hε20 hsub
    herode hmissing hcap

end MovingSofaQuantitative
