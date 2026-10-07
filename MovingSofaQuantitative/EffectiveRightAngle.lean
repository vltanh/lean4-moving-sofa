module

public import MovingSofaQuantitative.CenteredCap
public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.EffectiveRecovery
public import MovingSofaQuantitative.EffectiveRegularizationSupport
public import MovingSofaQuantitative.MidpointEntry
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

/-- Compact existence of the integral-penalized comparison cap.  It is obtained
as the Hausdorff limit of the existing finite penalized polygon maximizers;
uniform convergence of supports turns sampled penalties into the integral
penalty. -/
theorem exists_integral_penalized_cap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    (hpositive : 0 < sofaArea (π/2) K)
    {e λ : ℝ} (he : 0<e) (hλ : 0<λ)
    (hAe : sofaArea (π/2) K=area (gerverSofa P)-e) :
    ∃ C : Set Point,IsCap C (π/2) ∧
      sofaArea (π/2) C-λ*supportL2Penalty K C≥sofaArea (π/2) K ∧
      supportL2Penalty K C≤e/λ := by
  obtain ⟨C, hpenMax⟩ := exists_integral_penalized_limit hK hpositive hλ
  rcases hpenMax with ⟨hC, hmax⟩
  have hzero : supportL2Penalty K K = 0 := by
    simp [supportL2Penalty]
  have hobj : sofaArea (π/2) K ≤
      sofaArea (π/2) C - λ * supportL2Penalty K C := by
    have h := hmax K hK
    simpa [supportL2Penalty, hzero] using h
  have hglobal := right_angle_cap_area_le_gerver
    (gerver_maximizing_value hP hbox) hC
  have hpenBound : λ * supportL2Penalty K C ≤ e := by
    rw [hAe] at hobj
    linarith
  refine ⟨C, hC, hobj, ?_⟩
  exact (le_div_iff₀ hλ).2 hpenBound

/-- Translation-invariant control of the relative horizontal midpoint.

Both positive-area caps have centered radius below five.  Subtract their
centered support functions: the remainder is uniformly bounded by ten, while
the difference of original supports contains the harmonic
\`(midpoint C - midpoint K) * cos t\`.  Squaring and integrating gives
\`m^2 * (π/2) ≤ 2 * penalty + 200 * π\`.  A penalty at most 1/10
therefore forces \`|m| < 21\`.

An absolute bound on the midpoint of C would be false, since translating
K and C together preserves the hypotheses. -/
theorem center_shift_le_21_of_penalty {K C : Set Point}
    (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    (hKpos : 0<sofaArea (π/2) K)
    (hCpos : 0<sofaArea (π/2) C)
    (hpen : supportL2Penalty K C≤1/10) :
    |horizontalMidpoint C-horizontalMidpoint K|<21 := by
  let m : ℝ := horizontalMidpoint C-horizontalMidpoint K
  let r : ℝ→ℝ := fun t =>
    supp (centeredCopy C) t-supp (centeredCopy K) t
  have hKC : ∀t,|supp (centeredCopy K) t|≤5 := by
    intro t
    exact abs_supp_le_radius (centeredCopy_isCap hK).2.1
      (fun p hp=>(arbitrary_positive_cap_radius_five hK hKpos p hp).le) t
  have hCC : ∀t,|supp (centeredCopy C) t|≤5 := by
    intro t
    exact abs_supp_le_radius (centeredCopy_isCap hC).2.1
      (fun p hp=>(arbitrary_positive_cap_radius_five hC hCpos p hp).le) t
  have hr : ∀t,|r t|≤10 := by
    intro t
    dsimp [r]
    nlinarith [hKC t,hCC t,abs_sub_le_iff.2
      ⟨by nlinarith [hKC t,hCC t],by nlinarith [hKC t,hCC t]⟩]
  have hdecomp : ∀t,supp C t-supp K t=m*cos t+r t := by
    intro t
    unfold r m centeredCopy
    rw [supp_translate_horizontal hC.2.1 (-horizontalMidpoint C) t,
        supp_translate_horizontal hK.2.1 (-horizontalMidpoint K) t]
    ring
  have hpoint : ∀t,(m*cos t)^2≤
      2*(supp C t-supp K t)^2+200 := by
    intro t
    have hbound:=hr t
    have heq:=hdecomp t
    have hsq : (r t)^2≤100 := by
      nlinarith [abs_le.mp hbound,sq_abs (r t)]
    nlinarith [sq_nonneg ((supp C t-supp K t)+r t)]
  have hcos : (∫ t in (0:ℝ)..π,(cos t)^2)=π/2 := by
    simp
  have hint : m^2*(π/2)≤2*supportL2Penalty K C+200*π := by
    have hmono:=intervalIntegral.integral_mono_on pi_pos.le
      (by fun_prop :
        IntervalIntegrable (fun t=>(m*cos t)^2) volume 0 π)
      (by fun_prop :
        IntervalIntegrable (fun t=>
          2*(supp C t-supp K t)^2+200) volume 0 π)
      (fun t ht=>hpoint t)
    convert hmono using 1 <;>
      simp [supportL2Penalty,pow_mul,hcos,
        intervalIntegral.integral_add,intervalIntegral.integral_const] <;> ring
  have hpi : 3<π := pi_gt_three
  by_contra hn
  have hm : 21≤|m| := le_of_not_gt hn
  have hsq : 441≤m^2 := by nlinarith [sq_abs m]
  have hmul := mul_nonneg (sub_nonneg.mpr hsq) pi_pos.le
  nlinarith [hpen,hint,hmul,hpi]

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
    support_difference_lipschitz_of_radius hK.2.1 hC.2.1 hKr hCr
  have htop : (fun t=>supp C t-supp K t) (π/2)=0 := by
    have hKC : supp K (π/2)=1 := hK.2.2.2.1
    have hCC : supp C (π/2)=1 := hC.2.2.2.1
    simp [hKC,hCC]
  have hcube:=sup_le_of_L2_lipschitz
    (f:=fun t=>supp C t-supp K t)
    (P:=65536*e^(3/2:ℝ)) (L:=32)
    (by simpa [supportL2Penalty] using hpen) hLip (by norm_num) htop
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
    have hKpos : 0 < sofaArea (π/2) K := by
      rw [he]
      have hM := (gerverSofa_area_mem hP hbox).1
      linarith [he4]
    obtain ⟨C,hC,hobj,hPbound⟩ :=
      exists_integral_penalized_cap hP hbox hK hKpos hp hλ
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
  have hNK : niche K (π/2)⊆K := by
    dsimp [K]
    exact niche_subset_of_right_angle_movement hNm htop
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
    have hmN := midpointNormalizedSofa_midpoint P
      (ms_isCompact_of_isMovingSofaWithAngle hS) hS.2.1.nonempty
    have hmK := sofaCap_midpoint_of_midpoint_normalized hP hbox
      hNc hNn hstrip htop hmN
    exact centeredReference_eq_of_midpoint hmK
  rw [href] at hcap
  have hsupport:=hcap.abs_supp_sub_le hK.2.1.2.1
    (gm_isConvexBody_cap hP hbox).2.1 hK.2.1.1
    (gm_isConvexBody_cap hP hbox).1
  have hδ : (514:ℝ)*sqrt e≤514*sqrt ε :=
    mul_le_mul_of_nonneg_left (sqrt_le_sqrt heε) (by norm_num)
  have hmissing : area (capShape K\N)≤ε := by
    rw [area_sdiff_balance hNc.measurableSet
      (measurable_capShape hK) hNc.measure_lt_top.ne
      (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)]
    rw [area_capShape_of_niche_subset hK hNK,hε,sofaDeficit]
    nlinarith [heε]
  rcases hε0.eq_or_lt with hz | hp
  · subst ε
    have hzero : sofaDeficit P S=0 := hε.symm
    have hEq:=normalizedSofa_eq_gerver_of_zero_deficit hP hbox ⟨π/2,hS⟩ hzero
    have hmid:=midpoint_entry_of_pinned hP hbox ⟨π/2,hS⟩ le_rfl
      (by simpa [hEq] using (EuclideanClose.refl (gerverSofa P) le_rfl))
    simpa using hmid
  · have hhall : ApproxHallways K N 0 := by
      intro p hp t ht
      have hs:=sofaCap_partial_constraints hNm ⟨by positivity,le_rfl⟩ htop
      simpa using hs.2.1 p hp t ht
    exact effective_coarse_recovery hP hbox hK
      (show N⊆K from hsub.trans sdiff_subset)
      hp hε20 (by positivity) le_rfl hδ (by simp)
      (fun t ht => (hsupport t).trans hδ) hhall hmissing

end MovingSofaQuantitative
