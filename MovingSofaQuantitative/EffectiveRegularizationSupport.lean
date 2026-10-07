module

public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.MidpointEntry
public import MovingSofaQuantitative.CenteredCap
public import MovingSofaUniqueness.Selection
public import MovingSofaUniqueness.Variation
public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.Maximizing

/-!
Support lemmas for effective penalized regularization.

UNCOMPILED SOURCE. This file consolidates the analytic interfaces used by the
right-angle and partial-angle effective-entry arguments. The finite-dimensional
maximizers are the existing dyadic polygon maximizers from the uniqueness
library. No theorem in this file is a headline paper result.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness MovingSofaStability

namespace MovingSofaQuantitative

def supportSquareIntegral (f : ℝ→ℝ) : ℝ :=
  ∫ t in (0:ℝ)..π,(f t)^2

theorem supportL2Penalty_nonneg (K C : Set Point) :
    0≤∫ t in (0:ℝ)..π,(supp C t-supp K t)^2 := by
  exact intervalIntegral.integral_nonneg (by intro t; positivity)

theorem inner_floor_triangle_area_lower {K : Set Point}
    (hK : IsCap K (π/2)) :
    max 0 (horizontalWidth K/2-sqrt 2)^2≤area (niche K (π/2)) := by
  let W:=horizontalWidth K
  let a:=-supp K π
  let b:=supp K 0
  let m:=(a+b)/2
  let h:=max 0 (W/2-sqrt 2)
  have htri :
      {p : Point | p.2∈Icc (0:ℝ) h ∧ |p.1-m|≤h-p.2}
        ⊆ niche K (π/2) := by
    intro p hp
    rw [mem_niche_iff_slacks K p]
    refine ⟨hp.1.1,π/4,by constructor <;> positivity,?_,?_⟩
    all_goals
      simp [horizontalWidth,a,b,m,h,dot,uvec] at *
      nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]
  have harea:=area_mono_of_finite htri
    (volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne)
  have htriArea :
      area {p : Point | p.2∈Icc (0:ℝ) h ∧ |p.1-m|≤h-p.2}=h^2 := by
    exact area_isosceles_triangle m (by positivity)
  rw [htriArea]
  exact harea

theorem centered_cap_horizontal_bound {K : Set Point}
    (hK : IsCap K (π/2)) {W : ℝ}
    (hW : horizontalWidth K<W)
    {p : Point} (hp : p∈centeredReference K K) :
    |p.1|<W/2 := by
  have href:=centeredReference_self hK
  rw [href] at hp
  have h0:=dot_le_supp hK.2.1.2.1 hp 0
  have hπ:=dot_le_supp hK.2.1.2.1 hp π
  have hm:=centeredReference_midpoint_zero hK
  unfold horizontalWidth at hW
  simp [dot_uvec_zero,dot,uvec_pi] at h0 hπ
  unfold horizontalMidpoint at hm
  nlinarith

theorem cap_fst_centered_bound {K : Set Point}
    (hK : IsCap K (π/2)) {W : ℝ}
    (hW : horizontalWidth K<W)
    {p : Point} (hp : p∈K) :
    |p.1-horizontalMidpoint K|<W/2 := by
  have hs:=centeredReference_mem_iff hK p
  have hc:=centered_cap_horizontal_bound hK hW (hs.mpr hp)
  simpa [centeredReference,horizontalReference,Rigid.translate_apply] using hc

theorem support_difference_bound_of_radius {K C : Set Point}
    (hK : IsCompact K) (hC : IsCompact C)
    {RK RC : ℝ}
    (hKr : ∀p∈K,norm2 p≤RK)
    (hCr : ∀p∈C,norm2 p≤RC)
    (t : ℝ) :
    |supp C t-supp K t|≤RC+RK := by
  have hCs:=abs_supp_le_radius hC hCr t
  have hKs:=abs_supp_le_radius hK hKr t
  nlinarith [abs_sub_le_iff.2 ⟨by nlinarith [hCs,hKs],by nlinarith [hCs,hKs]⟩]

theorem support_difference_lipschitz_of_radius {K C : Set Point}
    (hK : IsCompact K) (hC : IsCompact C)
    {RK RC : ℝ}
    (hKr : ∀p∈K,norm2 p≤RK)
    (hCr : ∀p∈C,norm2 p≤RC) :
    LipschitzWith (RK+RC) (fun t=>supp C t-supp K t) := by
  intro s t
  rw [Real.dist_eq,Real.dist_eq]
  have h1:=support_angle_bound hC (by positivity) hCr s t
  have h2:=support_angle_bound hK (by positivity) hKr s t
  nlinarith [abs_sub_abs_le_abs_sub
    (supp C s-supp C t) (supp K s-supp K t)]

theorem bounded_abs_support_difference {K C : Set Point}
    (hK : IsCompact K) (hC : IsCompact C)
    {RK RC : ℝ}
    (hKr : ∀p∈K,norm2 p≤RK)
    (hCr : ∀p∈C,norm2 p≤RC) :
    BddAbove (|fun t=>supp C t-supp K t| '' Icc (0:ℝ) π) := by
  refine ⟨RK+RC,?_⟩
  rintro y ⟨t,ht,rfl⟩
  exact support_difference_bound_of_radius hK hC hKr hCr t

theorem continuousOn_of_lipschitz {f : ℝ→ℝ} {L : ℝ}
    (h : LipschitzWith L f) : ContinuousOn f (Icc (0:ℝ) π) :=
  h.continuous.continuousOn

theorem compact_abs_max {f : ℝ→ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) π)) :
    ∃t∈Icc (0:ℝ) π,
      sSup (|f| '' Icc (0:ℝ) π)=|f t| := by
  have hc : IsCompact (|f| '' Icc (0:ℝ) π) :=
    isCompact_Icc.image_of_continuousOn (continuous_abs.comp_continuousOn hf)
  obtain ⟨y,hy,hmax⟩:=hc.exists_isMaxOn
    ⟨|f 0|,⟨0,by simp [pi_pos.le],rfl⟩⟩ continuous_id.continuousOn
  obtain ⟨t,ht,rfl⟩:=hy.1
  exact ⟨t,ht,csSup_eq hmax⟩

structure OneSidedInterval (t : ℝ) where
  interval : ℝ→Set ℝ
  subset : ∀r≥0,interval r⊆Icc (0:ℝ) π
  length : ∀r≥0, r≤π/2 → volume.real (interval r)≥r
  near : ∀r≥0,∀u∈interval r,|u-t|≤r

def one_sided_interval_inside {t : ℝ} (ht : t∈Icc (0:ℝ) π) :
    OneSidedInterval t where
  interval r:=if t≤π/2 then Icc t (t+r) else Icc (t-r) t
  subset r hr:=by
    split_ifs with h
    · intro u hu; exact ⟨ht.1,by linarith [hu.2,pi_pos]⟩
    · intro u hu; exact ⟨by linarith [hu.1,ht.2,pi_pos],ht.2⟩
  length r hr hrπ:=by
    split_ifs <;> simp [Real.volume_Icc,hr]
  near r hr u hu:=by
    split_ifs at hu <;> rw [abs_le] <;> constructor <;> linarith [hu.1,hu.2]

theorem one_sided_interval_length {t M L : ℝ}
    (ht : t∈Icc (0:ℝ) π) (hM : 0<M) (hL : 0<L)
    (hsmall : M/(2*L)≤π/2) :
    M/(2*L)≤volume.real ((one_sided_interval_inside ht).interval (M/(2*L))) :=
  (one_sided_interval_inside ht).length _ (by positivity) hsmall

theorem integral_square_lower_on_interval {f : ℝ→ℝ} {I : Set ℝ} {m ℓ : ℝ}
    (hm : 0≤m) (hℓ : 0≤ℓ)
    (hI : ℓ≤volume.real I)
    (hf : ∀u∈I,m≤|f u|)
    (hmeas : MeasurableSet I)
    (hint : IntegrableOn (fun u=>(f u)^2) I) :
    m^2*ℓ≤∫u in I,(f u)^2 := by
  have hpoint : ∀u∈I,m^2≤(f u)^2 := by
    intro u hu
    nlinarith [hf u hu,abs_nonneg (f u),sq_abs (f u)]
  have hmInt:=integral_mono_on hmeas integrableOn_const hint
    (fun u hu=>hpoint u hu)
  simp [MeasureTheory.integral_const,hm] at hmInt
  nlinarith

theorem center_shift_L2_lower {K C : Set Point}
    (hK : IsCap K (π/2)) (hC : IsCap C (π/2)) :
    π/2*(horizontalMidpoint C-horizontalMidpoint K)^2≤
      ∫t in (0:ℝ)..π,(supp C t-supp K t)^2 := by
  exact support_midpoint_l2_lower hK hC

abbrev arbitrary_positive_cap_radius_five := centered_positive_cap_radius_five

def PenalizedCapMax (target C : Set Point) (λ : ℝ) : Prop :=
  IsCap C (π/2) ∧
  ∀D,IsCap D (π/2) →
    sofaArea (π/2) D-λ*(∫t in (0:ℝ)..π,(supp D t-supp target t)^2)≤
      sofaArea (π/2) C-λ*(∫t in (0:ℝ)..π,(supp C t-supp target t)^2)

theorem penalized_max_of_global_objective {target C : Set Point} {λ : ℝ}
    (hC : IsCap C (π/2))
    (h : ∀D,IsCap D (π/2) →
      sofaArea (π/2) D-λ*(∫t in (0:ℝ)..π,(supp D t-supp target t)^2)≤
      sofaArea (π/2) C-λ*(∫t in (0:ℝ)..π,(supp C t-supp target t)^2)) :
    PenalizedCapMax target C λ := ⟨hC,h⟩

theorem exists_integral_penalized_limit {K : Set Point}
    (hK : IsCap K (π/2)) (hpositive : 0<sofaArea (π/2) K)
    {λ : ℝ} (hλ : 0<λ) :
    ∃C,PenalizedCapMax K C λ := by
  let hω : (π/2:ℝ)∈Ioc 0 (π/2):=⟨by positivity,le_rfl⟩
  choose Cn hCn using fun n=>exists_dyadic_penalizedMax hω hK hpositive n
  obtain ⟨R,hR,hbox⟩:=selected_sequence_bounded hω hK hpositive Cn hCn
  have hcbody : ∀n,IsConvexBody (Cn n):=fun n=>(hCn n).1.1.2.1
  obtain ⟨C,hC,-,φ,hφ,hlim⟩:=mpc_blaschke hcbody
    (isCompact_Icc.prod isCompact_Icc) hbox
  have hcap:=mpc_limit_isCap hω (fun _=>rfl)
    (fun n=>(hCn (φ n)).1) hC hlim
  have hobj:=integral_penalty_limsup_of_dyadic hK hλ hφ hCn hbox hlim
  exact ⟨C,⟨hcap,hobj⟩⟩

structure ApproxCurvatureArms (K : Set Point) (η : ℝ) : Prop where
  first : ∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
    (sigma K (Ioo a b)).toReal≤
      (∫t in a..b,k0 (gPlus K t))+η*(b-a)
  second : ∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
    (sigma K (Ioo (π/2-b) (π/2-a))).toReal≤
      (∫t in a..b,k0 (fPlus K (π/2-t)))+η*(b-a)

theorem polygon_variation_to_approx_curvature {K C : Set Point} {λ η D : ℝ}
    (hC : IsCap C (π/2))
    (hmax : PenalizedCapMax K C λ)
    (hsupp : ∀t∈Icc (0:ℝ) π,|supp C t-supp K t|≤D)
    (hη : 8*λ*D≤η) :
    ApproxCurvatureArms C η := by
  exact quantitative_curvature_from_penalized_variation hC hmax.2 hsupp hη

theorem cap_arms_nonnegative {K : Set Point} (hK : IsCap K (π/2)) :
    (∀t∈Icc (0:ℝ) (π/2),0≤fK K t) ∧
    ∀t∈Icc (0:ℝ) (π/2),0≤gK K t := by
  exact ⟨fun t ht=>(inj_arm_nonneg hK.2.1 t).2.1,
    fun t ht=>(inj_arm_nonneg hK.2.1 t).2.2.1⟩

theorem arms_from_approx_curvature {K : Set Point} {η : ℝ}
    (hK : IsCap K (π/2)) (hcurv : ApproxCurvatureArms K η) :
    ∃f g : ℝ→ℝ,
      (∀t∈Icc (0:ℝ) (π/2),f t=fK K t ∧ g t=gK K t) ∧
      (∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
        f b-f a≤∫t in a..b,k0 (g t)+η*(b-a)) ∧
      (∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
        g b-g a≤∫t in a..b,k0 (f t)+η*(b-a)) := by
  exact approximate_arm_integrals hK hcurv.first hcurv.second

theorem robust_arm_bootstrap {f g : ℝ→ℝ} {η : ℝ}
    (hint :
      (∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
        f b-f a≤∫t in a..b,k0 (g t)+η*(b-a)) ∧
      (∀a b, a∈Icc (0:ℝ) (π/2) → b∈Icc a (π/2) →
        g b-g a≤∫t in a..b,k0 (f t)+η*(b-a)))
    (hnonneg : (∀t∈Icc (0:ℝ) (π/2),0≤f t) ∧
      ∀t∈Icc (0:ℝ) (π/2),0≤g t)
    (hη : η<1/29) :
    ∀t∈Ioo (0:ℝ) (π/2),1<f t ∧ 1<g t := by
  exact robust_lower_sequence_iteration hint hnonneg hη

theorem ki_of_arm_bounds_and_curvature {K : Set Point} {η : ℝ}
    (hK : IsCap K (π/2)) (hA : (22/10:ℝ)<sofaArea (π/2) K)
    (hcurv : ApproxCurvatureArms K η)
    (harms : ∀t∈Ioo (0:ℝ) (π/2),1<fK K t ∧ 1<gK K t) :
    IsKi K := by
  exact isKi_of_approx_curvature hK hA hcurv.first hcurv.second harms

theorem cap_close_of_support_sup {K C : Set Point} {δ : ℝ}
    (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    (h : ∀t∈Icc (0:ℝ) π,|supp C t-supp K t|≤δ)
    (hδ : 0≤δ) :
    EuclideanClose δ C K :=
  upperSupportClose_euclidean hδ hC hK h

theorem centered_reference_distance_from_support {K C : Set Point} {δ : ℝ}
    (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    (h : ∀t∈Icc (0:ℝ) π,|supp C t-supp K t|≤δ)
    (hδ : 0≤δ) :
    EuclideanClose δ (centeredReference K K) (centeredReference K C) := by
  exact centered_reference_lipschitz hK hC h hδ

theorem maximizing_cap_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2))
    (hmax : sofaArea (π/2) K=area (gerverSofa P)) :
    ∃a : ℝ,K=Rigid.translate (a,0) '' P.cap ∧
      capShape K=Rigid.translate (a,0) '' gerverSofa P := by
  exact (right_angle_maximizes_iff_translate_gerver hP hbox hK).1 hmax

theorem right_angle_sofa_subset_capShape {K S : Set Point}
    (hK : IsCap K (π/2))
    (hcon : PartialSofaConstraints K S (π/2)) :
    S⊆capShape K := by
  intro p hp
  refine ⟨hcon.1 hp,?_⟩
  intro hn
  obtain ⟨hy,t,ht,hU,hV⟩:=(mem_niche_iff_slacks K p).1 hn
  have hf:=hcon.2.1 p hp t ht.le
  exact (not_lt_of_ge hf) (max_lt hU hV)

theorem niche_subset_of_right_angle_movement {K S : Set Point}
    (hK : IsCap K (π/2))
    (hcon : PartialSofaConstraints K S (π/2))
    (hconn : IsConnected S)
    (hcap : K=sofaCap S) :
    niche K (π/2)⊆K := by
  exact connected_motion_niche_subset hK hcon hconn hcap

end MovingSofaQuantitative
