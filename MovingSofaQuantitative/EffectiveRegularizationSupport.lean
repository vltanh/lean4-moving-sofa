module

public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.MidpointEntry
public import MovingSofaQuantitative.CenteredCap
public import MovingSofaUniqueness.Selection
public import MovingSofaUniqueness.Variation
public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.Maximizing
public import MovingSofaUniqueness.Rigid

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
    have hcoarse : (W/2-3/2)^2≤(W/2-sqrt 2)^2 := by nlinarith
    have hz : W-(W/2-3/2)^2≤0 := by ring_nf; nlinarith [hW]
    nlinarith
  have hmax : max 0 (W/2-sqrt 2)^2=(W/2-sqrt 2)^2 := by
    rw [max_eq_right]; positivity
  rw [hmax] at harea
  linarith

/-- Centering a positive-area cap puts it in the radius-five box. -/
theorem centered_positive_cap_radius_five {K : Set Point}
    (hK : IsCap K (π/2)) (hA : 0<sofaArea (π/2) K) :
    ∀p∈centeredReference K K,norm2 p<5 := by
  have hW:=positive_cap_width_lt_nine hK hA
  intro p hp
  have hx:=centered_cap_horizontal_bound hK hW p hp
  have hy:=hK.snd_le_one (centeredReference_self_mem hK p hp)
  have hy0:=hK.snd_nonneg (centeredReference_self_mem hK p hp)
  unfold norm2 dot
  nlinarith [Real.sq_sqrt (by positivity : 0≤p.1^2+p.2^2)]

def centeredCopy (K : Set Point) : Set Point :=
  Rigid.translate (-horizontalMidpoint K,0) '' K

theorem centeredCopy_isCap {K : Set Point} (hK : IsCap K (π/2)) :
    IsCap (centeredCopy K) (π/2) := by
  unfold centeredCopy
  exact isCap_translate_horizontal hK (-horizontalMidpoint K)

theorem centeredCopy_sofaArea {K : Set Point} (hK : IsCap K (π/2)) :
    sofaArea (π/2) (centeredCopy K)=sofaArea (π/2) K := by
  unfold centeredCopy
  exact sofaArea_translate_horizontal hK.2.1 (-horizontalMidpoint K)

theorem centeredCopy_midpoint_zero {K : Set Point} (hK : IsCap K (π/2)) :
    horizontalMidpoint (centeredCopy K)=0 := by
  unfold centeredCopy horizontalMidpoint
  rw [supp_translate_horizontal hK.2.1 (-horizontalMidpoint K) 0,
      supp_translate_horizontal hK.2.1 (-horizontalMidpoint K) π]
  simp [horizontalMidpoint]
  ring

theorem centeredCopy_mem_iff {K : Set Point} (p : Point) :
    p∈centeredCopy K ↔ p+(horizontalMidpoint K,0)∈K := by
  unfold centeredCopy
  rw [Rigid.mem_translate_image]
  constructor <;> intro h
  · simpa [Rigid.translate_apply] using h
  · simpa [Rigid.translate_apply] using h

theorem euclideanDist_translate (a p q : Point) :
    euclideanDist (p+a) (q+a)=euclideanDist p q := by
  unfold euclideanDist
  congr 1
  abel

theorem euclideanClose_translate {A B : Set Point} {r : ℝ}
    (h : EuclideanClose r A B) (a : Point) :
    EuclideanClose r (Rigid.translate a '' A) (Rigid.translate a '' B) := by
  constructor
  · rintro _ ⟨p,hp,rfl⟩
    obtain ⟨q,hq,hd⟩:=h.1 p hp
    refine ⟨q+a,⟨q,hq,by simp [Rigid.translate_apply]⟩,?_⟩
    simpa [Rigid.translate_apply,euclideanDist_translate] using hd
  · rintro _ ⟨q,hq,rfl⟩
    obtain ⟨p,hp,hd⟩:=h.2 q hq
    refine ⟨p+a,⟨p,hp,by simp [Rigid.translate_apply]⟩,?_⟩
    simpa [Rigid.translate_apply,euclideanDist_translate] using hd

theorem centeredReference_translate_to_centeredCopies {G K : Set Point} :
    Rigid.translate (-horizontalMidpoint K,0) '' centeredReference G K =
      centeredCopy G := by
  unfold centeredReference horizontalReference centeredCopy
  ext p
  simp only [Rigid.mem_translate_image,Rigid.translate_apply]
  constructor
  · rintro ⟨q,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨z,hz,?_⟩
    ext <;> simp [horizontalMidpoint] <;> ring
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z+(horizontalMidpoint K-horizontalMidpoint G,0),
      ⟨z,hz,by rfl⟩,?_⟩
    ext <;> simp [horizontalMidpoint] <;> ring

theorem centeredCopy_translate_back {K : Set Point} :
    Rigid.translate (horizontalMidpoint K,0) '' centeredCopy K=K := by
  unfold centeredCopy
  ext p
  simp [Rigid.mem_translate_image,Rigid.translate_apply]
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa using hq
  · intro hp
    refine ⟨p+(-horizontalMidpoint K,0),?_,?_⟩
    · simpa using hp
    · ext <;> simp <;> ring

theorem abs_supp_le_radius {K : Set Point} (hK : IsConvexBody K)
    {R : ℝ} (hR : ∀p∈K,norm2 p≤R) (t : ℝ) :
    |supp K t|≤R := by
  obtain ⟨p,hp,hpeq⟩:=exists_dot_eq_supp hK.2.1 hK.1 t
  rw [←hpeq,abs_le]
  constructor
  · have hd:=dot_uvec_le_norm2 (-p) t
    simpa [dot_neg_left] using hd.trans (hR p hp)
  · exact (dot_uvec_le_norm2 p t).trans (hR p hp)

theorem area_isosceles_triangle (m : ℝ) {h : ℝ} (hh : 0≤h) :
    area {p : Point | p.2∈Icc (0:ℝ) h ∧ |p.1-m|≤h-p.2}=h^2 := by
  rw [area,Measure.volume_eq_prod]
  rw [Measure.volume_eq_lintegral_prod_snd]
  have hfiber : ∀y : ℝ,
      volume {x : ℝ | y∈Icc (0:ℝ) h ∧ |x-m|≤h-y} =
      if y∈Icc (0:ℝ) h then ENNReal.ofReal (2*(h-y)) else 0 := by
    intro y
    by_cases hy:y∈Icc (0:ℝ) h
    · rw [if_pos hy]
      have he : {x : ℝ | y∈Icc (0:ℝ) h ∧ |x-m|≤h-y} =
          Icc (m-(h-y)) (m+(h-y)) := by
        ext x
        simp [hy,abs_le]
      rw [he,Real.volume_Icc]
      simp [hy.2]
      ring
    · rw [if_neg hy]
      simp [hy]
  simp_rw [hfiber]
  rw [lintegral_ite measurableSet_Icc]
  simp only [lintegral_zero,add_zero]
  rw [←ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_indicator measurableSet_Icc]
    rw [←intervalIntegral.integral_of_le hh,
      intervalIntegral.integral_const_sub_id]
    simp
    ring
  · exact (intervalIntegrable_const.mul
      (intervalIntegrable_const.sub intervalIntegrable_id)).integrableOn
  · filter_upwards with y
    positivity

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
    {p : Point} (hp : p∈centeredCopy K) :
    |p.1|<W/2 := by
  have hc:=centeredCopy_isCap hK
  have hm:=centeredCopy_midpoint_zero hK
  have h0:=dot_le_supp hc.2.1.2.1 hp 0
  have hπ:=dot_le_supp hc.2.1.2.1 hp π
  have hw : horizontalWidth (centeredCopy K)=horizontalWidth K := by
    unfold horizontalWidth centeredCopy
    rw [supp_translate_horizontal hK.2.1 (-horizontalMidpoint K) 0,
      supp_translate_horizontal hK.2.1 (-horizontalMidpoint K) π]
    simp
    ring
  unfold horizontalMidpoint at hm
  unfold horizontalWidth at hw hW
  simp [dot_uvec_zero,dot,uvec_pi] at h0 hπ
  nlinarith

theorem cap_fst_centered_bound {K : Set Point}
    (hK : IsCap K (π/2)) {W : ℝ}
    (hW : horizontalWidth K<W)
    {p : Point} (hp : p∈K) :
    |p.1-horizontalMidpoint K|<W/2 := by
  let q:=p+(-horizontalMidpoint K,0)
  have hq : q∈centeredCopy K := by
    unfold q centeredCopy
    exact ⟨p,hp,by simp [Rigid.translate_apply]⟩
  have hc:=centered_cap_horizontal_bound hK hW hq
  dsimp [q] at hc
  simpa [abs_sub_comm] using hc

theorem support_difference_bound_of_radius {K C : Set Point}
    (hK : IsConvexBody K) (hC : IsConvexBody C)
    {RK RC : ℝ}
    (hKr : ∀p∈K,norm2 p≤RK)
    (hCr : ∀p∈C,norm2 p≤RC)
    (t : ℝ) :
    |supp C t-supp K t|≤RC+RK := by
  have hCs:=abs_supp_le_radius hC hCr t
  have hKs:=abs_supp_le_radius hK hKr t
  nlinarith [abs_sub_le_iff.2 ⟨by nlinarith [hCs,hKs],by nlinarith [hCs,hKs]⟩]

theorem support_difference_lipschitz_of_radius {K C : Set Point}
    (hK : IsConvexBody K) (hC : IsConvexBody C)
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

/-- A common horizontal translation cancels from the difference of two
support functions.  The Lipschitz estimate therefore only needs radii
relative to one shared centre, not absolute radii from the origin. -/
theorem support_difference_lipschitz_common_center {K C : Set Point}
    (hK : IsCap K (π/2)) (hC : IsCap C (π/2))
    {m RK RC : ℝ}
    (hKr : ∀p∈K,norm2 (p-(m,0))≤RK)
    (hCr : ∀p∈C,norm2 (p-(m,0))≤RC) :
    LipschitzWith (RK+RC) (fun t=>supp C t-supp K t) := by
  let K' := Rigid.translate (-m,0) '' K
  let C' := Rigid.translate (-m,0) '' C
  have hK' : IsCap K' (π/2) := isCap_translate_horizontal hK (-m)
  have hC' : IsCap C' (π/2) := isCap_translate_horizontal hC (-m)
  have hKr' : ∀p∈K',norm2 p≤RK := by
    rintro p ⟨q,hq,rfl⟩
    simpa [K',Rigid.translate_apply,Prod.fst_sub,Prod.snd_sub] using hKr q hq
  have hCr' : ∀p∈C',norm2 p≤RC := by
    rintro p ⟨q,hq,rfl⟩
    simpa [C',Rigid.translate_apply,Prod.fst_sub,Prod.snd_sub] using hCr q hq
  have hLip := support_difference_lipschitz_of_radius
    hK'.2.1 hC'.2.1 hKr' hCr'
  have heq : (fun t=>supp C' t-supp K' t) =
      (fun t=>supp C t-supp K t) := by
    funext t
    dsimp [C',K']
    rw [supp_translate_horizontal hC.2.1 (-m) t,
        supp_translate_horizontal hK.2.1 (-m) t]
    ring
  simpa only [heq] using hLip

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
  subset : ∀r≥0, r≤π/2 → interval r⊆Icc (0:ℝ) π
  length : ∀r≥0, r≤π/2 → volume.real (interval r)≥r
  near : ∀r≥0,∀u∈interval r,|u-t|≤r

def one_sided_interval_inside {t : ℝ} (ht : t∈Icc (0:ℝ) π) :
    OneSidedInterval t where
  interval r:=if t≤π/2 then Icc t (t+r) else Icc (t-r) t
  subset r hr hrπ:=by
    split_ifs with h
    · intro u hu
      exact ⟨ht.1.trans hu.1, by linarith [hu.2,h,hrπ]⟩
    · intro u hu
      exact ⟨by linarith [hu.1,ht.1,hrπ,not_le.mp h],hu.2.trans ht.2⟩
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

/-- L2 closeness plus a Lipschitz bound controls the supremum by a cubic
one-dimensional estimate. -/
theorem sup_le_of_L2_lipschitz {f : ℝ→ℝ} {P L : ℝ}
    (hP : supportSquareIntegral f≤P)
    (hL : LipschitzWith L f) (hL0 : 0≤L)
    (hzero : f (π/2)=0) :
    (sSup (|f| '' Icc (0:ℝ) π))^3≤8*L*P := by
  obtain ⟨t,ht,hmax⟩:=compact_abs_max continuousOn_of_lipschitz hL
  let M:=|f t|
  rcases eq_or_lt_of_le (abs_nonneg (f t)) with hMzero | hM
  · simp [hMzero]
  · have hLpos : 0<L := by
      by_contra hn
      have hLz : L=0 := le_antisymm (le_of_not_gt hn) hL0
      have hd := hL.dist_le_mul t (π/2)
      rw [hLz,zero_mul] at hd
      have heq : f t=f (π/2) := dist_le_zero.mp hd
      simp [M,heq,hzero] at hM
    let r:=M/(2*L)
    have hsmall : r≤π/2 := by
      have hd:=hL.dist_le_mul t (π/2)
      rw [hzero,Real.dist_eq,Real.dist_eq] at hd
      have hnear : |t-π/2|≤π := by
        rw [abs_le]
        constructor <;> linarith [ht.1,ht.2,pi_pos]
      have hMbound : M≤L*π := by
        dsimp [M]
        simpa [abs_sub_comm] using
          (show |f t| ≤ L*π from
            (by simpa [sub_zero] using hd).trans
              (mul_le_mul_of_nonneg_left hnear hL0))
      dsimp [r]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hLpos)).2
      nlinarith [hMbound]
    have hside:=one_sided_interval_inside ht
    have hlower : ∀u∈hside.interval r, M/2≤|f u| := by
      intro u hu
      have hd:=hL.dist_le_mul u t
      rw [Real.dist_eq] at hd
      have hnear:=hside.near r (by positivity) u hu
      dsimp [r] at hnear
      nlinarith [abs_sub_abs_le_abs_sub (f u) (f t)]
    have hmeasure : M/(2*L)≤volume.real (hside.interval r) :=
      one_sided_interval_length ht hM hLpos hsmall
    have hmeas : MeasurableSet (hside.interval r) := by
      unfold one_sided_interval_inside
      split <;> exact measurableSet_Icc
    have hintg : IntegrableOn (fun u=>(f u)^2) (hside.interval r) := by
      exact (hL.continuous.pow 2).integrableOn_compact
        (by unfold one_sided_interval_inside; split <;> exact isCompact_Icc)
    have hint:=integral_square_lower_on_interval
      (m:=M/2) (ℓ:=M/(2*L)) (by positivity) (by positivity)
      hmeasure hlower hmeas hintg
    have hsubset:=hside.subset r (by positivity) hsmall
    have hwhole : ∫u in hside.interval r,(f u)^2≤supportSquareIntegral f := by
      unfold supportSquareIntegral
      exact setIntegral_mono_set (by positivity)
        ((hL.continuous.pow 2).integrableOn_compact isCompact_Icc) hsubset
    have hsup:=hint.trans (hwhole.trans hP)
    rw [show sSup (|f| '' Icc (0:ℝ) π)=M by exact hmax]
    dsimp [M,r] at *
    nlinarith


theorem arbitrary_positive_cap_radius_five {K : Set Point}
    (hK : IsCap K (π/2)) (hA : 0<sofaArea (π/2) K) :
    ∀p∈centeredCopy K,norm2 p<5 := by
  have hW:=positive_cap_width_lt_nine hK hA
  intro p hp
  have hx:=centered_cap_horizontal_bound hK hW hp
  have hc:=centeredCopy_isCap hK
  have hy0:=hc.snd_nonneg hp
  have hy1:=hc.snd_le_one hp
  unfold norm2 dot
  nlinarith [Real.sq_sqrt (by positivity : 0≤p.1^2+p.2^2)]

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
  rw [centeredReference_self]
  unfold centeredReference horizontalReference horizontalMidpoint
  let a:=(supp C 0-supp C π)/2-(supp K 0-supp K π)/2
  have h0:=h 0 ⟨le_rfl,pi_pos.le⟩
  have hπ:=h π ⟨pi_pos.le,le_rfl⟩
  have ha : |a|≤δ := by
    dsimp [a]
    rw [abs_le] at h0 hπ ⊢
    constructor <;> linarith [h0.1,h0.2,hπ.1,hπ.2]
  exact (close_horizontal_translate K a).symm.mono ha

/-- Midpoint alignment of the *same reference* cap at two comparison
midpoints. This is a comparison of two translated copies of G, not a
comparison of a cap C with a translated copy of an unrelated cap K. -/
theorem centered_reference_alignment_of_support {G K C : Set Point} {δ : ℝ}
    (h : ∀ t ∈ Icc (0:ℝ) π, |supp C t - supp K t| ≤ δ)
    (hδ : 0 ≤ δ) :
    EuclideanClose δ (centeredReference G C) (centeredReference G K) := by
  let a := horizontalMidpoint C - horizontalMidpoint K
  have h0 := abs_le.mp (h 0 ⟨le_rfl, pi_pos.le⟩)
  have hπ := abs_le.mp (h π ⟨pi_pos.le, le_rfl⟩)
  have ha : |a| ≤ δ := by
    dsimp [a, horizontalMidpoint]
    apply abs_le.mpr
    constructor <;> linarith [h0.1, h0.2, hπ.1, hπ.2]
  have heq : centeredReference G C =
      Rigid.translate (a, 0) '' centeredReference G K := by
    unfold centeredReference horizontalReference
    rw [Rigid.coe_translate]
    simp only [Set.image_image, Function.comp_def]
    congr 1
    funext p
    ext <;> simp [a, horizontalMidpoint, Prod.fst_add, Prod.snd_add] <;> ring
  rw [heq]
  exact (close_horizontal_translate (centeredReference G K) a).mono ha

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

/-- At right angle the stability cap agrees with Baek's cap of the
standard-position sofa. -/
theorem sofaCap_eq_capOf_right_angle {S : Set Point}
    (hS : IsMovingSofaWithAngle S (π/2))
    (htop : supp S (π/2)=1) :
    sofaCap S=capOf S (π/2) := by
  have hc:=ms_isCompact_of_isMovingSofaWithAngle hS
  have hn:=hS.2.1.nonempty
  have hstrip:=moving_strip_of_top ⟨π/2,hS⟩ htop
  have hSC:=sofaCap_isCap hc hn hstrip htop
  have hstd:IsStandardPosition S (π/2):=⟨htop,htop⟩
  have hCO:=theorem2_4_1 pi_div_two_mem_Ioc hS hstd
  apply caps_eq_of_upper_supports hSC hCO
  intro t ht
  have hJ:=ht
  rw [sofaCap_upper_support hc hn hstrip htop
      (by rcases ht with ht|ht <;> constructor <;> linarith [ht.1,ht.2,pi_pos])]
  exact (lemma2_3_5_supp pi_div_two_mem_Ioc hS hstd hJ).2.symm

/-- The full right-angle cap of an actual moving sofa contains its niche.
This is an immediate consequence of Baek's connected-monotonization
criterion, avoiding a separate floor-wedge API. -/
theorem niche_subset_of_right_angle_movement {S : Set Point}
    (hS : IsMovingSofaWithAngle S (π/2))
    (htop : supp S (π/2)=1) :
    niche (sofaCap S) (π/2)⊆sofaCap S := by
  have hstd:IsStandardPosition S (π/2):=⟨htop,htop⟩
  have hcapOf:=theorem2_4_1 pi_div_two_mem_Ioc hS hstd
  have hmono:IsMonotoneSofa (monotonization S (π/2)) (π/2) :=
    ⟨pi_div_two_mem_Ioc,S,hS,hstd,rfl⟩
  have hconn: IsConnected (capOf S (π/2)\niche (capOf S (π/2)) (π/2)) := by
    rw [←theorem2_4_2 pi_div_two_mem_Ioc hS hstd]
    exact hmono.isMovingSofaWithAngle.2.1
  have hN : niche (capOf S (π/2)) (π/2)⊆capOf S (π/2) :=
    ((theorem2_5_8 hcapOf).out 4 1).1 hconn
  rw [sofaCap_eq_capOf_right_angle hS htop]
  exact hN

end MovingSofaQuantitative
