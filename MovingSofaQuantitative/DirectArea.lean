module

public import MovingSofaQuantitative.ReferenceExplicitMargins
public import MovingSofaQuantitative.ExplicitBudget
public import MovingSofaStability.Recovery

/-!
# Direct symmetric-difference estimate

UNCOMPILED SOURCE.  The estimate compares the full-angle envelope directly
with Gerver's sofa; it does not first convert the 2.3 Hausdorff estimate into
an area estimate.

For support error delta,
  |U \ G| <= (62307/2500) delta + 4 delta^2.
Together with the complementary terminal budget and centered cap coefficient
1001/1000 this gives 50 sqrt(epsilon).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped Pointwise
open MovingSofaOptimality MovingSofaStability

namespace MovingSofaQuantitative

def horizontalSegment (δ : ℝ) : Set Point := Icc (-δ) δ ×ˢ ({0} : Set ℝ)
def verticalSegment (δ : ℝ) : Set Point := ({0} : Set ℝ) ×ˢ Icc (-δ) δ

theorem horizontalSegment_isConvexBody {δ : ℝ} (hδ : 0≤δ) :
    IsConvexBody (horizontalSegment δ) := by
  refine ⟨⟨(0,0),by simp [horizontalSegment,hδ]⟩,
    isCompact_Icc.prod isCompact_singleton,convex_Icc.prod convex_singleton⟩

theorem verticalSegment_isConvexBody {δ : ℝ} (hδ : 0≤δ) :
    IsConvexBody (verticalSegment δ) := by
  refine ⟨⟨(0,0),by simp [verticalSegment,hδ]⟩,
    isCompact_singleton.prod isCompact_Icc,convex_singleton.prod convex_Icc⟩

theorem horizontalSegment_supp_zero {δ : ℝ} (hδ : 0≤δ) :
    supp (horizontalSegment δ) 0=δ := by
  apply le_antisymm
  · apply supp_le_of_forall (horizontalSegment_isConvexBody hδ).1
    rintro p ⟨hp,-⟩
    simpa [dot_uvec_zero] using hp.2
  · have h:=dot_le_supp (horizontalSegment_isConvexBody hδ).2.1
      ⟨(δ,0),by simp [horizontalSegment,hδ]⟩ 0
    simpa [dot_uvec_zero] using h

theorem horizontalSegment_supp_pi {δ : ℝ} (hδ : 0≤δ) :
    supp (horizontalSegment δ) π=δ := by
  apply le_antisymm
  · apply supp_le_of_forall (horizontalSegment_isConvexBody hδ).1
    rintro p ⟨hp,-⟩
    simp only [dot,uvec_pi]
    linarith [hp.1]
  · have h:=dot_le_supp (horizontalSegment_isConvexBody hδ).2.1
      ⟨(-δ,0),by simp [horizontalSegment,hδ]⟩ π
    simpa [dot,uvec_pi] using h

def horizontalWidth (K : Set Point) : ℝ := supp K 0+supp K π

/-- Square parallel set, written as two segment dilations so Cavalieri can be
applied one coordinate at a time. -/
def horizontalThickening (K : Set Point) (δ : ℝ) : Set Point :=
  K + horizontalSegment δ

def squareThickening (K : Set Point) (δ : ℝ) : Set Point :=
  horizontalThickening K δ + verticalSegment δ

/-- Every Euclidean delta-neighbor lies in the square thickening. -/
theorem euclidean_parallel_subset_square {K L : Set Point} {δ : ℝ}
    (hδ : 0≤δ) (hK : IsCompact K)
    (hclose : DirectedClose δ L K) :
    L⊆squareThickening K δ := by
  intro p hp
  obtain ⟨q,hq,hd⟩ := hclose p hp
  have hx := (abs_fst_le_norm2 (p-q)).trans hd
  have hy := (abs_snd_le_norm2 (p-q)).trans hd
  refine ⟨q+(p.1-q.1,0),?_,(0,p.2-q.2),?_,?_⟩
  · exact ⟨q,hq,(p.1-q.1,0),⟨abs_le.mp hx,by simp⟩,rfl⟩
  · exact ⟨by simp,abs_le.mp hy⟩
  · ext <;> simp <;> ring

/-- Horizontal sections of a compact convex set are intervals. -/
theorem convex_horizontal_fiber_interval {K : Set Point}
    (hK : IsConvexBody K) (y : ℝ) :
    ∃ a b : ℝ, {x | (x,y)∈K}=Icc a b ∨ {x | (x,y)∈K}=∅ := by
  by_cases hn : ∃x,(x,y)∈K
  · have hc : IsCompact {x : ℝ | (x,y)∈K} :=
      hK.2.1.preimage_of_continuousOn (by fun_prop)
        (isClosed_embedding_prodMk_right y)
    have hv : Convex ℝ {x : ℝ | (x,y)∈K} := by
      intro x hx z hz a b ha hb hab
      simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
        smul_eq_mul] using hK.2.2 hx hz ha hb hab
    obtain ⟨a,ha⟩ := hc.exists_isMinOn hn continuous_id.continuousOn
    obtain ⟨b,hb⟩ := hc.exists_isMaxOn hn continuous_id.continuousOn
    refine ⟨a,b,Or.inl ?_⟩
    ext x
    constructor
    · intro hx; exact ⟨ha hx,hb hx⟩
    · intro hx
      have hab : a≤b := ha hb.1
      have hs : x∈segment ℝ a b := by
        simpa [segment_eq_Icc hab] using hx
      exact hv.segment_subset ha.1 hb.1 hs
  · exact ⟨0,0,Or.inr (by ext x; simp [hn])⟩

/-- Extending every nonempty horizontal interval by delta adds exactly 2 delta
to its one-dimensional measure. -/
theorem horizontal_fiber_thickening_length {K : Set Point}
    (hK : IsConvexBody K) {δ : ℝ} (hδ : 0≤δ) (y : ℝ) :
    volume {x : ℝ | (x,y)∈horizontalThickening K δ} =
      if (Set.Nonempty {x : ℝ | (x,y)∈K})
      then volume {x : ℝ | (x,y)∈K}+ENNReal.ofReal (2*δ)
      else 0 := by
  obtain ⟨a,b,hfiber|hfiber⟩ := convex_horizontal_fiber_interval hK y
  · have hab : a≤b := by
      have hn : (Icc a b).Nonempty := by
        rw [←hfiber]
        exact Classical.decEq _ ▸ by simp
      exact hn.some_mem.1.trans hn.some_mem.2
    rw [if_pos (by rw [hfiber]; exact ⟨a,by simp [hab]⟩)]
    rw [hfiber,show {x : ℝ | (x,y)∈horizontalThickening K δ}=
      Icc (a-δ) (b+δ) by
        ext x
        simp [horizontalThickening,hfiber,Set.mem_add]
        constructor
        · rintro ⟨u,hu,v,hv,rfl⟩
          linarith [hu.1,hu.2,hv.1,hv.2]
        · intro hx
          let u:=max a (min x b)
          refine ⟨u,?_,x-u,?_,by ring⟩
          · exact ⟨le_max_left _ _,max_le hab (min_le_right _ _)⟩
          · constructor <;> dsimp [u] <;> linarith [hx.1,hx.2]]
    simp [Real.volume_Icc,hab,hδ]
    rw [←ENNReal.ofReal_add (sub_nonneg.mpr hab) (by positivity)]
    congr 1
    ring
  · rw [if_neg (by simpa [hfiber])]
    have he : {x : ℝ | (x,y)∈horizontalThickening K δ}=∅ := by
      ext x
      simp [horizontalThickening,hfiber,Set.mem_add]
    rw [he,measure_empty]

/-- First Cavalieri step: horizontal dilation adds at most 2 delta because a
right-angle cap has vertical projection of length one. -/
theorem area_horizontalThickening_cap {K : Set Point}
    (hK : IsCap K (π/2)) {δ : ℝ} (hδ : 0≤δ) :
    area (horizontalThickening K δ)≤area K+2*δ := by
  have hmeasK:=hK.2.1.2.1.measurableSet
  have hmeasT : MeasurableSet (horizontalThickening K δ) :=
    (hK.2.1.2.1.add_isCompact (isCompact_Icc.prod isCompact_singleton)).measurableSet
  rw [area,Measure.volume_eq_lintegral_prod_fst hmeasT,
    Measure.volume_eq_lintegral_prod_fst hmeasK]
  have hfiber:=horizontal_fiber_thickening_length hK.2.1 hδ
  have hsupport : {y : ℝ | Set.Nonempty {x : ℝ | (x,y)∈K}}⊆Icc (0:ℝ) 1 := by
    rintro y ⟨x,hx⟩
    exact ⟨hK.snd_nonneg hx,hK.snd_le_one hx⟩
  have hle := lintegral_mono fun y => by
    rw [hfiber y]
    split
    · gcongr
    · simp
  have hmass : ∫⁻ y in {y : ℝ | Set.Nonempty {x : ℝ | (x,y)∈K}},
      ENNReal.ofReal (2*δ) ≤ ENNReal.ofReal (2*δ) := by
    rw [lintegral_const,Measure.restrict_apply_univ]
    have hm := measure_mono hsupport
    rw [Real.volume_Icc] at hm
    simpa using mul_le_of_le_one_right (by positivity) hm
  rw [ENNReal.toReal_le_toReal] <;>
    first | exact hle.trans (by simpa [lintegral_add_left] using hmass)
          | positivity

/-- Vertical sections of a compact convex set are intervals. -/
theorem convex_vertical_fiber_interval {K : Set Point}
    (hK : IsConvexBody K) (x : ℝ) :
    ∃ a b : ℝ, {y | (x,y)∈K}=Icc a b ∨ {y | (x,y)∈K}=∅ := by
  by_cases hn : ∃y,(x,y)∈K
  · have hc : IsCompact {y : ℝ | (x,y)∈K} :=
      hK.2.1.preimage_of_continuousOn (by fun_prop)
        (isClosed_embedding_prodMk_left x)
    have hv : Convex ℝ {y : ℝ | (x,y)∈K} := by
      intro y hy z hz a b ha hb hab
      simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
        smul_eq_mul] using hK.2.2 hy hz ha hb hab
    obtain ⟨a,ha⟩ := hc.exists_isMinOn hn continuous_id.continuousOn
    obtain ⟨b,hb⟩ := hc.exists_isMaxOn hn continuous_id.continuousOn
    refine ⟨a,b,Or.inl ?_⟩
    ext y
    constructor
    · intro hy; exact ⟨ha hy,hb hy⟩
    · intro hy
      have hab : a≤b := ha hb.1
      have hs : y∈segment ℝ a b := by
        simpa [segment_eq_Icc hab] using hy
      exact hv.segment_subset ha.1 hb.1 hs
  · exact ⟨0,0,Or.inr (by ext y; simp [hn])⟩

theorem vertical_fiber_thickening_length {K : Set Point}
    (hK : IsConvexBody K) {δ : ℝ} (hδ : 0≤δ) (x : ℝ) :
    volume {y : ℝ | (x,y)∈K+verticalSegment δ} =
      if (Set.Nonempty {y : ℝ | (x,y)∈K})
      then volume {y : ℝ | (x,y)∈K}+ENNReal.ofReal (2*δ)
      else 0 := by
  obtain ⟨a,b,hfiber|hfiber⟩ := convex_vertical_fiber_interval hK x
  · have hab : a≤b := by
      have hn : (Icc a b).Nonempty := by
        rw [←hfiber]
        exact ⟨a,by simp⟩
      exact hn.some_mem.1.trans hn.some_mem.2
    rw [if_pos (by rw [hfiber]; exact ⟨a,by simp [hab]⟩)]
    rw [hfiber,show {y : ℝ | (x,y)∈K+verticalSegment δ}=Icc (a-δ) (b+δ) by
      ext y
      simp [verticalSegment,Set.mem_add,hfiber]
      constructor
      · rintro ⟨u,hu,v,hv,rfl⟩
        linarith [hu.1,hu.2,hv.1,hv.2]
      · intro hy
        let u:=max a (min y b)
        refine ⟨u,?_,y-u,?_,by ring⟩
        · exact ⟨le_max_left _ _,max_le hab (min_le_right _ _)⟩
        · constructor <;> dsimp [u] <;> linarith [hy.1,hy.2]]
    simp [Real.volume_Icc,hab,hδ]
    rw [←ENNReal.ofReal_add (sub_nonneg.mpr hab) (by positivity)]
    congr 1
    ring
  · rw [if_neg (by simpa [hfiber])]
    have he : {y : ℝ | (x,y)∈K+verticalSegment δ}=∅ := by
      ext y
      simp [verticalSegment,Set.mem_add,hfiber]
    rw [he,measure_empty]

/-- A vertical segment dilation of a compact convex body adds at most
twice delta times its horizontal width. -/
theorem area_verticalThickening_le {K : Set Point}
    (hK : IsConvexBody K) {δ : ℝ} (hδ : 0≤δ) :
    area (K+verticalSegment δ)≤area K+2*δ*(supp K 0+supp K π) := by
  have hmeasK:=hK.2.1.measurableSet
  have hmeasT : MeasurableSet (K+verticalSegment δ) :=
    (hK.2.1.add_isCompact (verticalSegment_isConvexBody hδ).2.1).measurableSet
  rw [area,Measure.volume_eq_lintegral_prod_snd hmeasT,
    Measure.volume_eq_lintegral_prod_snd hmeasK]
  have hfiber:=vertical_fiber_thickening_length hK hδ
  have hsupport :
      {x : ℝ | Set.Nonempty {y : ℝ | (x,y)∈K}}⊆
        Icc (-supp K π) (supp K 0) := by
    rintro x ⟨y,hy⟩
    have h0:=dot_le_supp hK.2.1 hy 0
    have hπ:=dot_le_supp hK.2.1 hy π
    rw [dot_uvec_zero] at h0
    simp only [dot,uvec_pi] at hπ
    exact ⟨by linarith,by linarith⟩
  have hle:=lintegral_mono fun x => by
    rw [hfiber x]
    split
    · gcongr
    · simp
  have hmass :
      ∫⁻x in {x : ℝ | Set.Nonempty {y : ℝ | (x,y)∈K}},
        ENNReal.ofReal (2*δ)≤
      ENNReal.ofReal (2*δ*(supp K 0+supp K π)) := by
    rw [lintegral_const,Measure.restrict_apply_univ]
    have hm:=measure_mono hsupport
    rw [Real.volume_Icc] at hm
    rw [←ENNReal.ofReal_mul (by positivity)]
    gcongr
    simpa [sub_neg_eq_add] using hm
  rw [ENNReal.toReal_le_toReal] <;>
    first
    | exact hle.trans (by simpa [lintegral_add_left] using hmass)
    | positivity

/-- Vertical dilation of the horizontally thickened set adds at most
2 delta times its horizontal span W+2delta. -/
theorem area_squareThickening_cap {K : Set Point}
    (hK : IsCap K (π/2)) {δ : ℝ} (hδ : 0≤δ) :
    area (squareThickening K δ)-area K ≤
      2*(horizontalWidth K+1)*δ+4*δ^2 := by
  have hh := area_horizontalThickening_cap hK hδ
  have hconv : IsConvexBody (horizontalThickening K δ) :=
    convexBody_add hK.2.1 (horizontalSegment_isConvexBody hδ)
  have hspan : horizontalWidth (horizontalThickening K δ)=horizontalWidth K+2*δ := by
    unfold horizontalWidth horizontalThickening
    rw [supp_add,horizontalSegment_supp_zero hδ,horizontalSegment_supp_pi hδ]
    ring
  have hv := area_verticalThickening_le hconv hδ
  unfold squareThickening at hv
  rw [hspan] at hv
  nlinarith

/-- Support closeness puts the competitor cap in Gerver's square parallel set. -/
theorem cap_layer_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2)) {δ : ℝ} (hδ : 0≤δ)
    (hclose : UpperSupportClose δ K P.cap) :
    area (K\P.cap)≤2*(horizontalWidth P.cap+1)*δ+4*δ^2 := by
  have hdist:=upperSupportClose_euclidean hδ hK (gm_isCap hP hbox) hclose
  have hsub:=euclidean_parallel_subset_square hδ (gm_isConvexBody_cap hP hbox).2.1 hdist.1
  have harea:=area_mono_of_finite
    (show K\P.cap⊆squareThickening P.cap δ\P.cap by
      intro p hp; exact ⟨hsub hp.1,hp.2⟩)
    (volume_ne_top_of_subset sdiff_subset
      (isCompact_squareThickening (gm_isConvexBody_cap hP hbox).2.1 hδ).measure_lt_top.ne)
  have hsquare:=area_squareThickening_cap (gm_isCap hP hbox) hδ
  have hsplit:=area_sdiff_of_subset
    (subset_squareThickening hδ (gm_isConvexBody_cap hP hbox).1)
    (gm_isConvexBody_cap hP hbox).2.1.measurableSet
  linarith

/-- Support error changes either inner slack by at most delta. -/
theorem slack_support_error {K₀ K : Set Point} {δ : ℝ}
    (hclose : UpperSupportClose δ K K₀) {t : ℝ}
    (ht : t∈Icc (0:ℝ) (π/2)) (p : Point) :
    |innerSlackU K t p-innerSlackU K₀ t p|≤δ ∧
    |innerSlackV K t p-innerSlackV K₀ t p|≤δ := by
  constructor
  · unfold innerSlackU
    simpa only [sub_sub_sub_cancel_right,abs_neg] using hclose t ⟨ht.1,by linarith [ht.2,pi_pos]⟩
  · unfold innerSlackV
    simpa only [sub_sub_sub_cancel_right,abs_neg] using
      hclose (t+π/2) ⟨by linarith [ht.1,pi_pos],by linarith [ht.2]⟩

/-- Reference roof depth of an envelope point is at most delta/c. -/
theorem envelope_roof_depth_le {K₀ K : Set Point} {γ : ℝ→ℝ}
    {c τ δ : ℝ} (hK : IsCap K (π/2)) (hc : 0<c)
    (hclose : UpperSupportClose δ K K₀) (hsmall : δ<τ)
    (hmargin : RoofSlackMargin K₀ γ c τ)
    {p : Point} (hp : p∈capShape K) (hpN : p∈niche K₀ (π/2)) :
    γ p.1-p.2≤δ/c := by
  obtain ⟨t,ht,hU,hV⟩:=hmargin p hpN
  obtain ⟨heU,heV⟩:=slack_support_error hclose ht.le p
  have hhall : 0≤max (innerSlackU K t p) (innerSlackV K t p) := by
    by_contra hn
    have hboth:=max_lt_iff.mp (not_le.mp hn)
    exact hp.2 ((mem_niche_iff_slacks K p).2
      ⟨hK.snd_nonneg hp.1,t,ht,hboth.1,hboth.2⟩)
  have hdepth : c*(γ p.1-p.2)≤δ := by
    by_contra hn
    have hm : δ<min (c*(γ p.1-p.2)) τ :=
      lt_min (not_le.mp hn) hsmall
    have hu : innerSlackU K t p<0 := by linarith
    have hv : innerSlackV K t p<0 := by linarith
    exact (not_lt_of_ge hhall) (max_lt hu hv)
  exact (le_div_iff₀ hc).2 hdepth

/-- Area of the vertical roof band of depth d. -/
theorem roof_band_area {a b d : ℝ} {γ : ℝ→ℝ}
    (hab : a≤b) (hd : 0≤d) (hγ : Continuous γ) :
    area {p : Point | p.1∈Icc a b ∧ γ p.1-d≤p.2 ∧ p.2≤γ p.1}
      =d*(b-a) := by
  rw [area,Measure.volume_eq_prod]
  rw [volume_regionBetween_eq_lintegral'
    (hγ.sub continuous_const).measurable hγ.measurable measurableSet_Icc]
  simp [Real.volume_Icc,hab,hd]
  rw [ENNReal.toReal_ofReal (mul_nonneg hd (sub_nonneg.mpr hab))]
  ring

/-- Excess of the full-angle envelope over Gerver. -/
theorem quantitative_envelope_excess {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsCap K (π/2)) {δ : ℝ}
    (hδ : 0≤δ) (hclose : UpperSupportClose δ K P.cap) :
    ∃ τ : ℝ,0<τ ∧ δ<τ →
      area (capShape K\gerverSofa P)≤
        (62307/2500)*δ+4*δ^2 := by
  obtain ⟨H,L,γ,hroof⟩:=gerver_roof_data hP hbox
  obtain ⟨τ,hτ,hmargin⟩:=gerver_explicit_roof_slack hP hbox hroof
  refine ⟨τ,hτ,?_⟩
  intro hδτ
  have hwidth:=gerver_quantitative_widths hP hbox
  have hcap:=cap_layer_area hP hbox hK hδ hclose
  have hbandSub :
      (capShape K\gerverSofa P)∩P.cap ⊆
        {p : Point | p.1∈Icc (gerverRoofLeft P) (gerverRoofRight P) ∧
          γ p.1-(51/5)*δ≤p.2 ∧ p.2≤γ p.1} := by
    intro p hp
    have hpN : p∈niche P.cap (π/2) := by
      rw [←gerver_shape_eq hP hbox] at hp
      by_contra hn
      exact hp.1.2 ⟨hp.2,hn⟩
    have hd:=envelope_roof_depth_le hK (by norm_num : (0:ℝ)<5/51)
      hclose hδτ hmargin hp.1.1 hpN
    rw [hroof.niche_eq] at hpN
    refine ⟨hpN.1,?_,hpN.2.2.le⟩
    nlinarith
  have hbandArea :
      area ((capShape K\gerverSofa P)∩P.cap)≤
        (51/5)*δ*(gerverRoofRight P-gerverRoofLeft P) := by
    have hmono:=area_mono_of_finite hbandSub
      (volume_ne_top_of_subset (s:=_)
        (t:= {p : Point | p.1∈Icc (gerverRoofLeft P) (gerverRoofRight P) ∧
          γ p.1-(51/5)*δ≤p.2 ∧ p.2≤γ p.1}) subset_rfl
        (by rw [roof_band_area hroof.order.le (by positivity)
          (continuous_clamped_roof hroof.order.le hroof.slope_nonneg hroof.roof_lipschitz)];
            exact ENNReal.ofReal_ne_top))
    exact hmono
  have hsplit :
      area (capShape K\gerverSofa P)≤area (K\P.cap)+
        area ((capShape K\gerverSofa P)∩P.cap) := by
    apply area_mono_union_bound
    intro p hp
    by_cases hpK : p∈P.cap
    · exact Or.inr ⟨hp,hpK⟩
    · exact Or.inl ⟨hp.1.1,hpK⟩
  have hw : 2*(horizontalWidth P.cap+1)+(51/5)*
      (gerverRoofRight P-gerverRoofLeft P)<62307/2500 := by
    unfold horizontalWidth at *
    have hW : horizontalWidth P.cap<323/100 := hwidth.1
    have hR : gerverRoofRight P-gerverRoofLeft P<807/500 := hwidth.2
    nlinarith
  nlinarith


/-- Same excess estimate with the reference roof and clipping scale exposed, so
a global theorem can choose its deficit threshold before seeing the competitor. -/
theorem quantitative_envelope_excess_with_margin {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ→ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ)
    {τ : ℝ} (hτ : 0<τ) (hmargin : RoofSlackMargin P.cap γ (5/51) τ)
    {K : Set Point} (hK : IsCap K (π/2)) {δ : ℝ}
    (hδ : 0≤δ) (hδτ : δ<τ) (hclose : UpperSupportClose δ K P.cap) :
    area (capShape K\gerverSofa P)≤(62307/2500)*δ+4*δ^2 := by
  have hwidth:=gerver_quantitative_widths hP hbox
  have hcap:=cap_layer_area hP hbox hK hδ hclose
  have hbandSub :
      (capShape K\gerverSofa P)∩P.cap ⊆
        {p : Point | p.1∈Icc (gerverRoofLeft P) (gerverRoofRight P) ∧
          γ p.1-(51/5)*δ≤p.2 ∧ p.2≤γ p.1} := by
    intro p hp
    have hpN : p∈niche P.cap (π/2) := by
      rw [←gerver_shape_eq hP hbox] at hp
      by_contra hn
      exact hp.1.2 ⟨hp.2,hn⟩
    have hd:=envelope_roof_depth_le hK (by norm_num : (0:ℝ)<5/51)
      hclose hδτ hmargin hp.1.1 hpN
    rw [hroof.niche_eq] at hpN
    exact ⟨hpN.1,by nlinarith,hpN.2.2.le⟩
  have hbandArea :
      area ((capShape K\gerverSofa P)∩P.cap)≤
        (51/5)*δ*(gerverRoofRight P-gerverRoofLeft P) := by
    have hm:=area_mono_of_finite hbandSub
      (by
        rw [roof_band_area hroof.order.le (by positivity)
          (continuous_clamped_roof hroof.order.le hroof.slope_nonneg hroof.roof_lipschitz)]
        exact ENNReal.ofReal_ne_top)
    exact hm
  have hsplit :
      area (capShape K\gerverSofa P)≤area (K\P.cap)+
        area ((capShape K\gerverSofa P)∩P.cap) := by
    exact area_split_by_measurable P.cap (capShape K\gerverSofa P)
      (gm_isConvexBody_cap hP hbox).2.1.measurableSet
  have hw : 2*(horizontalWidth P.cap+1)+(51/5)*
      (gerverRoofRight P-gerverRoofLeft P)<62307/2500 := by
    nlinarith [hwidth.1,hwidth.2]
  nlinarith

/-- The final 50 coefficient from the complementary area budget. -/
theorem symmetric_difference_50 {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox)
    {S U : Set Point} {ε e δ : ℝ}
    (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSf : volume S≠⊤) (hUf : volume U≠⊤)
    (hε : 0≤ε) (he : 0≤e) (heε : e≤ε)
    (hεeq : area (gerverSofa P)-area S=ε)
    (hgain : area (S\U)≤(31/10000)*(ε-e))
    (hδ : 0≤δ) (hδbound : δ≤(1001/1000)*sqrt e)
    (hexcess : area (U\gerverSofa P)≤(62307/2500)*δ+4*δ^2)
    (hsmall : sqrt ε≤1/200) :
    symmetricDifferenceArea S (gerverSofa P)≤50*sqrt ε := by
  have hG:=ms_isCompact_of_isMovingSofaWithAngle (gm_movingSofa_std hP hbox).1
  have hsub : S\gerverSofa P⊆(S\U)∪(U\gerverSofa P) := by
    intro p hp
    by_cases hu:p∈U
    · exact Or.inr ⟨hu,hp.2⟩
    · exact Or.inl ⟨hp.1,hu⟩
  have harea : symmetricDifferenceArea S (gerverSofa P)≤
      ε+2*area(S\U)+2*area(U\gerverSofa P) := by
    rw [symmetricDifferenceArea_eq hS hG.measurableSet hSf hG.measure_lt_top.ne,hεeq]
    have hm:=area_mono_of_finite hsub
      (volume_ne_top_of_subset (union_subset
        (sdiff_subset.trans (subset_union_left))
        (sdiff_subset.trans (subset_union_right)))
        (ENNReal.add_ne_top.mpr
          ⟨volume_ne_top_of_subset sdiff_subset hSf,
           volume_ne_top_of_subset sdiff_subset hUf⟩))
    have hu:=measure_union_le (S\U) (U\gerverSofa P)
    nlinarith [hm,ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr
       ⟨volume_ne_top_of_subset sdiff_subset hSf,
        volume_ne_top_of_subset sdiff_subset hUf⟩) hu]
  have hb:=midpoint_area_budget he heε
  have hc:=midpoint_area_coefficient hε hsmall
  nlinarith [harea,hgain,hexcess,hδbound,hδ,sqrt_nonneg e]

end MovingSofaQuantitative
