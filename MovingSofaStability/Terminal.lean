module

public import MovingSofaStability.LocalBound

/-!
# The cost of a missing final angle

If the sofa turns only through `ω < π/2`, the tilted final strip removes a floor region of area at least
`c (π/2 - ω)`, while the omitted hallway positions add less (`nearby_terminal_comparison`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## The interior niche floor is already removed before the terminal angle

A directed compact-cover argument supplies a uniform strict slack and an angle
bounded away from pi/2. The fixed floor interval is chosen first; no unsupported
rate of compactness is used.
-/

section FloorCoverage

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Gerver's roof has positive height at every abscissa strictly between its endpoints. -/
theorem gerver_floor_mem_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : ℝ} (hx : x ∈ Ioo (gerverRoofLeft P) (gerverRoofRight P)) :
    (x, 0) ∈ niche P.cap (π / 2) := by
  have h := gn_envHyp hP (romik_bounds hP hbox)
  obtain ⟨h1, h12, h23, h34, h4⟩ := h.ht
  have hBcont : ContinuousOn (envB P.path P.gs_α) (Icc 0 (π / 2)) :=
    h.x_cont.add (h.α_cont.smul continuous_vvec.continuousOn)
  have hDcont : ContinuousOn (envD P.path P.gs_β) (Icc 0 (π / 2)) :=
    h.x_cont.sub (h.β_cont.smul continuous_uvec.continuousOn)
  have hBanti : StrictAntiOn (fun t => (envB P.path P.gs_α t).2)
      (Icc (π / 2 - P.θ) (π / 2)) := by
    apply env_strictAntiOn (env_bp_finite P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ))
      (hBcont.snd.mono (Icc_subset_Icc (by linarith) le_rfl))
      (f' := fun t => (gb_rhoA P t - 1) * cos t)
    · intro t ht hne
      simpa only [Prod.smul_snd, smul_eq_mul, vvec_snd] using
        hasDerivAt_snd (h.B_deriv t ⟨by linarith [ht.1], ht.2⟩ hne)
    · intro t ht hne
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (h.ρA_lt t ⟨ht.1.le, ht.2.le⟩))
        (cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩)
  have hDmono : StrictMonoOn (fun t => (envD P.path P.gs_β t).2) (Icc 0 P.θ) := by
    apply env_strictMonoOn (env_bp_finite P.φ P.θ (π / 2 - P.θ) (π / 2 - P.φ))
      (hDcont.snd.mono (Icc_subset_Icc le_rfl (by linarith)))
      (f' := fun t => (1 - gb_rhoC P t) * sin t)
    · intro t ht hne
      simpa only [Prod.smul_snd, smul_eq_mul, uvec_snd] using
        hasDerivAt_snd (h.D_deriv t ⟨ht.1, by linarith [ht.2]⟩ hne)
    · intro t ht hne
      exact mul_pos (sub_pos.mpr (h.ρC_lt t ⟨ht.1.le, ht.2.le⟩))
        (sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos]))
  obtain ⟨q, hq, hqx⟩ := env_exists_curve_fst h ⟨hx.1.le, hx.2.le⟩
  have hqy : 0 < q.2 := by
    rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · have htv : t < π / 2 := lt_of_le_of_ne ht.2 (by
        intro he
        subst t
        change gerverRoofRight P = x at hqx
        exact (ne_of_lt hx.2) hqx.symm)
      have he : (envB P.path P.gs_α (π / 2)).2 < (envB P.path P.gs_α t).2 :=
        hBanti ht ⟨by linarith, le_rfl⟩ htv
      rwa [h.B_end] at he
    · exact h.x_pos t ht
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
        intro he
        subst t
        change gerverRoofLeft P = x at hqx
        exact (ne_of_lt hx.1) hqx)
      have he : (envD P.path P.gs_β 0).2 < (envD P.path P.gs_β t).2 :=
        hDmono ⟨le_rfl, by linarith⟩ ht ht0
      rwa [h.D_end] at he
  rw [gerver_niche_envelope hP hbox]
  exact ⟨le_rfl, q, hq, hqx, hqy⟩

/-- Compact sets of floor points in the reference niche have uniform strict
witnesses whose angles stay away from both endpoints. -/
theorem compact_floor_witnesses {K₀ : Set Point} {I : Set ℝ} (hI : IsCompact I)
    (hfloor : ∀ x ∈ I, (x, 0) ∈ niche K₀ (π / 2)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ I, ∃ t ∈ Ioo e (π / 2 - e),
      innerSlackU K₀ t (x, 0) < -e ∧ innerSlackV K₀ t (x, 0) < -e := by
  classical
  let J := {e : ℝ // 0 < e}
  let U : J → Set ℝ := fun e => ⋃ t ∈ Ioo e.1 (π / 2 - e.1),
    {x | innerSlackU K₀ t (x, 0) < -e.1 ∧ innerSlackV K₀ t (x, 0) < -e.1}
  have : Nonempty J := ⟨⟨1, by norm_num⟩⟩
  have ho : ∀ e, IsOpen (U e) := by
    intro e
    apply isOpen_iUnion
    intro t
    apply isOpen_iUnion
    intro ht
    exact (isOpen_lt (f := fun x : ℝ => innerSlackU K₀ t (x, 0))
      (by unfold innerSlackU dot; fun_prop) continuous_const).inter
      (isOpen_lt (f := fun x : ℝ => innerSlackV K₀ t (x, 0))
        (by unfold innerSlackV dot; fun_prop) continuous_const)
  have hcover : I ⊆ ⋃ e, U e := by
    intro x hx
    obtain ⟨-, t, ht, hU, hV⟩ := (mem_niche_iff_slacks K₀ (x, 0)).1 (hfloor x hx)
    let e := min t (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0)))) / 2
    have he : 0 < e := half_pos (lt_min ht.1
      (lt_min (sub_pos.mpr ht.2) (lt_min (neg_pos.mpr hU) (neg_pos.mpr hV))))
    have hr := min_le_right t
      (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0))))
    have e1 : e < t := by
      have hm := min_le_left t
        (min (π / 2 - t) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0))))
      dsimp [e] at *
      linarith
    have e2 : e < π / 2 - t := by
      have hm := hr.trans (min_le_left _ _)
      dsimp [e] at *
      linarith
    have e3 : e < -innerSlackU K₀ t (x, 0) := by
      have hm := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
      dsimp [e] at *
      linarith
    have e4 : e < -innerSlackV K₀ t (x, 0) := by
      have hm := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
      dsimp [e] at *
      linarith
    exact mem_iUnion.mpr ⟨⟨e, he⟩, mem_iUnion₂.mpr ⟨t, ⟨e1, by linarith⟩, by linarith, by linarith⟩⟩
  have hd : Directed (· ⊆ ·) U := by
    intro e f
    let g : J := ⟨min e.1 f.1, lt_min e.2 f.2⟩
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      obtain ⟨t, ht, hU, hV⟩ := mem_iUnion₂.mp hx
      have hge : g.1 ≤ e.1 := min_le_left _ _
      exact mem_iUnion₂.mpr ⟨t, ⟨hge.trans_lt ht.1, by linarith [ht.2]⟩, by linarith, by linarith⟩
    · intro x hx
      obtain ⟨t, ht, hU, hV⟩ := mem_iUnion₂.mp hx
      have hgf : g.1 ≤ f.1 := min_le_right _ _
      exact mem_iUnion₂.mpr ⟨t, ⟨hgf.trans_lt ht.1, by linarith [ht.2]⟩, by linarith, by linarith⟩
  obtain ⟨e, he⟩ := hI.elim_directed_cover U ho hcover hd
  refine ⟨e.1, e.2, fun x hx => ?_⟩
  obtain ⟨t, ht, hx'⟩ := mem_iUnion₂.mp (he hx)
  exact ⟨t, ht, hx'⟩

/-- A fixed interior floor slab is removed by angles uniformly below pi/2,
even after a sufficiently small perturbation of the cap support. -/
theorem gerver_floor_slab_covered {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {l r : ℝ} (hl : gerverRoofLeft P < l) (hr : r < gerverRoofRight P) :
    ∃ e δ : ℝ, 0 < e ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ K : Set Point, UpperSupportClose δ K P.cap →
      ∀ p ∈ Icc l r ×ˢ Icc (0 : ℝ) δ,
        ∃ t ∈ Ioo (0 : ℝ) (π / 2 - e),
          innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  obtain ⟨e, he, hw⟩ := compact_floor_witnesses isCompact_Icc
    (fun x hx => gerver_floor_mem_niche hP hbox ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩)
  let δ := min 1 (e / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδe : δ ≤ e / 4 := min_le_right _ _
  refine ⟨e, δ, he, hδ, min_le_left _ _, ?_⟩
  intro K hclose p hp
  obtain ⟨t, ht, hU, hV⟩ := hw p.1 hp.1
  have htv : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨he.trans ht.1, by linarith [ht.2]⟩
  have hs1 := (abs_le.mp (hclose t ⟨htv.1.le, by linarith [htv.2, pi_pos]⟩)).1
  have hs2 := (abs_le.mp (hclose (t + π / 2) ⟨by linarith [htv.1, pi_pos], by linarith [htv.2]⟩)).1
  have hu : p.2 * sin t ≤ δ := (mul_le_mul_of_nonneg_left (sin_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  have hv : p.2 * cos t ≤ δ := (mul_le_mul_of_nonneg_left (cos_le_one t) hp.2.1).trans
    (by simpa only [mul_one] using hp.2.2)
  refine ⟨t, ⟨htv.1, ht.2⟩, ?_, ?_⟩
  · simp only [innerSlackU, dot, uvec] at hU ⊢
    nlinarith
  · simp only [innerSlackV, dot, vvec] at hV ⊢
    nlinarith

end MovingSofaStability

end FloorCoverage

/-!
## Partial-angle shapes and the omitted wedges

The partial shape is an over-envelope of a sofa whose rotation stops at omega.
It need not be a full-angle moving sofa. The difference from the full-angle
shape is retained explicitly.
-/

section PartialHallways

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def partialNiche (K : Set Point) (ω : ℝ) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) ω, innerSlackU K t p < 0 ∧ innerSlackV K t p < 0}

def partialShape (K : Set Point) (ω : ℝ) : Set Point := K \ partialNiche K ω

def omittedWedges (K : Set Point) (ω : ℝ) : Set Point := partialShape K ω \ capShape K

@[simp] theorem partialNiche_rightAngle (K : Set Point) : partialNiche K (π / 2) = niche K (π / 2) := by
  ext p
  exact (mem_niche_iff_slacks K p).symm

@[simp] theorem partialShape_rightAngle (K : Set Point) : partialShape K (π / 2) = capShape K := by
  simp only [partialShape, partialNiche_rightAngle, capShape]

theorem partialNiche_measurable (K : Set Point) (ω : ℝ) : MeasurableSet (partialNiche K ω) := by
  have he : partialNiche K ω = {p : Point | 0 ≤ p.2} ∩
      ⋃ t ∈ Ioo (0 : ℝ) ω, {p : Point | innerSlackU K t p < 0 ∧ innerSlackV K t p < 0} := by
    ext p
    simp only [partialNiche, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [he]
  apply MeasurableSet.inter (isClosed_le continuous_const continuous_snd).measurableSet
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro ht
  exact (isOpen_lt (f := fun p : Point => innerSlackU K t p)
    (by unfold innerSlackU dot; fun_prop) continuous_const).inter
    (isOpen_lt (f := fun p : Point => innerSlackV K t p)
      (by unfold innerSlackV dot; fun_prop) continuous_const)

theorem partialShape_measurable {K : Set Point} (hK : IsConvexBody K) (ω : ℝ) :
    MeasurableSet (partialShape K ω) :=
  hK.2.1.measurableSet.diff (partialNiche_measurable K ω)

theorem partialNiche_subset_niche (K : Set Point) {ω : ℝ} (hω : ω ≤ π / 2) :
    partialNiche K ω ⊆ niche K (π / 2) := by
  rintro p ⟨hy, t, ht, hu, hv⟩
  exact (mem_niche_iff_slacks K p).2 ⟨hy, t, ⟨ht.1, ht.2.trans_le hω⟩, hu, hv⟩

theorem capShape_subset_partialShape (K : Set Point) {ω : ℝ} (hω : ω ≤ π / 2) :
    capShape K ⊆ partialShape K ω := by
  rintro p ⟨hp, hn⟩
  exact ⟨hp, fun h => hn (partialNiche_subset_niche K hω h)⟩

theorem sofa_subset_partialShape {K S : Set Point} {ω : ℝ}
    (hSK : S ⊆ K)
    (hpartial : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) :
    S ⊆ partialShape K ω := by
  intro p hp
  refine ⟨hSK hp, ?_⟩
  rintro ⟨-, t, ht, hu, hv⟩
  have he := hpartial p hp t ⟨ht.1.le, ht.2.le⟩
  exact (not_lt_of_ge he) (max_lt hu hv)

/-- An omitted point has a forbidden-wedge witness at or after the terminal angle. -/
theorem omittedWedges_witness {K : Set Point} {ω : ℝ} {p : Point}
    (hp : p ∈ omittedWedges K ω) :
    p ∈ K ∧ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2), ω ≤ t ∧
      innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  have hn : p ∈ niche K (π / 2) := by
    by_contra h
    exact hp.2 ⟨hp.1.1, h⟩
  obtain ⟨hy, t, ht, hu, hv⟩ := (mem_niche_iff_slacks K p).1 hn
  have hωt : ω ≤ t := by
    by_contra h
    exact hp.1.2 ⟨hy, t, ⟨ht.1, not_le.mp h⟩, hu, hv⟩
  exact ⟨hp.1.1, hy, t, ht, hωt, hu, hv⟩

/-- The height of a late inner corner is linear in its distance from pi/2. -/
theorem late_corner_height {K : Set Point} (hK : IsCap K (π / 2)) {R : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    (innerCorner K t).2 ≤ (3 * R + 1) * (π / 2 - t) := by
  have hR0 : 0 ≤ R := by linarith
  have hs := support_angle_bound hK.2.1 hR0 hradius t (π / 2)
  rw [hK.2.2.2.1, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hs
  have hfirst : supp K t - 1 ≤ 2 * R * (π / 2 - t) := by
    have he := (abs_le.mp hs).2
    linarith
  have hsecond := (abs_le.mp (support_abs_le_radius hK.2.1 hradius (t + π / 2))).2
  have hsin0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, pi_pos])
  have hcos0 : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hcos : cos t ≤ π / 2 - t := by
    rw [← sin_pi_div_two_sub]
    exact sin_le (by linarith [ht.2])
  have h1 := mul_le_mul_of_nonneg_right hfirst hsin0
  have h2 := mul_le_mul_of_nonneg_left (sin_le_one t)
    (show 0 ≤ 2 * R * (π / 2 - t) from mul_nonneg (by linarith) (sub_nonneg.mpr ht.2))
  have h3 := mul_le_mul_of_nonneg_right (show supp K (t + π / 2) - 1 ≤ R + 1 by linarith) hcos0
  have h4 := mul_le_mul_of_nonneg_left hcos (show 0 ≤ R + 1 by linarith)
  rw [proposition2_2_2_innerCorner]
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, uvec_snd, vvec_snd]
  nlinarith

/-- All omitted wedges lie in a thin horizontal slab. -/
theorem omittedWedges_height {K : Set Point} (hK : IsCap K (π / 2)) {R ω : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) :
    ∀ p ∈ omittedWedges K ω, p.2 ∈ Icc (0 : ℝ) ((3 * R + 1) * (π / 2 - ω)) := by
  intro p hp
  obtain ⟨-, hy, t, ht, hωt, hu, hv⟩ := omittedWedges_witness hp
  have hbelow := point_below_corner_of_negative_slacks ht hu hv
  have hc := late_corner_height hK hR hradius ⟨ht.1.le, ht.2.le⟩
  refine ⟨hy, ?_⟩
  have hm := mul_le_mul_of_nonneg_left (show π / 2 - t ≤ π / 2 - ω by linarith)
    (show 0 ≤ 3 * R + 1 by linarith)
  linarith

/-- Area of a nondegenerate closed rectangle, with all finiteness visible. -/
theorem area_closed_rectangle {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    area (Icc a b ×ˢ Icc c d) = (b - a) * (d - c) := by
  unfold area
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]

/-- Two endpoint windows of width 2 eta have total area at most 4 eta H. -/
theorem area_two_windows_le {E : Set Point} {a b η H : ℝ}
    (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hsub : E ⊆ (Icc (a - η) (a + η) ×ˢ Icc (0 : ℝ) H) ∪
      (Icc (b - η) (b + η) ×ˢ Icc (0 : ℝ) H)) :
    area E ≤ 4 * η * H := by
  let A := Icc (a - η) (a + η) ×ˢ Icc (0 : ℝ) H
  let B := Icc (b - η) (b + η) ×ˢ Icc (0 : ℝ) H
  have hAf : volume A ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hBf : volume B ≠ ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAf, hBf⟩)
    ((measure_mono hsub).trans (measure_union_le A B))
  rw [ENNReal.toReal_add hAf hBf] at he
  change area E ≤ area A + area B at he
  rw [area_closed_rectangle (by linarith) hH, area_closed_rectangle (by linarith) hH] at he
  nlinarith

end MovingSofaStability

end PartialHallways

/-!
## A small linear cost for omitted terminal wedges

The radius is fixed before the endpoint-window width. Only afterwards are the
support neighborhood and angle threshold chosen. Thus the gain coefficient can
be made smaller than a fixed terminal floor loss, without any quantitative
compactness assumption.
-/

section OmittedWedgeArea

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Late wedges add area only in two arbitrarily short endpoint windows. -/
theorem nearby_omittedWedges_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η R : ℝ} (hη : 0 < η) (hR : 1 ≤ R) :
    ∃ δ α₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      (∀ p ∈ K, norm2 p ≤ R) → ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ →
        area (omittedWedges K ω) ≤ 4 * η * (3 * R + 1) * (π / 2 - ω) := by
  obtain ⟨δN, hδN, hδN1, hlocal⟩ := nearby_niche_horizontal_localization hP hbox hη
  obtain ⟨e, δF, he, hδF, hδF1, hcover⟩ := gerver_floor_slab_covered hP hbox
    (l := gerverRoofLeft P + η) (r := gerverRoofRight P - η) (by linarith) (by linarith)
  let Cw := 3 * R + 1
  have hCw : 0 < Cw := by dsimp [Cw]; linarith
  let δ := min δN δF
  let α₀ := min (e / 2) (δF / Cw)
  have hδ : 0 < δ := lt_min hδN hδF
  have hα₀ : 0 < α₀ := lt_min (by linarith) (div_pos hδF hCw)
  have hδN' : δ ≤ δN := min_le_left _ _
  have hδF' : δ ≤ δF := min_le_right _ _
  have hαe : α₀ ≤ e / 2 := min_le_left _ _
  have hαh : α₀ ≤ δF / Cw := min_le_right _ _
  refine ⟨δ, α₀, hδ, hδN'.trans hδN1, hα₀, ?_⟩
  intro K hK hclose hradius ω hω hα
  have hα0 : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  have hheight : Cw * (π / 2 - ω) ≤ δF := by
    have hh := (le_div_iff₀ hCw).1 (hα.trans hαh)
    nlinarith
  have homega : π / 2 - e < ω := by linarith
  have hsub : omittedWedges K ω ⊆
      (Icc (gerverRoofLeft P - η) (gerverRoofLeft P + η) ×ˢ Icc (0 : ℝ) (Cw * (π / 2 - ω))) ∪
      (Icc (gerverRoofRight P - η) (gerverRoofRight P + η) ×ˢ Icc (0 : ℝ) (Cw * (π / 2 - ω))) := by
    intro p hp
    obtain ⟨hpK, hy0, t, ht, -, hu, hv⟩ := omittedWedges_witness hp
    have hpN := (mem_niche_iff_slacks K p).2 ⟨hy0, t, ht, hu, hv⟩
    have hx := hlocal K hK (hclose.mono hδN') p hpN
    have hy := omittedWedges_height hK hR hradius p hp
    by_cases hleft : p.1 ≤ gerverRoofLeft P + η
    · exact Or.inl ⟨⟨hx.1, hleft⟩, hy⟩
    by_cases hright : gerverRoofRight P - η ≤ p.1
    · exact Or.inr ⟨⟨hright, hx.2⟩, hy⟩
    have hpbox : p ∈ Icc (gerverRoofLeft P + η) (gerverRoofRight P - η) ×ˢ Icc (0 : ℝ) δF :=
      ⟨⟨(not_le.mp hleft).le, (not_le.mp hright).le⟩, hy0, hy.2.trans hheight⟩
    obtain ⟨s, hs, hsU, hsV⟩ := hcover K (hclose.mono hδF') p hpbox
    exact (hp.1.2 ⟨hy0, s, ⟨hs.1, hs.2.trans homega⟩, hsU, hsV⟩).elim
  have ha := area_two_windows_le hη.le (mul_nonneg hCw.le hα0) hsub
  dsimp [Cw] at ha
  nlinarith

end MovingSofaStability

end OmittedWedgeArea

/-!
## The terminal strip removes a fixed linear amount of floor area

A fixed rectangle in Gerver's left wing persists in nearby full-angle shapes. A
tilted terminal strip excludes its bottom slice, whose area is c0 times the
missing angle. The slice is constructed explicitly.
-/

section TerminalFloor

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A convenient elementary lower bound, enough for small terminal angles. -/
theorem sin_ge_half_on_unit {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : α / 2 ≤ sin α := by
  have hcos : ∀ t ∈ Ioo (0 : ℝ) α, (1 / 2 : ℝ) ≤ cos t := by
    intro t ht
    have he := one_sub_sq_div_two_le_cos (x := t)
    nlinarith [ht.1, ht.2, hα.2]
  have he := right_derivative_increment_ge hα.1 continuous_sin.continuousOn
    (fun t ht => (hasDerivAt_sin t).hasDerivWithinAt) hcos
  rw [sin_zero] at he
  linarith

/-- The terminal lower wall excludes low points to the left of a top contact. -/
theorem terminal_excludes_low_left {K : Set Point} (hK : IsCap K (π / 2))
    {a d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hαd : α ≤ d / 4)
    {q p : Point} (hq : q ∈ K) (hqy : q.2 = 1)
    (hqx : a - d / 4 ≤ q.1) (hpx : p.1 ≤ a - d)
    (hpy0 : 0 ≤ p.2) (hpy : p.2 ≤ α * d / 8) :
    dot p (uvec (π / 2 - α)) < supp K (π / 2 - α) - 1 := by
  have hs := sin_ge_half_on_unit ⟨hα.le, hα1⟩
  have hs0 : 0 ≤ sin α := by linarith
  have hc := one_sub_sq_div_two_le_cos (x := α)
  have hup := dot_le_supp hK.2.1.2.1 hq (π / 2 - α)
  simp only [dot, uvec, cos_pi_div_two_sub, sin_pi_div_two_sub, hqy, one_mul] at hup ⊢
  have hx : 3 * d / 4 ≤ q.1 - p.1 := by linarith
  have hm1 := mul_le_mul_of_nonneg_right hx hs0
  have hm2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * d / 4 by positivity)
  have hm3 := mul_le_mul_of_nonneg_left (cos_le_one α) hpy0
  have hm4 : α ^ 2 / 2 ≤ α * d / 8 := by nlinarith
  have hpos : 0 < α * d := mul_pos hα hd
  nlinarith

/-- A fixed left-wing rectangle persists as a subset of the full-angle shape. -/
theorem nearby_left_floor_rectangle {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ l r d δ : ℝ, l < r ∧ 0 < d ∧ 0 < δ ∧ δ ≤ 1 ∧
      r = gerverRoofLeft P - d ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        Icc l r ×ˢ Icc (0 : ℝ) (1 / 8) ⊆ capShape K ∧
        ∃ q ∈ K, q.2 = 1 ∧ gerverRoofLeft P - d / 4 ≤ q.1 := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  let x₀ := -supp P.cap π
  let a := gerverRoofLeft P
  let D := a - x₀
  have hD : 0 < D := sub_pos.mpr hroof.left_wing
  let l := x₀ + D / 4
  let r := x₀ + D / 2
  let d := D / 2
  have hlr : l < r := by dsimp [l, r]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hra : r = a - d := by dsimp [r, d, D]; ring
  have hla : x₀ < l := by dsimp [l]; linarith
  have hr0 : r < supp P.cap 0 := by
    have ha0 : a < supp P.cap 0 := hroof.order.trans hroof.right_wing
    rw [hra]
    linarith
  have ha : (a, 1) ∈ P.cap := hroof.rectangle ⟨⟨le_rfl, hroof.order.le⟩, by norm_num, le_rfl⟩
  have hxl : (l, (1 / 4 : ℝ)) ∈ P.cap := by
    have he := hroof.cap.2.1.2.2.add_smul_sub_mem (opt_cap_C_mem hroof.cap) ha
      (show (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    convert he using 1
    ext <;> dsimp [l, D, x₀, a] <;> ring
  have hxr : (r, (1 / 4 : ℝ)) ∈ P.cap := by
    have he := hroof.cap.2.1.2.2.add_smul_sub_mem (opt_cap_C_mem hroof.cap) ha
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    have hrhalf : (r, (1 / 2 : ℝ)) ∈ P.cap := by
      convert he using 1
      ext <;> dsimp [r, D, x₀, a] <;> ring
    exact opt_cap_down hroof.cap hrhalf (by norm_num) (by norm_num)
  obtain ⟨m, hm, hmargin⟩ := cap_rectangle_upper_margin hroof.cap hlr hla hr0
    (show (1 / 8 : ℝ) < 1 / 4 by norm_num) hxl hxr
  obtain ⟨δN, hδN, hδN1, hN⟩ := nearby_niche_horizontal_localization hP hbox
    (η := d / 4) (by positivity)
  obtain ⟨δT, ρ, hδT, hρ, hδT1, htop⟩ := gerver_near_top_contacts hP hbox
    (η := d / 4) (by positivity)
  let δ := min δN (min δT (m / 2))
  have hδ : 0 < δ := lt_min hδN (lt_min hδT (by positivity))
  have dN : δ ≤ δN := min_le_left _ _
  have dT : δ ≤ δT := (min_le_right _ _).trans (min_le_left _ _)
  have dm : δ ≤ m / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l, r, d, δ, hlr, hd, hδ, dN.trans hδN1, hra, ?_⟩
  intro K hK hclose
  constructor
  · intro p hp
    have hpK : p ∈ K := by
      apply (cap_mem_iff_upper hK p).2
      refine ⟨hp.2.1, ?_⟩
      intro t ht
      have he := hmargin p hp t ht
      have hs := (abs_le.mp (hclose t ht)).1
      linarith
    refine ⟨hpK, ?_⟩
    intro hpN
    have hx := (hN K hK (hclose.mono dN) p hpN).1
    have hpr := hp.1.2
    rw [hra] at hpr
    change a - d / 4 ≤ p.1 at hx
    linarith
  · let q := vplus K (π / 2)
    have hq := vplus_mem_edge hK.2.1 (π / 2)
    have hqy : q.2 = 1 := by
      have he := hq.2
      change dot q (uvec (π / 2)) = supp K (π / 2) at he
      rwa [dot_uvec_pi_div_two, hK.2.2.2.1] at he
    have hqx := (htop K hK (hclose.mono dT) (π / 2)
      ⟨by positivity, by linarith [pi_pos]⟩ (by simpa only [sub_self, abs_zero] using hρ.le) q hq).1
    exact ⟨q, hq.1, hqy, hqx.le⟩

/-- There is a uniform positive floor-loss coefficient. For alpha>0 the
constructed slice is disjoint from every set in the terminal unit strip. -/
theorem terminal_floor_loss {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ c₀ δ α₀ : ℝ, 0 < c₀ ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ S : Set Point,
      (∀ p ∈ S, supp K (π / 2 - α) - 1 ≤ dot p (uvec (π / 2 - α))) →
        ∃ F : Set Point, MeasurableSet F ∧ F ⊆ capShape K ∧ Disjoint S F ∧ area F = c₀ * α := by
  obtain ⟨l, r, d, δ, hlr, hd, hδ, hδ1, hra, hrect⟩ := nearby_left_floor_rectangle hP hbox
  let c₀ := (r - l) * d / 8
  let α₀ := min 1 (min (d / 4) (1 / d))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hα₀ : 0 < α₀ := lt_min (by norm_num) (lt_min (by positivity) (one_div_pos.mpr hd))
  refine ⟨c₀, δ, α₀, hc₀, hδ, hδ1, hα₀, ?_⟩
  intro K hK hclose α hα hαsmall S hterminal
  obtain ⟨hinside, q, hq, hqy, hqx⟩ := hrect K hK hclose
  have hα1 : α ≤ 1 := hαsmall.trans (min_le_left _ _)
  have hαd : α ≤ d / 4 := hαsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hαinv : α ≤ 1 / d := hαsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hheight : α * d / 8 ≤ (1 / 8 : ℝ) := by
    have he := (le_div_iff₀ hd).1 hαinv
    nlinarith
  let F := Icc l r ×ˢ Icc (0 : ℝ) (α * d / 8)
  refine ⟨F, measurableSet_Icc.prod measurableSet_Icc, ?_, ?_, ?_⟩
  · intro p hp
    exact hinside ⟨hp.1, hp.2.1, hp.2.2.trans hheight⟩
  · rw [Set.disjoint_left]
    intro p hpS hpF
    have hpL : p.1 ≤ gerverRoofLeft P - d := hpF.1.2.trans_eq hra
    have he := terminal_excludes_low_left hK hd hα hα1 hαd hq hqy hqx hpL hpF.2.1 hpF.2.2
    exact (not_lt_of_ge (hterminal p hpS)) he
  · rw [area_closed_rectangle hlr.le (by positivity)]
    dsimp [c₀]
    ring

end MovingSofaStability

end TerminalFloor

/-!
## Local terminal-angle comparison

The excluded floor slice and omitted-wedge estimates are now constructed, not
hypotheses supplied by the final theorem. Their competition gives a linear angle
deficit and both directed missing areas.
-/

section TerminalComparison

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The geometric data actually inherited from a partial-angle moving sofa. -/
def PartialSofaConstraints (K S : Set Point) (ω : ℝ) : Prop :=
  S ⊆ K ∧
  (∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω, 0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) ∧
  (∀ p ∈ S, supp K ω - 1 ≤ dot p (uvec ω))

theorem capShape_measurable {K : Set Point} (hK : IsConvexBody K) : MeasurableSet (capShape K) := by
  rw [← partialShape_rightAngle]
  exact partialShape_measurable hK _

/-- Here the full niche is contained in K; this identity is not asserted for all caps. -/
theorem area_capShape_of_niche_subset {K : Set Point} (hK : IsCap K (π / 2))
    (hNK : niche K (π / 2) ⊆ K) : area (capShape K) = sofaArea (π / 2) K := by
  have hN : MeasurableSet (niche K (π / 2)) := by
    rw [← partialNiche_rightAngle]
    exact partialNiche_measurable K _
  have he := area_inter_add_sdiff (S := K) hN hK.2.1.2.1.measure_lt_top.ne
  rw [inter_eq_right.mpr hNK] at he
  change area (niche K (π / 2)) + area (capShape K) = area K at he
  unfold sofaArea
  linarith

/-- Uniform local area and angle reduction for arbitrary measurable partial sofas.
The original set is allowed to contain points outside the full-angle shape. -/
theorem nearby_terminal_comparison {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ c δ α₀ R : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧ 1 ≤ R ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ S : Set Point, MeasurableSet S → ∀ ω ∈ Icc (0 : ℝ) (π / 2),
      π / 2 - ω ≤ α₀ → PartialSofaConstraints K S ω →
        area S ≤ sofaArea (π / 2) K - c * (π / 2 - ω) ∧
        π / 2 - ω ≤ (area (gerverSofa P) - area S) / c ∧
        area (gerverSofa P) - sofaArea (π / 2) K ≤ area (gerverSofa P) - area S ∧
        area (S \ capShape K) ≤ area (gerverSofa P) - area S ∧
        area (capShape K \ S) ≤ 2 * (area (gerverSofa P) - area S) ∧
        ApproxHallways K S (4 * R * (π / 2 - ω)) := by
  obtain ⟨R, hR, hradius⟩ := exists_uniform_cap_radius (GerverParams.gm_isCap hP hbox)
  obtain ⟨c₀, δF, αF, hc₀, hδF, hδF1, hαF, hfloor⟩ := terminal_floor_loss hP hbox
  let Cw := 3 * R + 1
  have hCw : 0 < Cw := by dsimp [Cw]; linarith
  let η := c₀ / (16 * Cw)
  have hη : 0 < η := div_pos hc₀ (by positivity)
  have hηeq : 16 * Cw * η = c₀ := by dsimp [η]; field_simp
  let c := c₀ / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hcoeff : 4 * η * Cw ≤ c := by dsimp [c]; nlinarith
  obtain ⟨δO, αO, hδO, hδO1, hαO, homitted⟩ := nearby_omittedWedges_area hP hbox hη hR
  obtain ⟨δC, hδC, hδC1, hcert⟩ := nearby_cap_certificate hP hbox
  let δ := min δC (min δF δO)
  let α₀ := min αF αO
  have hδ : 0 < δ := lt_min hδC (lt_min hδF hδO)
  have hα₀ : 0 < α₀ := lt_min hαF hαO
  have dC : δ ≤ δC := min_le_left _ _
  have dF : δ ≤ δF := (min_le_right _ _).trans (min_le_left _ _)
  have dO : δ ≤ δO := (min_le_right _ _).trans (min_le_right _ _)
  have d1 : δ ≤ 1 := dC.trans hδC1
  refine ⟨c, δ, α₀, R, hc, hδ, d1, hα₀, hR, ?_⟩
  intro K hK hclose S hS ω hω hαsmall hconstraints
  obtain ⟨hSK, hpartial, hterminal⟩ := hconstraints
  have hα : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  have hrad := hradius K hK (hclose.mono d1)
  obtain ⟨ht, hNK, hAQ, hQM⟩ := hcert K hK (hclose.mono dC)
  have hUM : area (capShape K) ≤ area (gerverSofa P) := by
    rw [area_capShape_of_niche_subset hK hNK]
    exact hAQ.trans hQM
  have hVf : volume (partialShape K ω) ≠ ⊤ :=
    volume_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne
  have hgain : area (partialShape K ω \ capShape K) ≤ c * (π / 2 - ω) := by
    have he := homitted K hK (hclose.mono dO) hrad ω hω
      (hαsmall.trans (min_le_right _ _))
    have hm := mul_le_mul_of_nonneg_right hcoeff hα
    dsimp [Cw] at hm
    exact he.trans hm
  obtain ⟨F, hFm, hFU, hSF, hloss⟩ :
      ∃ F : Set Point, MeasurableSet F ∧ F ⊆ capShape K ∧ Disjoint S F ∧
        2 * c * (π / 2 - ω) ≤ area F := by
    rcases eq_or_lt_of_le hα with he | hp
    · refine ⟨∅, MeasurableSet.empty, empty_subset _, disjoint_empty _, ?_⟩
      simp only [← he, mul_zero, area, measure_empty, ENNReal.toReal_zero, le_refl]
    · obtain ⟨F, hFm, hFU, hSF, harea⟩ := hfloor K hK (hclose.mono dF)
        (π / 2 - ω) hp (hαsmall.trans (min_le_left _ _)) S (by
          simpa only [sub_sub_cancel] using hterminal)
      refine ⟨F, hFm, hFU, hSF, ?_⟩
      rw [harea]
      dsimp [c]
      ring_nf
      exact le_rfl
  have hcomp := terminal_region_comparison hc hα
    (sofa_subset_partialShape hSK hpartial) (capShape_subset_partialShape K hω.2) hFU hSF
    hS (capShape_measurable hK.2.1) hFm hVf hloss hgain hUM
  rw [area_capShape_of_niche_subset hK hNK] at hcomp
  exact ⟨hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2,
    approximate_full_angle_slack hK (by linarith) hrad hω hSK hpartial⟩

end MovingSofaStability

end TerminalComparison
