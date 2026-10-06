module

public import MovingSofaStability.LocalBound

/-!
# The cost of a missing final angle

If the sofa turns only through `ω < π/2`, the tilted final strip removes a floor region of area at
least `c (π/2 - ω)`, while the omitted hallway positions add less (`nearby_terminal_comparison`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality GerverParams

namespace MovingSofaStability

/-! ## Gerver's floor is removed before the final angle -/

/-- The floor under Gerver's roof, strictly between its ends, lies in Gerver's niche. -/
theorem gerver_floor_mem_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : ℝ} (hx : x ∈ Ioo (gerverRoofLeft P) (gerverRoofRight P)) :
    (x, 0) ∈ niche P.cap (π / 2) := by
  have h := gn_envHyp hP (romik_bounds hP hbox)
  obtain ⟨q, hq, hqx⟩ := env_exists_curve_fst h ⟨hx.1.le, hx.2.le⟩
  -- every point of the envelope above `x` has positive height
  have hqy : 0 < q.2 := by
    rcases hq with (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · refine env_B₂_pos h ⟨ht.1, ht.2.lt_of_ne ?_⟩
      rintro rfl
      exact hx.2.ne hqx.symm
    · exact h.x_pos t ht
    · refine env_D₂_pos h ⟨ht.1.lt_of_ne ?_, ht.2⟩
      rintro rfl
      exact hx.1.ne hqx
  rw [gerver_niche_envelope hP hbox]
  exact ⟨le_rfl, q, hq, hqx, hqy⟩

/-- Points `(x, 0)` of the niche with `x` in a compact set have witness angles in `(e, π/2 - e)`
with both slacks below `-e`, for one `e > 0`. -/
theorem compact_floor_witnesses {K₀ : Set Point} {I : Set ℝ} (hI : IsCompact I)
    (hfloor : ∀ x ∈ I, (x, 0) ∈ niche K₀ (π / 2)) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ I, ∃ t ∈ Ioo e (π / 2 - e),
      innerSlackU K₀ t (x, 0) < -e ∧ innerSlackV K₀ t (x, 0) < -e := by
  -- the points with witnesses of margin `e` form a directed open cover of `I`
  let U : {e : ℝ // 0 < e} → Set ℝ := fun e => ⋃ t ∈ Ioo e.1 (π / 2 - e.1),
    {x | innerSlackU K₀ t (x, 0) < -e.1 ∧ innerSlackV K₀ t (x, 0) < -e.1}
  have : Nonempty {e : ℝ // 0 < e} := ⟨⟨1, one_pos⟩⟩
  have ho : ∀ e, IsOpen (U e) := fun e => isOpen_biUnion fun t _ =>
    (isOpen_lt (f := fun x : ℝ => innerSlackU K₀ t (x, 0))
      (by unfold innerSlackU dot; fun_prop) continuous_const).inter
      (isOpen_lt (f := fun x : ℝ => innerSlackV K₀ t (x, 0))
        (by unfold innerSlackV dot; fun_prop) continuous_const)
  have hcover : I ⊆ ⋃ e, U e := by
    intro x hx
    obtain ⟨-, t, ht, hU, hV⟩ := (mem_niche_iff_slacks K₀ (x, 0)).1 (hfloor x hx)
    let m := min (min t (π / 2 - t)) (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0)))
    have hm : 0 < m :=
      lt_min (lt_min ht.1 (sub_pos.2 ht.2)) (lt_min (neg_pos.2 hU) (neg_pos.2 hV))
    have h : m / 2 < min (min t (π / 2 - t))
        (min (-innerSlackU K₀ t (x, 0)) (-innerSlackV K₀ t (x, 0))) := half_lt_self hm
    simp only [lt_min_iff] at h
    exact mem_iUnion.2 ⟨⟨m / 2, half_pos hm⟩, mem_iUnion₂.2
      ⟨t, ⟨h.1.1, by linarith [h.1.2]⟩, by linarith [h.2.1], by linarith [h.2.2]⟩⟩
  have hanti : Antitone U := fun e f hef x hx => by
    have hef : e.1 ≤ f.1 := hef
    obtain ⟨t, ht, hU, hV⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨t, ⟨hef.trans_lt ht.1, by linarith [ht.2]⟩, by linarith, by linarith⟩
  obtain ⟨e, he⟩ := hI.elim_directed_cover U ho hcover hanti.directed_le
  refine ⟨e.1, e.2, fun x hx => ?_⟩
  obtain ⟨t, ht, hx'⟩ := mem_iUnion₂.1 (he hx)
  exact ⟨t, ht, hx'⟩

/-- A fixed slab `[l, r] × [0, δ]` of the floor under Gerver's roof is removed, at angles below
`π/2 - e`, from every cap whose supports are `δ`-close to Gerver's. -/
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
  have hδe : δ ≤ e / 4 := min_le_right _ _
  refine ⟨e, δ, he, lt_min one_pos (by linarith), min_le_left _ _, fun K hclose p hp => ?_⟩
  obtain ⟨t, ht, hU, hV⟩ := hw p.1 hp.1
  have htv : t ∈ Ioo (0 : ℝ) (π / 2) := ⟨he.trans ht.1, by linarith [ht.2]⟩
  have hs1 := (abs_le.mp (hclose t ⟨htv.1.le, by linarith [htv.2, pi_pos]⟩)).1
  have hs2 := (abs_le.mp (hclose (t + π / 2)
    ⟨by linarith [htv.1, pi_pos], by linarith [htv.2]⟩)).1
  have hu := mul_le_mul_of_nonneg_left (sin_le_one t) hp.2.1
  have hv := mul_le_mul_of_nonneg_left (cos_le_one t) hp.2.1
  refine ⟨t, ⟨htv.1, ht.2⟩, ?_, ?_⟩
  · simp only [innerSlackU, dot, uvec] at hU ⊢
    linarith [hp.2.2]
  · simp only [innerSlackV, dot, vvec] at hV ⊢
    linarith [hp.2.2]

/-! ## Partial-angle shapes and the omitted wedges -/

/-- The niche `𝒩_ω(K)` of the angles in `(0, ω)`. -/
def partialNiche (K : Set Point) (ω : ℝ) : Set Point :=
  {p | 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) ω, innerSlackU K t p < 0 ∧ innerSlackV K t p < 0}

/-- The partial-angle shape `K \ 𝒩_ω(K)`. -/
def partialShape (K : Set Point) (ω : ℝ) : Set Point := K \ partialNiche K ω

/-- The omitted wedges `O_ω(K) = (K \ 𝒩_ω(K)) \ (K \ 𝒩(K))`. -/
def omittedWedges (K : Set Point) (ω : ℝ) : Set Point := partialShape K ω \ capShape K

/-- The niche of the angles in `(0, π/2)` is the niche. -/
@[simp] theorem partialNiche_rightAngle (K : Set Point) :
    partialNiche K (π / 2) = niche K (π / 2) := by
  ext p
  exact (mem_niche_iff_slacks K p).symm

theorem partialNiche_measurable (K : Set Point) (ω : ℝ) : MeasurableSet (partialNiche K ω) := by
  have he : partialNiche K ω = {p : Point | 0 ≤ p.2} ∩
      ⋃ t ∈ Ioo (0 : ℝ) ω, {p : Point | innerSlackU K t p < 0 ∧ innerSlackV K t p < 0} := by
    ext p
    simp only [partialNiche, mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [he]
  exact (isClosed_le continuous_const continuous_snd).measurableSet.inter
    (isOpen_biUnion fun t _ =>
      (isOpen_lt (f := fun p : Point => innerSlackU K t p)
        (by unfold innerSlackU dot; fun_prop) continuous_const).inter
        (isOpen_lt (f := fun p : Point => innerSlackV K t p)
          (by unfold innerSlackV dot; fun_prop) continuous_const)).measurableSet

theorem niche_measurable (K : Set Point) : MeasurableSet (niche K (π / 2)) :=
  partialNiche_rightAngle K ▸ partialNiche_measurable K _

/-- An omitted point is in the niche at an angle in `[ω, π/2)`. -/
theorem omittedWedges_witness {K : Set Point} {ω : ℝ} {p : Point}
    (hp : p ∈ omittedWedges K ω) :
    p ∈ K ∧ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2), ω ≤ t ∧
      innerSlackU K t p < 0 ∧ innerSlackV K t p < 0 := by
  obtain ⟨hy, t, ht, hu, hv⟩ :=
    (mem_niche_iff_slacks K p).1 (not_not.1 fun h => hp.2 ⟨hp.1.1, h⟩)
  exact ⟨hp.1.1, hy, t, ht, not_lt.1 fun h => hp.1.2 ⟨hy, t, ⟨ht.1, h⟩, hu, hv⟩, hu, hv⟩

/-- The inner corner at an angle `t` near `π/2` has height at most `(3R + 1)(π/2 - t)`. -/
theorem late_corner_height {K : Set Point} (hK : IsCap K (π / 2)) {R : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    (innerCorner K t).2 ≤ (3 * R + 1) * (π / 2 - t) := by
  have hs := support_angle_bound hK.2.1 (by linarith) hradius t (π / 2)
  rw [hK.2.2.2.1, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hs
  have hfirst : supp K t - 1 ≤ 2 * R * (π / 2 - t) := by linarith [(abs_le.mp hs).2]
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
  linarith

/-- The omitted wedges lie under the height `(3R + 1)(π/2 - ω)`. -/
theorem omittedWedges_height {K : Set Point} (hK : IsCap K (π / 2)) {R ω : ℝ}
    (hR : 1 ≤ R) (hradius : ∀ p ∈ K, norm2 p ≤ R) :
    ∀ p ∈ omittedWedges K ω, p.2 ∈ Icc (0 : ℝ) ((3 * R + 1) * (π / 2 - ω)) := by
  intro p hp
  obtain ⟨-, hy, t, ht, hωt, hu, hv⟩ := omittedWedges_witness hp
  have hbelow := point_below_corner_of_negative_slacks ht hu hv
  have hc := late_corner_height hK hR hradius ⟨ht.1.le, ht.2.le⟩
  have hm := mul_le_mul_of_nonneg_left (show π / 2 - t ≤ π / 2 - ω by linarith)
    (show 0 ≤ 3 * R + 1 by linarith)
  exact ⟨hy, by linarith⟩

/-- The area of a closed rectangle. -/
theorem area_closed_rectangle {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    area (Icc a b ×ˢ Icc c d) = (b - a) * (d - c) := by
  rw [area, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]

/-- A set in two windows of width `2η` and height `H` has area at most `4ηH`. -/
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
  linarith

/-- For caps near Gerver's cap and angles `ω` near `π/2`, the omitted wedges have area at most
`4η(3R + 1)(π/2 - ω)`: they lie in two windows of width `2η` at the ends of the roof. -/
theorem nearby_omittedWedges_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {η R : ℝ} (hη : 0 < η) (hR : 1 ≤ R) :
    ∃ δ α₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      (∀ p ∈ K, norm2 p ≤ R) → ∀ ω ∈ Icc (0 : ℝ) (π / 2), π / 2 - ω ≤ α₀ →
        area (omittedWedges K ω) ≤ 4 * η * (3 * R + 1) * (π / 2 - ω) := by
  obtain ⟨δN, hδN, hδN1, hlocal⟩ := nearby_niche_horizontal_localization hP hbox hη
  obtain ⟨e, δF, he, hδF, hδF1, hcover⟩ := gerver_floor_slab_covered hP hbox
    (l := gerverRoofLeft P + η) (r := gerverRoofRight P - η) (by linarith) (by linarith)
  have hCw : 0 < 3 * R + 1 := by linarith
  refine ⟨min δN δF, min (e / 2) (δF / (3 * R + 1)), lt_min hδN hδF,
    (min_le_left _ _).trans hδN1, lt_min (by linarith) (div_pos hδF hCw), ?_⟩
  intro K hK hclose hradius ω hω hα
  have hα0 : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  have hheight : (3 * R + 1) * (π / 2 - ω) ≤ δF := by
    rw [mul_comm, ← le_div_iff₀ hCw]
    exact hα.trans (min_le_right _ _)
  have homega : π / 2 - e < ω := by linarith [hα.trans (min_le_left _ _)]
  have hsub : omittedWedges K ω ⊆
      (Icc (gerverRoofLeft P - η) (gerverRoofLeft P + η) ×ˢ
        Icc (0 : ℝ) ((3 * R + 1) * (π / 2 - ω))) ∪
      (Icc (gerverRoofRight P - η) (gerverRoofRight P + η) ×ˢ
        Icc (0 : ℝ) ((3 * R + 1) * (π / 2 - ω))) := by
    intro p hp
    obtain ⟨hpK, hy0, t, ht, -, hu, hv⟩ := omittedWedges_witness hp
    have hx := hlocal K hK (hclose.mono (min_le_left _ _)) p
      ((mem_niche_iff_slacks K p).2 ⟨hy0, t, ht, hu, hv⟩)
    have hy := omittedWedges_height hK hR hradius p hp
    by_cases hleft : p.1 ≤ gerverRoofLeft P + η
    · exact Or.inl ⟨⟨hx.1, hleft⟩, hy⟩
    by_cases hright : gerverRoofRight P - η ≤ p.1
    · exact Or.inr ⟨⟨hright, hx.2⟩, hy⟩
    -- the middle of the floor is already removed before the angle `ω`
    obtain ⟨s, hs, hsU, hsV⟩ := hcover K (hclose.mono (min_le_right _ _)) p
      ⟨⟨(not_le.mp hleft).le, (not_le.mp hright).le⟩, hy0, hy.2.trans hheight⟩
    exact (hp.1.2 ⟨hy0, s, ⟨hs.1, hs.2.trans homega⟩, hsU, hsV⟩).elim
  have ha := area_two_windows_le hη.le (mul_nonneg hCw.le hα0) hsub
  linarith

/-! ## The final strip misses a rectangle of the floor -/

/-- At angle `π/2 - α`, the lower wall of the hallway excludes the points of height at most
`α d / 8` that lie at least `3d/4` to the left of a point of the cap at height `1`. -/
theorem terminal_excludes_low_left {K : Set Point} (hK : IsCap K (π / 2))
    {a d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hαd : α ≤ d / 4)
    {q p : Point} (hq : q ∈ K) (hqy : q.2 = 1)
    (hqx : a - d / 4 ≤ q.1) (hpx : p.1 ≤ a - d)
    (hpy0 : 0 ≤ p.2) (hpy : p.2 ≤ α * d / 8) :
    dot p (uvec (π / 2 - α)) < supp K (π / 2 - α) - 1 := by
  have hs : α / 2 ≤ sin α := by
    refine le_trans ?_ (Real.mul_le_sin hα.le (by linarith [pi_gt_three]))
    rw [div_mul_eq_mul_div, le_div_iff₀ pi_pos]
    linarith [mul_le_mul_of_nonneg_left pi_le_four hα.le]
  have hc := one_sub_sq_div_two_le_cos (x := α)
  have hup := dot_le_supp hK.2.1.2.1 hq (π / 2 - α)
  simp only [dot, uvec, cos_pi_div_two_sub, sin_pi_div_two_sub, hqy, one_mul] at hup ⊢
  have hm1 := mul_le_mul_of_nonneg_right (show 3 * d / 4 ≤ q.1 - p.1 by linarith)
    (show 0 ≤ sin α by linarith)
  have hm2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 * d / 4 by positivity)
  have hm3 := mul_le_mul_of_nonneg_left (cos_le_one α) hpy0
  have hm4 := mul_le_mul_of_nonneg_left hαd hα.le
  have hpos : 0 < α * d := mul_pos hα hd
  linarith

/-- A fixed rectangle `[l, r] × [0, 1/8]` of the floor, `d` to the left of Gerver's roof, lies in
the shape of every cap near Gerver's cap, and the top edge of such a cap has a point at most
`d/4` to the left of the roof. -/
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
    rw [hra]
    linarith [hroof.order.trans hroof.right_wing]
  -- the rectangle `[l, r] × [0, 1/4]` lies in Gerver's cap, under the segment from `(x₀, 0)` to
  -- `(a, 1)`
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
  have dN : δ ≤ δN := min_le_left _ _
  have dT : δ ≤ δT := (min_le_right _ _).trans (min_le_left _ _)
  have dm : δ ≤ m / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l, r, d, δ, hlr, hd, lt_min hδN (lt_min hδT (by positivity)), dN.trans hδN1, hra,
    fun K hK hclose => ⟨fun p hp => ⟨?_, fun hpN => ?_⟩, ?_⟩⟩
  · -- the rectangle lies in `K`, with margin `m` from the upper supporting lines
    refine (cap_mem_iff_upper hK p).2 ⟨hp.2.1, fun t ht => ?_⟩
    linarith [hmargin p hp t ht, (abs_le.mp (hclose t ht)).1]
  · -- and it misses the niche of `K`, which lies to the right of `a - d/4`
    have hx : a - d / 4 ≤ p.1 := (hN K hK (hclose.mono dN) p hpN).1
    linarith [hp.1.2]
  · -- the top contact of `K`
    have hq := vplus_mem_edge hK.2.1 (π / 2)
    have hqy : (vplus K (π / 2)).2 = 1 := by
      have he : dot (vplus K (π / 2)) (uvec (π / 2)) = supp K (π / 2) := hq.2
      rwa [dot_uvec_pi_div_two, hK.2.2.2.1] at he
    have hqx := (htop K hK (hclose.mono dT) (π / 2) ⟨by positivity, by linarith [pi_pos]⟩
      (by simpa only [sub_self, abs_zero] using hρ.le) _ hq).1
    exact ⟨_, hq.1, hqy, hqx.le⟩

/-- For caps `K` near Gerver's cap and small `α > 0`, every set above the lower wall of the
hallway at angle `π/2 - α` misses a measurable subset of the shape of `K` of area `c₀ α`. -/
theorem terminal_floor_loss {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ c₀ δ α₀ : ℝ, 0 < c₀ ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < α₀ ∧
      ∀ K : Set Point, IsCap K (π / 2) → UpperSupportClose δ K P.cap →
      ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ S : Set Point,
      (∀ p ∈ S, supp K (π / 2 - α) - 1 ≤ dot p (uvec (π / 2 - α))) →
        ∃ F : Set Point, MeasurableSet F ∧ F ⊆ capShape K ∧ Disjoint S F ∧ area F = c₀ * α := by
  obtain ⟨l, r, d, δ, hlr, hd, hδ, hδ1, hra, hrect⟩ := nearby_left_floor_rectangle hP hbox
  refine ⟨(r - l) * d / 8, δ, min 1 (min (d / 4) (1 / d)), by positivity, hδ, hδ1,
    lt_min one_pos (lt_min (by positivity) (one_div_pos.mpr hd)), ?_⟩
  intro K hK hclose α hα hαsmall S hterminal
  obtain ⟨hinside, q, hq, hqy, hqx⟩ := hrect K hK hclose
  simp only [le_min_iff] at hαsmall
  obtain ⟨hα1, hαd, hαinv⟩ := hαsmall
  have hheight : α * d / 8 ≤ (1 / 8 : ℝ) := by linarith [(le_div_iff₀ hd).1 hαinv]
  refine ⟨Icc l r ×ˢ Icc (0 : ℝ) (α * d / 8), measurableSet_Icc.prod measurableSet_Icc,
    fun p hp => hinside ⟨hp.1, hp.2.1, hp.2.2.trans hheight⟩,
    Set.disjoint_left.2 fun p hpS hpF => ?_, ?_⟩
  · exact (terminal_excludes_low_left hK hd hα hα1 hαd hq hqy hqx (hpF.1.2.trans_eq hra)
      hpF.2.1 hpF.2.2).not_ge (hterminal p hpS)
  · rw [area_closed_rectangle hlr.le (by positivity)]
    ring

/-! ## The terminal comparison -/

/-- The constraints of `(K, ω)` on a set `S`: `S ⊆ K`, no point of `S` has both slacks negative at
an angle in `[0, ω]`, and `S` lies above the lower wall of the hallway at angle `ω`. -/
def PartialSofaConstraints (K S : Set Point) (ω : ℝ) : Prop :=
  S ⊆ K ∧
  (∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω, 0 ≤ max (innerSlackU K t p) (innerSlackV K t p)) ∧
  (∀ p ∈ S, supp K ω - 1 ≤ dot p (uvec ω))

/-- If the niche of `K` lies in `K`, the shape of `K` has area `𝒜(K)`. -/
theorem area_capShape_of_niche_subset {K : Set Point} (hK : IsCap K (π / 2))
    (hNK : niche K (π / 2) ⊆ K) : area (capShape K) = sofaArea (π / 2) K := by
  have he := area_inter_add_sdiff (S := K) (niche_measurable K) hK.2.1.2.1.measure_lt_top.ne
  rw [inter_eq_right.mpr hNK] at he
  change area (niche K (π / 2)) + area (capShape K) = area K at he
  unfold sofaArea
  linarith

/-- The terminal comparison: for caps `K` near Gerver's cap, angles `ω` near `π/2` and measurable
sets `S` with the constraints of `(K, ω)`, `|S| ≤ 𝒜(K) - c (π/2 - ω)`. So the deficit `|G| - |S|`
bounds `π/2 - ω`, `|G| - 𝒜(K)` and the two directed missing areas against the shape of `K`, and `S`
violates the hallways by at most `4R (π/2 - ω)`. -/
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
  obtain ⟨R, hR, hradius⟩ := exists_uniform_cap_radius (gm_isCap hP hbox)
  obtain ⟨c₀, δF, αF, hc₀, hδF, hδF1, hαF, hfloor⟩ := terminal_floor_loss hP hbox
  -- the gain of the omitted wedges is at most `c (π/2 - ω)`, half the floor loss
  let c := c₀ / 2
  let η := c₀ / (16 * (3 * R + 1))
  have hη : 0 < η := div_pos hc₀ (by positivity)
  have hcoeff : 4 * η * (3 * R + 1) ≤ c := by
    have he : 4 * η * (3 * R + 1) = c₀ / 4 := by
      dsimp only [η]
      field_simp
      ring
    dsimp only [c]
    linarith
  obtain ⟨δO, αO, hδO, hδO1, hαO, homitted⟩ := nearby_omittedWedges_area hP hbox hη hR
  obtain ⟨δC, hδC, hδC1, hcert⟩ := nearby_cap_certificate hP hbox
  let δ := min δC (min δF δO)
  have dC : δ ≤ δC := min_le_left _ _
  have dF : δ ≤ δF := (min_le_right _ _).trans (min_le_left _ _)
  have dO : δ ≤ δO := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, δ, min αF αO, R, by positivity, lt_min hδC (lt_min hδF hδO), dC.trans hδC1,
    lt_min hαF hαO, hR, ?_⟩
  rintro K hK hclose S hS ω hω hαsmall ⟨hSK, hpartial, hterminal⟩
  have hα : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  have hrad := hradius K hK (hclose.mono (dC.trans hδC1))
  obtain ⟨-, hNK, hAQ, hQM⟩ := hcert K hK (hclose.mono dC)
  -- `V = K \ 𝒩_ω(K)` contains `U = K \ 𝒩(K)` and, by the constraints, `S`
  have hSV : S ⊆ partialShape K ω := fun p hp => ⟨hSK hp, fun ⟨_, t, ht, hu, hv⟩ =>
    (hpartial p hp t ⟨ht.1.le, ht.2.le⟩).not_gt (max_lt hu hv)⟩
  have hUV : capShape K ⊆ partialShape K ω := fun p ⟨hp, hn⟩ => ⟨hp, fun ⟨hy, t, ht, hu, hv⟩ =>
    hn ((mem_niche_iff_slacks K p).2 ⟨hy, t, ⟨ht.1, ht.2.trans_le hω.2⟩, hu, hv⟩)⟩
  have hgain : area (partialShape K ω \ capShape K) ≤ c * (π / 2 - ω) :=
    (homitted K hK (hclose.mono dO) hrad ω hω (hαsmall.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right hcoeff hα)
  -- the floor rectangle missed by `S`, empty if `ω = π/2`
  obtain ⟨F, hFm, hFU, hSF, hloss⟩ : ∃ F : Set Point, MeasurableSet F ∧ F ⊆ capShape K ∧
      Disjoint S F ∧ 2 * c * (π / 2 - ω) ≤ area F := by
    rcases hα.eq_or_lt with he | hp
    · refine ⟨∅, MeasurableSet.empty, empty_subset _, disjoint_empty _, ?_⟩
      simp only [← he, mul_zero, area, measure_empty, ENNReal.toReal_zero, le_refl]
    · obtain ⟨F, hFm, hFU, hSF, harea⟩ := hfloor K hK (hclose.mono dF) (π / 2 - ω) hp
        (hαsmall.trans (min_le_left _ _)) S (by simpa only [sub_sub_cancel] using hterminal)
      refine ⟨F, hFm, hFU, hSF, ?_⟩
      rw [harea]
      dsimp only [c]
      linarith
  have hUM : area (capShape K) ≤ area (gerverSofa P) := by
    rw [area_capShape_of_niche_subset hK hNK]
    exact hAQ.trans hQM
  have hcomp := terminal_region_comparison (by positivity) hα hSV hUV hFU hSF hS
    (hK.2.1.2.1.measurableSet.diff (niche_measurable K)) hFm
    (measure_ne_top_of_subset sdiff_subset hK.2.1.2.1.measure_lt_top.ne) hloss hgain hUM
  rw [area_capShape_of_niche_subset hK hNK] at hcomp
  exact ⟨hcomp.1, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2.1, hcomp.2.2.2.2,
    approximate_full_angle_slack hK (by linarith) hrad hω hSK hpartial⟩

end MovingSofaStability
