module

public import MovingSofaStability.OmittedWedgeArea

/-!
# The terminal strip removes a fixed linear amount of floor area

Uncompiled proof source. A fixed rectangle in Gerver's left wing persists in
nearby full-angle shapes. A tilted terminal strip excludes its bottom slice,
whose area is c0 times the missing angle. The slice is constructed explicitly.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- A convenient elementary lower bound, enough for small terminal angles. -/
theorem sin_ge_half_on_unit {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : α / 2 ≤ sin α := by
  sorry

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
    convert he using 1 <;> ext <;> dsimp [l, D, x₀, a] <;> ring
  have hxr : (r, (1 / 4 : ℝ)) ∈ P.cap := by
    have he := hroof.cap.2.1.2.2.add_smul_sub_mem (opt_cap_C_mem hroof.cap) ha
      (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    have hrhalf : (r, (1 / 2 : ℝ)) ∈ P.cap := by
      convert he using 1 <;> ext <;> dsimp [r, D, x₀, a] <;> ring
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
