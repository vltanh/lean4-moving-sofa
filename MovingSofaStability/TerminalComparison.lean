module

public import MovingSofaStability.TerminalFloor

/-!
# Local terminal-angle comparison

Uncompiled proof source. The excluded floor slice and omitted-wedge estimates
are now constructed, not hypotheses supplied by the final theorem. Their
competition gives a linear angle deficit and both directed missing areas.
-/

@[expose] public section
noncomputable section

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
