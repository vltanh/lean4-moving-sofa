module

public import MovingSofaStability.RoofMargins

/-!
# Direct roof-band localization of the competing envelope

Uncompiled proof source. This is the geometric improvement behind the area
estimate: compare the full-angle envelope directly with the reference niche.
The global Hausdorff coefficient is not used. The subsequent exact band-area
integration and square-parallel-layer specialization remain separate steps.
-/

@[expose] public section
noncomputable section

open Real Set MovingSofaOptimality

namespace MovingSofaStability

/-- At a point of the competing envelope inside the reference niche, the
reference roof depth is bounded by the support error divided by the margin. -/
theorem envelope_roof_depth_le {K₀ K : Set Point} {γ : ℝ → ℝ} {c τ δ : ℝ}
    (hK : IsCap K (π / 2)) (hc : 0 < c)
    (hclose : UpperSupportClose δ K K₀) (hsmall : δ < τ)
    (hmargin : RoofSlackMargin K₀ γ c τ)
    {p : Point} (hp : p ∈ capShape K) (hpN : p ∈ niche K₀ (π / 2)) :
    γ p.1 - p.2 ≤ δ / c := by
  obtain ⟨t, ht, hu, hv⟩ := hmargin p hpN
  have hU := (abs_le.mp (slackU_support_error hclose
    ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩ p)).2
  have hV := (abs_le.mp (slackV_support_error hclose ⟨ht.1.le, ht.2.le⟩ p)).2
  have hhall := ((mem_capShape_iff hK p).mp hp).2 t ht
  have hdepth : c * (γ p.1 - p.2) ≤ δ := by
    by_contra hn
    have hmin : δ < min (c * (γ p.1 - p.2)) τ := lt_min (not_le.mp hn) hsmall
    have hu' : innerSlackU K t p < 0 := by linarith
    have hv' : innerSlackV K t p < 0 := by linarith
    exact (not_lt_of_ge hhall) (max_lt hu' hv')
  apply (le_div_iff₀ hc).mpr
  nlinarith only [hdepth]

/-- Localizing the excess does not assume that the input sofa is itself its envelope. -/
theorem envelope_excess_inside_cap_band {K₀ K : Set Point} {γ : ℝ → ℝ}
    {a b H L c τ δ : ℝ}
    (hroof : CapRoofData K₀ a b H L γ) (hK : IsCap K (π / 2)) (hc : 0 < c)
    (hclose : UpperSupportClose δ K K₀) (hsmall : δ < τ)
    (hmargin : RoofSlackMargin K₀ γ c τ) :
    (capShape K \ capShape K₀) ∩ K₀ ⊆
      {p : Point | p.1 ∈ Icc a b ∧ γ p.1 - δ / c ≤ p.2 ∧ p.2 < γ p.1} := by
  rintro p ⟨⟨hp, hpG⟩, hpK₀⟩
  have hpN : p ∈ niche K₀ (π / 2) := by
    by_contra hn
    exact hpG ⟨hpK₀, hn⟩
  have hdepth := envelope_roof_depth_le hK hc hclose hsmall hmargin hp hpN
  rw [hroof.niche_eq] at hpN
  exact ⟨hpN.1, by linarith, hpN.2.2⟩

/-- The adaptive reference margin yields a vertical band of thickness 10.2 delta. -/
theorem envelope_roof_depth_phase {K₀ K : Set Point} {γ : ℝ → ℝ} {τ δ : ℝ}
    (hK : IsCap K (π / 2))
    (hclose : UpperSupportClose δ K K₀) (hsmall : δ < τ)
    (hmargin : RoofSlackMargin K₀ γ (5 / 51) τ)
    {p : Point} (hp : p ∈ capShape K) (hpN : p ∈ niche K₀ (π / 2)) :
    γ p.1 - p.2 ≤ (51 / 5) * δ := by
  have h := envelope_roof_depth_le hK (by norm_num : (0 : ℝ) < 5 / 51)
    hclose hsmall hmargin hp hpN
  nlinarith

end MovingSofaStability
