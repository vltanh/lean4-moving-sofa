module

public import MovingSofaStability.EnvelopeSlack

/-!
# Gerver's quantitative roof margin

A roof function is identified with the existing three-piece envelope through
equality of their strict subgraphs. The reference error bound then follows from
the proved envelope slack estimates.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Two nonnegative graph roofs with the same strict subgraph have the same height. -/
theorem roof_value_of_envelope {K Γ : Set Point} {a b H L LΓ : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData K a b H L γ)
    (henv : niche K (π / 2) = envUnderStrict Γ)
    (hΓ : VerticalSlopeBound Γ LΓ)
    (hbounds : ∀ q ∈ Γ, q.1 ∈ Icc a b ∧ 0 ≤ q.2)
    {q : Point} (hq : q ∈ Γ) : q.2 = γ q.1 := by
  have hx := (hbounds q hq).1
  have hq0 := (hbounds q hq).2
  have hγ0 := hroof.roof_nonneg q.1 hx
  apply le_antisymm
  · by_contra hnot
    have hlt : γ q.1 < q.2 := not_le.mp hnot
    let p : Point := (q.1, (γ q.1 + q.2) / 2)
    have hp : p ∈ niche K (π / 2) := by
      rw [henv]
      exact ⟨by dsimp [p]; linarith, q, hq, rfl, by dsimp [p]; linarith⟩
    rw [hroof.niche_eq] at hp
    have hh := hp.2.2
    change (γ q.1 + q.2) / 2 < γ q.1 at hh
    linarith
  · by_contra hnot
    have hlt : q.2 < γ q.1 := not_le.mp hnot
    let p : Point := (q.1, (γ q.1 + q.2) / 2)
    have hp : p ∈ niche K (π / 2) := by
      rw [hroof.niche_eq]
      exact ⟨hx, by dsimp [p]; linarith, by dsimp [p]; linarith⟩
    rw [henv] at hp
    obtain ⟨-, q', hq', hqx, hheight⟩ := hp
    have he : q' = q := eq_of_same_abscissa hΓ hq' hq hqx
    rw [he] at hheight
    change (γ q.1 + q.2) / 2 < q.2 at hheight
    linarith

/-- The uniform roof-wall certificate is supplied by Gerver's established envelope geometry. -/
theorem gerver_roof_slack_margin {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {H L : ℝ} {γ : ℝ → ℝ}
    (hroof : CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ) :
    ∃ c τ : ℝ, 0 < c ∧ 0 < τ ∧ RoofSlackMargin P.cap γ c τ := by
  have hB := romik_bounds hP hbox
  have henv := gn_envHyp hP hB
  have hθ : P.θ < π / 4 := by linarith [henv.ht.2.2.1]
  obtain ⟨LΓ, -, hΓ⟩ := envelope_slope_bound henv hθ (by linarith)
  have hheight : ∀ t ∈ Icc (0 : ℝ) (π / 2), (P.path t).2 < 1 :=
    fun t ht => path_snd_lt_one hP hB ht.1 ht.2
  have hbounds := envelope_bounds_of_path_height henv hheight
  have hniche := gerver_niche_envelope hP hbox
  have hgraph : ∀ q ∈ gerverEnvelope P, q.2 = γ q.1 := by
    intro q hq
    exact roof_value_of_envelope hroof hniche hΓ
      (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1⟩) hq
  obtain ⟨c, τ, hc, hτ, hslack⟩ := envelope_downward_slack henv
    (K := P.cap) (fun t ht => ((theorem8_4_1_monotone hP hbox).2 t ht).2.2)
  refine ⟨c, τ, hc, hτ, ?_⟩
  intro p hp
  rw [hniche] at hp
  obtain ⟨hpy, q, hq, hqx, hlt⟩ := hp
  let d := q.2 - p.2
  have hd : 0 < d := sub_pos.mpr hlt
  have hfloor : 0 ≤ q.2 - d := by dsimp [d]; linarith
  obtain ⟨t, ht, hU, hV⟩ := hslack q hq d hd hfloor
  have he : (q.1, q.2 - d) = p := by
    apply Prod.ext
    · exact hqx
    · dsimp [d]
      ring
  have hdγ : d = γ p.1 - p.2 := by
    dsimp [d]
    rw [hgraph q hq, hqx]
  rw [he, hdγ] at hU hV
  exact ⟨t, ht, hU, hV⟩

/-- All constants needed for the S-to-G directed recovery are properties of Gerver,
not additional assumptions on a near-optimal competing sofa. -/
theorem gerver_recovery_constants {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ H L : ℝ, ∃ γ : ℝ → ℝ, ∃ c τ d₀ κ r₀ : ℝ,
      CapRoofData P.cap (gerverRoofLeft P) (gerverRoofRight P) H L γ ∧
      0 < c ∧ 0 < τ ∧ 0 < d₀ ∧ 0 < κ ∧ 0 < r₀ ∧
      RoofSlackMargin P.cap γ c τ ∧
      (∀ p ∈ niche P.cap (π / 2), ∀ t ∈ Icc (0 : ℝ) π,
        d₀ ≤ supp P.cap t - dot p (uvec t)) ∧
      HasInteriorBalls (gerverSofa P) κ r₀ := by
  obtain ⟨H, L, γ, hroof⟩ := gerver_roof_data hP hbox
  obtain ⟨c, τ, hc, hτ, hslack⟩ := gerver_roof_slack_margin hP hbox hroof
  obtain ⟨d₀, hd₀, houter⟩ := hroof.outer_margin
  obtain ⟨κ, r₀, hκ, hr₀, hballs⟩ := gerver_interiorBalls hP hbox
  exact ⟨H, L, γ, c, τ, d₀, κ, r₀, hroof, hc, hτ, hd₀, hκ, hr₀, hslack, houter, hballs⟩

end MovingSofaStability
