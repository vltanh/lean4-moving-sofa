module

public import MovingSofaStability.SofaBounds

/-!
# Closed supporting constraints give a genuine motion of the limit

Uncompiled proof source. The original movement paths are not assumed to have
a convergent subsequence. The limit motion is constructed directly from the
limit set's support function and its terminal width. Compact support continuity
is used directly; the actual sofa is not required to be convex.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem compact_innerCorner_continuous {S : Set Point} (hS : IsCompact S) :
    Continuous (innerCorner S) := by
  have hs := continuous_supp hS
  have he : innerCorner S = fun t => (supp S t - 1) • uvec t +
      (supp S (t + π / 2) - 1) • vvec t := by
    funext t
    exact proposition2_2_2_innerCorner S t
  rw [he]
  exact ((hs.sub continuous_const).smul continuous_uvec).add
    (((hs.comp (continuous_id.add continuous_const)).sub continuous_const).smul continuous_vvec)

/-- Canonical placement coordinates equal the two inner-wall slacks. -/
theorem canonical_placement_coordinates (S : Set Point) (t : ℝ) (p : Point) :
    (rot (-t) (p - innerCorner S t)).1 = innerSlackU S t p ∧
    (rot (-t) (p - innerCorner S t)).2 = innerSlackV S t p := by
  sorry

/-- Closed canonical-hallway inequalities and terminal width define a movement. -/
theorem moving_of_supporting_constraints {S : Set Point} {ω : ℝ}
    (hS : IsCompact S) (hc : IsConnected S) (hω : 0 ≤ ω)
    (hstrip : S ⊆ hStrip) (htop : supp S (π / 2) = 1)
    (hwidth : supp S ω + supp S (ω + π) ≤ 1)
    (hslack : ∀ p ∈ S, ∀ t ∈ Icc (0 : ℝ) ω,
      0 ≤ max (innerSlackU S t p) (innerSlackV S t p)) :
    IsMovingSofaWithAngle S ω := by
  sorry

/-- Both slacks pass to limits of compact sets, points, and hallway angles. -/
theorem compactShape_slack_limits {K : ℕ → CompactShape} {L : CompactShape}
    (hK : Tendsto K atTop (𝓝 L)) {p : ℕ → Point} {q : Point}
    (hp : Tendsto p atTop (𝓝 q)) {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun n => innerSlackU (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackU (L : Set Point) a q)) ∧
    Tendsto (fun n => innerSlackV (K n : Set Point) (t n) (p n)) atTop
      (𝓝 (innerSlackV (L : Set Point) a q)) := by
  have hu := continuous_uvec.continuousAt.tendsto.comp ht
  have hv := continuous_vvec.continuousAt.tendsto.comp ht
  have hdu := continuous_dot_pair.continuousAt.tendsto.comp (hp.prodMk_nhds hu)
  have hdv := continuous_dot_pair.continuousAt.tendsto.comp (hp.prodMk_nhds hv)
  have hsu := compactShape_support_tendsto hK ht
  have hsv := compactShape_support_tendsto hK (ht.add_const (π / 2))
  exact ⟨(hdu.sub hsu).add_const 1, (hdv.sub hsv).add_const 1⟩

/-- The class with a reduced angle, fixed supports and an actual movement is
closed under compact-set convergence. -/
theorem normalized_moving_limit {P : GerverParams} {K : ℕ → CompactShape} {L : CompactShape}
    {ωn : ℕ → ℝ} {ω : ℝ} (hK : Tendsto K atTop (𝓝 L)) (hωn : Tendsto ωn atTop (𝓝 ω))
    (hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ωn n))
    (hangles : ∀ n, ωn n ∈ Icc (arccos (5 / 11)) (π / 2))
    (htops : ∀ n, supp (K n : Set Point) (π / 2) = 1)
    (hlefts : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π) :
    IsMovingSofaWithAngle (L : Set Point) ω ∧
      ω ∈ Icc (arccos (5 / 11)) (π / 2) ∧
      supp (L : Set Point) (π / 2) = 1 ∧ supp (L : Set Point) π = supp (gerverSofa P) π := by
  sorry

end MovingSofaStability
