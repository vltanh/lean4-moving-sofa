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
  sorry

end MovingSofaStability
