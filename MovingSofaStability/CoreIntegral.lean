module

public import MovingSofaStability.CoreGraph

/-!
# Change of variables and signed area for the nonsmooth core

Uncompiled proof source. A continuous primitive of the roof function is
composed with the horizontal coordinate. The right-derivative fundamental
theorem then gives change of variables without assuming a C1 competing cap.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- One-dimensional substitution using right derivatives and a continuous integrand. -/
theorem integral_comp_mul_rightDerivative {X X' F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hF : Continuous F)
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt X (X' t) (Ioi t) t)
    (hi : IntervalIntegrable (fun t => F (X t) * X' t) volume a b) :
    (∫ t in a..b, F (X t) * X' t) = ∫ x in X a..X b, F x := by
  sorry

/-- Multiplying a coordinate by a coordinate of the right velocity is integrable. -/
theorem corner_coordinate_velocity_integrable {K : Set Point}
    (hK : IsCap K (π / 2)) (a b : ℝ) :
    IntervalIntegrable (fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2) volume a b ∧
    IntervalIntegrable (fun t => (innerCorner K t).2 * (cornerRightVelocity K t).1) volume a b := by
  sorry

/-- Integration by parts using the right derivative of the coordinate product. -/
theorem corner_coordinate_product_integral {K : Set Point}
    (hK : IsCap K (π / 2)) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (innerCorner K t).1 * (cornerRightVelocity K t).2) +
      (∫ t in a..b, (innerCorner K t).2 * (cornerRightVelocity K t).1) =
      (innerCorner K b).1 * (innerCorner K b).2 -
        (innerCorner K a).1 * (innerCorner K a).2 := by
  sorry

/-- The signed core area is its graph integral and the usual endpoint term. -/
theorem core_curveArea_graph_integral {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℝ} (hF : Continuous F)
    (hgraph : ∀ t ∈ Icc a b, F (innerCorner K t).1 = (innerCorner K t).2) :
    curveArea (innerCorner K) a b =
      (∫ x in (innerCorner K b).1..(innerCorner K a).1, F x) +
      (1 / 2) * ((innerCorner K b).1 * (innerCorner K b).2 -
        (innerCorner K a).1 * (innerCorner K a).2) := by
  sorry

/-- The region under a strictly decreasing nonsmooth core is an ordinary region
between continuous graphs. The change of variables uses the previous lemma. -/
theorem volume_under_core_graph {K : Set Point} (hK : IsCap K (π / 2))
    {a b c H : ℝ} (hab : a < b) (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2)
    (hH : ∀ t ∈ Icc a b, 0 < (innerCorner K t).2 + H) :
    volume ((fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
      {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2 + H}) =
      ENNReal.ofReal (∫ t in a..b, -(cornerRightVelocity K t).1 * ((innerCorner K t).2 + H)) := by
  sorry

end MovingSofaStability
