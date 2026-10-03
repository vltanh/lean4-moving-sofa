module

public import MovingSofa.Convex.Mamikon
public import SofaUniqueness.SquareGap
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Equality in Mamikon's formula identifies the displacement functions

The square-integrability hypotheses are proved from the bounded measurable
functions supplied by Theorem 7.4.1. Equality cannot arise from Lean's default
value for a nonintegrable integral. The result is first almost-everywhere
 equality and then pointwise equality on any interval where both displacements
are continuous.

Uncompiled source; no admitted statements.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter MovingSofa

namespace SofaUniqueness

/-- Signed tangent displacement from the positive endpoint of the support face. -/
def displacement (K : Set (ℝ × ℝ)) (z : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  dot (z t - vplus K t) (vvec t)

variable {a b : ℝ} (hab : a < b) (hb : b < a + π)
variable (z : ConvexBodySet → ℝ → ℝ × ℝ)
variable (hz : ∀ K, IsCBV (z K) a b)
variable (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)

/-- Products of two tangent displacements are integrable on the interval. -/
theorem displacement_mul_integrable (K₀ K₁ : ConvexBodySet) :
    IntegrableOn (fun t => displacement K₀.1 (z K₀) t * displacement K₁.1 (z K₁) t)
      (Ioo a b) volume := by
  sorry

/-- Mamikon's area in the same restricted-measure form as `SquareGap`. -/
theorem mamikon_eq_halfSquareIntegral (K : ConvexBodySet) :
    mamikon K.1 a b (z K) =
      halfSquareIntegral (volume.restrict (Ioo a b)) (displacement K.1 (z K)) := by
  sorry

variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)

/-- The signed displacement is affine in the convex body. -/
theorem displacement_combo (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc a b) :
    displacement (convexBodyComb c K₀ K₁).1 (z (convexBodyComb c K₀ K₁)) t =
      (1 - c) * displacement K₀.1 (z K₀) t + c * displacement K₁.1 (z K₁) t := by
  sorry

/-- Equality in a nontrivial Mamikon convexity inequality gives a.e. equality
of the underlying displacement functions. -/
theorem displacement_ae_eq_of_mamikon_eq (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁)) :
    displacement K₀.1 (z K₀) =ᵐ[volume.restrict (Ioo a b)] displacement K₁.1 (z K₁) := by
  sorry

/-- Continuity upgrades a.e. displacement equality on the open interval.
Endpoint values are not asserted; the later support argument uses continuity
of the support function itself at those endpoints. -/
theorem displacement_eqOn_of_mamikon_eq (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁))
    (hcont₀ : ContinuousOn (displacement K₀.1 (z K₀)) (Ioo a b))
    (hcont₁ : ContinuousOn (displacement K₁.1 (z K₁)) (Ioo a b)) :
    EqOn (displacement K₀.1 (z K₀)) (displacement K₁.1 (z K₁)) (Ioo a b) := by
  sorry

end SofaUniqueness
