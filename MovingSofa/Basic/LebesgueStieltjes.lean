module

public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Lebesgue–Stieltjes measures (§5.1)

The paper's Lebesgue–Stieltjes measure `df` of a right-continuous function `f : [a, b] → E` of
bounded variation (Definition 5.1.3, `def:lebesgue-stieltjes`) is the unique finite signed measure
on `[a, b]` with `df({a}) = 0` and `df((a, t]) = f(t) - f(a)`.

We realise it with Mathlib's vector measure `BoundedVariationOn.vectorMeasure` of the function
`t ↦ f (max a (min b t))`, which agrees with `f` on `[a, b]` and is constant outside; that function
has bounded variation on `ℝ` exactly when `f` has bounded variation on `[a, b]`, and its vector measure
gives no mass to `{a}` and the mass `f t - f a` to `(a, t]`. Integrals against `df` are Mathlib's
vector-measure integrals `∫ᵛ`, with an explicit pairing (scalar multiplication, the dot product, or
the cross product).
-/

@[expose] public section

open Set Filter MeasureTheory Topology

namespace MovingSofa

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- The function `f` restricted to `[a, b]` and extended by constants outside. -/
def clampFun {α : Type*} (f : ℝ → α) (a b : ℝ) (t : ℝ) : α := f (max a (min b t))

open Classical in
/-- The Lebesgue–Stieltjes measure `df` of `f` on `[a, b]` (Definition 5.1.3, `def:lebesgue-stieltjes`).
It is meaningful when `f` has bounded variation on `[a, b]`; otherwise it is defined as `0`. -/
noncomputable def lsMeasure (f : ℝ → E) (a b : ℝ) : VectorMeasure ℝ E :=
  if h : BoundedVariationOn (clampFun f a b) univ then h.vectorMeasure else 0

/-- `df` gives no mass to the left endpoint (Definition 5.1.3). -/
theorem lsMeasure_singleton_left {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) :
    lsMeasure f a b {a} = 0 := by
  sorry

/-- `df((a, t]) = f(t) - f(a)` for right-continuous `f` of bounded variation (Definition 5.1.3). -/
theorem lsMeasure_Ioc {f : ℝ → E} {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Icc a b)
    (hf : BoundedVariationOn f (Icc a b)) (hrc : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    lsMeasure f a b (Ioc a t) = f t - f a := by
  sorry

/-- **Proposition 5.1.1** (`pro:lebesgue-stieltjes-sum`). `d(rf + sg) = r df + s dg`. -/
theorem proposition5_1_1 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b)) (r s : ℝ) :
    lsMeasure (fun t => r * f t + s * g t) a b = r • lsMeasure f a b + s • lsMeasure g a b := by
  sorry

/-- **Lemma 5.1.2** (`lem:integration-by-parts`, Revuz–Yor Proposition 4.5). For right-continuous
`f, g` of bounded variation on `[a, b]`,
`∫_{(a,b]} g df + ∫_{(a,b]} f(t-) dg = f(b) g(b) - f(a) g(a)`. -/
theorem lemma5_1_2 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hgr : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x) :
    (∫ᵛ t in Ioc a b, g t ∂• lsMeasure f a b) +
      (∫ᵛ t in Ioc a b, Function.leftLim (clampFun f a b) t ∂• lsMeasure g a b) =
      f b * g b - f a * g a := by
  sorry

/-- **Lemma 5.1.3** (`lem:lebesgue-stieltjes-product`). If one of `f, g` is continuous, then
`d(fg) = g df + f dg` on `[a, b]`; stated on every Borel subset of `[a, b]`. -/
theorem lemma5_1_3 {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hgr : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x)
    (hcont : ContinuousOn f (Icc a b) ∨ ContinuousOn g (Icc a b))
    {X : Set ℝ} (hX : MeasurableSet X) (hXab : X ⊆ Icc a b) :
    lsMeasure (fun t => f t * g t) a b X =
      (∫ᵛ t in X, g t ∂• lsMeasure f a b) + (∫ᵛ t in X, f t ∂• lsMeasure g a b) := by
  sorry

/-- **Proposition 5.1.4** (`pro:lebesgue-stieltjes-abs-cont`). A right-continuous `f` of bounded
variation on `[a, b]` is absolutely continuous iff `df = r dt` for a bounded measurable `r`; then
`f' = r` almost everywhere. -/
theorem proposition5_1_4 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) :
    AbsolutelyContinuousOnInterval f a b ↔
      ∃ r : ℝ → ℝ, Measurable r ∧ (∃ C, ∀ t, |r t| ≤ C) ∧
        lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r := by
  sorry

theorem proposition5_1_4_deriv {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hr : Measurable r) (hrb : ∃ C, ∀ t, |r t| ≤ C)
    (h : lsMeasure f a b = (volume.restrict (Icc a b)).withDensityᵥ r) :
    ∀ᵐ t ∂(volume.restrict (Icc a b)), HasDerivAt f (r t) t := by
  sorry

end MovingSofa
