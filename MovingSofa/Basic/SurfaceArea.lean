module

public import MovingSofa.Basic.ConvexBody
public import MovingSofa.Basic.LebesgueStieltjes
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The surface area measure of a planar convex body

The paper takes the surface area measure `σ_K` from Schneider's book (Definition 2.1.13,
`def:surface-area-measure`) and uses it through two properties: `σ_K({t})` is the length of the edge
`e_K(t)` (Proposition 2.1.2), and `d v_K⁺(t) = v_t σ_K` (Theorem 5.2.2).

We define `σ_K` directly as the Lebesgue–Stieltjes measure on `ℝ` of the monotone right-continuous
function `t ↦ ⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`. In the plane, `⟨v_K⁺(t), v_t⟩` is the right derivative of
`h_K`, so this is the classical identity `σ_K = h_K'' + h_K` in the sense of distributions. Angles are
real numbers: `σ_K` is `2π`-periodic, and the paper's measure on `S¹` is its restriction to any
interval of length `2π`.
-/

@[expose] public section

open Real Set Filter MeasureTheory Topology

namespace MovingSofa

/-- The distribution function of the surface area measure: `⟨v_K⁺(t), v_t⟩ + ∫₀ᵗ h_K`. -/
noncomputable def sigmaFun (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  dot (vplus K t) (vvec t) + ∫ s in (0 : ℝ)..t, supp K s

theorem monotone_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Monotone (sigmaFun K) := by
  sorry

theorem continuousWithinAt_sigmaFun {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    ContinuousWithinAt (sigmaFun K) (Ici t) t := by
  sorry

open Classical in
/-- The Stieltjes function of `σ_K` (the identity function when `K` is not a convex body). -/
noncomputable def sigmaStieltjes (K : Set (ℝ × ℝ)) : StieltjesFunction ℝ :=
  if hK : IsConvexBody K then
    { toFun := sigmaFun K
      mono' := monotone_sigmaFun hK
      right_continuous' := continuousWithinAt_sigmaFun hK }
  else StieltjesFunction.id

/-- The surface area measure `σ_K` of a planar convex body `K` (Definition 2.1.13,
`def:surface-area-measure`), as a `2π`-periodic measure on the angles `t ∈ ℝ`. -/
noncomputable def sigma (K : Set (ℝ × ℝ)) : Measure ℝ := (sigmaStieltjes K).measure

/-- The value `σ_K({t})`, written `σ_K(t)` in the paper. -/
noncomputable def sigmaAt (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := (sigma K {t}).toReal

instance (K : Set (ℝ × ℝ)) : IsLocallyFiniteMeasure (sigma K) := by
  unfold sigma; infer_instance

theorem sigma_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    sigma K (Ioc a b) = ENNReal.ofReal (sigmaFun K b - sigmaFun K a) := by
  simp [sigma, sigmaStieltjes, hK]

theorem sigma_periodic {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (X : Set ℝ) :
    sigma K ((fun t => t + 2 * π) '' X) = sigma K X := by
  sorry

/-- **Proposition 2.1.2** (`pro:surface-area-measure-side-length`). `σ_K(t)` is the length of the
edge `e_K(t)`, and `v_K⁺(t) = v_K⁻(t) + σ_K(t) v_t`. -/
theorem proposition2_1_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    sigmaAt K t = norm2 (vplus K t - vminus K t) ∧
      vplus K t = vminus K t + sigmaAt K t • vvec t := by
  sorry

/-- **Lemma 5.2.1** (`lem:vertex-bounded-variation`). The vertex `v_K⁺` has bounded variation on
every interval. -/
theorem lemma5_2_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    BoundedVariationOn (vplus K) (Icc a b) := by
  sorry

/-- The integrated form of Theorem 5.2.2: `v_K⁺(b) - v_K⁺(a) = ∫_{(a,b]} v_t dσ_K(t)`. -/
theorem vplus_sub_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    vplus K b - vplus K a = ∫ t in Ioc a b, vvec t ∂(sigma K) := by
  sorry

/-- **Theorem 5.2.2** (`thm:boundary-measure`). For `a < b ≤ a + 2π`, `d v_K⁺(t) = v_t σ_K` as
measures on the half-open interval `(a, b]`. -/
theorem theorem5_2_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b ≤ a + 2 * π) :
    (lsMeasure (vplus K) a b).restrict (Ioc a b) =
      ((sigma K).restrict (Ioc a b)).withDensityᵥ vvec := by
  sorry

end MovingSofa
