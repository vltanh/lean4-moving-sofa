module

public import MovingSofa.Convex.ConvexCurve

/-!
# Mamikon's theorem (§7.4)

Definitions 7.4.1 (`def:mamikon-region`), 7.4.2 (`def:mamikon`), Theorems 7.4.1 (`thm:mamikon`) and
7.4.2 (`thm:mamikon-convex`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- The Mamikon region swept by the tangent segments from `v_K⁺(t)` to `v_K⁺(t) + α(t) v_t`,
`t ∈ [a, b]` (Definition 7.4.1, `def:mamikon-region`). -/
def mamikonRegion (K : Set (ℝ × ℝ)) (a b : ℝ) (α : ℝ → ℝ) : Set (ℝ × ℝ) :=
  ⋃ t ∈ Icc a b, segment ℝ (vplus K t) (vplus K t + α t • vvec t)

/-- `𝓜_K(a, b; 𝐳) = 𝒥(v_K⁺(a), 𝐳(a)) + 𝒥(𝐳|_{[a,b]}) + 𝒥(𝐳(b), v_K⁻(b)) - 𝒥(𝐮_K^{a,b})`
(Definition 7.4.2, `def:mamikon`). -/
noncomputable def mamikon (K : Set (ℝ × ℝ)) (a b : ℝ) (z : ℝ → ℝ × ℝ) : ℝ :=
  segArea (vplus K a) (z a) + curveArea z a b + segArea (z b) (vminus K b) - convexCurveArea K a b

/-- **Theorem 7.4.1** (`thm:mamikon`, Mamikon's theorem, generalized). For `a < b < a + π` and
`𝐳 ∈ C^BV[a, b]` with `𝐳(t) ∈ l_K(t)`, the function `α(t) = (𝐳(t) - v_K⁺(t)) · v_t` is bounded and
measurable, `𝐳(t) = v_K⁺(t) + α(t) v_t`, and `𝓜_K(a, b; 𝐳) = ½ ∫_a^b α(t)² dt`. -/
theorem theorem7_4_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) {z : ℝ → ℝ × ℝ} (hz : IsCBV z a b) (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) :
    Measurable (fun t => dot (z t - vplus K t) (vvec t)) ∧
      (∃ C, ∀ t ∈ Icc a b, |dot (z t - vplus K t) (vvec t)| ≤ C) ∧
      (∀ t ∈ Icc a b, z t = vplus K t + dot (z t - vplus K t) (vvec t) • vvec t) ∧
      mamikon K a b z = (1 / 2) * ∫ t in a..b, dot (z t - vplus K t) (vvec t) ^ 2 := by
  sorry

/-- **Theorem 7.4.2** (`thm:mamikon-convex`). If `𝐳_K ∈ C^BV[a, b]` lies on the supporting lines
`l_K(t)` and depends convex-linearly on `K`, then `𝓜_K(a, b; 𝐳_K)` is a convex quadratic functional
of `K`. -/
theorem theorem7_4_2 {a b : ℝ} (hab : a < b) (hb : b < a + π) (z : ConvexBodySet → ℝ → ℝ × ℝ)
    (hz : ∀ K, IsCBV (z K) a b) (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
    (hlin : ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb c K₁ K₂) t = (1 - c) • z K₁ t + c • z K₂ t) :
    convexBodyDomain.IsQuadratic (fun K => mamikon K.1 a b (z K)) ∧
      convexBodyDomain.IsConvexFun (fun K => mamikon K.1 a b (z K)) := by
  sorry

end MovingSofa
