module

public import MovingSofa.Optimality.UpperBound

/-!
# Concavity of `𝒬` (§8.3)

Definitions 8.3.1–8.3.4, Theorems 8.3.1–8.3.2, Lemmas 8.3.3–8.3.7 and Theorem 8.3.8
(`thm:upper-bound-concave`).

**Reading of Definition 8.3.3.** The paper writes `ℛ_B = 𝓜_B(π/2 + φ^R, 3π/2; 𝐥_B^{3π/2})`; the tail
`𝐛_B` and Lemma 8.3.4 use the interval `(π + φ^R, 3π/2)`, which we use.
-/

@[expose] public section

open Real Set

namespace MovingSofa

/-- The parametrization `𝐥_K^t : (t - π, t] → ℝ²` of the supporting line `l_K(t)`:
`𝐥_K^t(s) = v_K(s, t)` for `s < t` and `𝐥_K^t(t) = v_K⁻(t)` (Definition 8.3.1). -/
noncomputable def tangentParam (K : Set (ℝ × ℝ)) (t s : ℝ) : ℝ × ℝ :=
  if s < t then vint K s t else vminus K t

/-- **Theorem 8.3.1** (`thm:tangent-line-parametrization`). For `a ≤ b` in `(t - π, t]`, `𝐥_K^t`
restricted to `[a, b]` is a continuous parametrization of bounded variation of the segment from
`𝐥_K^t(a)` to `𝐥_K^t(b)`, and `𝒥(𝐥_K^t|_{[a,b]}) = 𝒥(𝐥_K^t(a), 𝐥_K^t(b))`. -/
theorem theorem8_3_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t a b : ℝ} (ha : t - π < a)
    (hab : a ≤ b) (hb : b ≤ t) :
    IsCBV (tangentParam K t) a b ∧
      tangentParam K t '' Icc a b = segment ℝ (tangentParam K t a) (tangentParam K t b) ∧
      curveArea (tangentParam K t) a b = segArea (tangentParam K t a) (tangentParam K t b) := by
  sorry

/-- **Theorem 8.3.2** (`thm:tangent-line-param-linear`). `𝐥_K^t|_{[a,b]}` is convex-linear in `K`. -/
theorem theorem8_3_2 {t a b : ℝ} (ha : t - π < a) (hab : a ≤ b) (hb : b ≤ t)
    (K₁ K₂ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Icc a b) :
    tangentParam (convexBodyComb c K₁ K₂).1 t s =
      (1 - c) • tangentParam K₁.1 t s + c • tangentParam K₂.1 t s := by
  sorry

/-- `𝒮_K`, the sum of the four Mamikon regions above the cap (Definition 8.3.2, `def:mamikon-middle`). -/
noncomputable def mamikonS (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  mamikon K 0 φ (tangentParam K (π / 2)) + mamikon K φ (π / 2 - φ) (outerCorner K) +
    mamikon K (π / 2 - φ) (π / 2) (tangentParam K (π / 2 + (π / 2 - φ))) +
    mamikon K (π / 2) π (tangentParam K π)

/-- `ℛ_B = 𝓜_B(π + φ^R, 3π/2; 𝐥_B^{3π/2})` (Definition 8.3.3, `def:mamikon-right-left`; see the module
docstring). -/
noncomputable def mamikonR (φ : ℝ) (B : Set (ℝ × ℝ)) : ℝ :=
  mamikon B (π + φ) (3 * π / 2) (tangentParam B (3 * π / 2))

/-- `ℒ_D = 𝓜_D(3π/2, 3π/2 + φ^L; 𝐥_D^{3π/2 + φ^L})` (Definition 8.3.3). -/
noncomputable def mamikonL (φ : ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  mamikon D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) (tangentParam D (3 * π / 2 + (π / 2 - φ)))

/-- The caps of `𝒦^i` (as a type). -/
abbrev KiSet : Type := {K : ConvexBodySet // IsKi K.1}

open Classical in
/-- The barycentric operation on `𝒦^i` (Theorem 8.1.1 (1)). -/
noncomputable def kiComb (c : ℝ) (K₁ K₂ : KiSet) : KiSet :=
  if hc : c ∈ Icc (0 : ℝ) 1 then
    ⟨convexBodyComb c K₁.1 K₂.1, by simpa [convexBodyComb, hc] using theorem8_1_1_convex K₁.2 K₂.2 hc⟩
  else K₁

theorem kiSet_embeds :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : KiSet → E), Function.Injective e ∧
      ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w, e (kiComb c v w) = (1 - c) • e v + c • e w := by
  sorry

/-- The convex domain `𝒦^i` (Theorem 8.1.1 (1)). -/
noncomputable def kiDomain : ConvexDomain KiSet where
  comb := kiComb
  embeds := kiSet_embeds

/-- **Lemma 8.3.3** (`lem:mamikon-sofa-convex`). `𝒮_K`, `ℛ_B` and `ℒ_D` are convex quadratic
functionals of `K ∈ 𝒦^i`, `B ∈ 𝒦` and `D ∈ 𝒦`. -/
theorem lemma8_3_3 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.IsQuadratic (fun K => mamikonS φ K.1.1) ∧ kiDomain.IsConvexFun (fun K => mamikonS φ K.1.1) ∧
      convexBodyDomain.IsQuadratic (fun B => mamikonR φ B.1) ∧
      convexBodyDomain.IsConvexFun (fun B => mamikonR φ B.1) ∧
      convexBodyDomain.IsQuadratic (fun D => mamikonL φ D.1) ∧
      convexBodyDomain.IsConvexFun (fun D => mamikonL φ D.1) := by
  sorry

/-- `𝒫_K = |K| + 𝒥(Z_K^L, 𝐱_K^L) - 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^R, W_K^R)` (Definition 8.3.4,
`def:upper-bound-middle`). -/
noncomputable def upperP (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  area K + segArea (zLeft φ K) (xLeft φ K) - curveArea (innerCorner K) φ (π / 2 - φ) +
    segArea (xRight φ K) (wRight φ K)

/-- **Lemma 8.3.4** (`lem:upper-bound-decomposition`). On `𝓛`, `𝒬(K, B, D) = 𝒫_K - ℛ_B - ℒ_D`. -/
theorem lemma8_3_4 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    upperQ φ K B D = upperP φ K - mamikonR φ B - mamikonL φ D := by
  sorry

/-- **Lemma 8.3.5** (`lem:upper-boundary-tracing`). On `𝒦^i`,
`|K| ≡_K 𝒥(𝐮_K^{0,φ^R}) + 𝒥(𝐮_K^{φ^R,φ^L}) + 𝒥(𝐮_K^{φ^L,π/2}) + 𝒥(𝐮_K^{π/2,π})`. -/
theorem lemma8_3_5 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => area K.1.1)
      (fun K => convexCurveArea K.1.1 0 φ + convexCurveArea K.1.1 φ (π / 2 - φ) +
        convexCurveArea K.1.1 (π / 2 - φ) (π / 2) + convexCurveArea K.1.1 (π / 2) π) := by
  sorry

/-- **Lemma 8.3.6** (`lem:linvals`). On `𝒦^i`: (1) `𝒥(𝐲_K|_I) ≡_K 𝒥(𝐱_K|_I)`;
(2) `𝒥(𝐥_K^{π/2}(φ^R), 𝐲_K(φ^R)) ≡_K 𝒥(W_K^R, 𝐱_K^R)`;
(3) `𝒥(𝐥_K^{π/2 + φ^L}(φ^L), 𝐲_K(φ^L)) ≡_K 𝒥(Z_K^L, 𝐱_K^L)`. -/
theorem lemma8_3_6 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => curveArea (outerCorner K.1.1) φ (π / 2 - φ))
        (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) ∧
      kiDomain.EqModLinear
        (fun K => segArea (tangentParam K.1.1 (π / 2) φ) (outerCorner K.1.1 φ))
        (fun K => segArea (wRight φ K.1.1) (xRight φ K.1.1)) ∧
      kiDomain.EqModLinear
        (fun K => segArea (tangentParam K.1.1 (π / 2 + (π / 2 - φ)) (π / 2 - φ))
          (outerCorner K.1.1 (π / 2 - φ)))
        (fun K => segArea (zLeft φ K.1.1) (xLeft φ K.1.1)) := by
  sorry

/-- **Lemma 8.3.7** (`lem:mamikon-middle-eq`). On `𝒦^i`, `𝒮_K ≡_K -𝒫_K`. -/
theorem lemma8_3_7 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => mamikonS φ K.1.1) (fun K => -upperP φ K.1.1) := by
  sorry

/-- **Theorem 8.3.8** (`thm:upper-bound-concave`). `𝒬` is concave on `𝓛`. -/
theorem theorem8_3_8 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) : (lDomain φ).IsConcave (upperQL φ) := by
  sorry

end MovingSofa
