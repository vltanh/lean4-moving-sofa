module

public import MovingSofa.Convex.CurveArea

/-!
# Convex curves (§7.3)

Definition 7.3.1 (`def:convex-curve`), Lemma 7.3.1 (`lem:convex-curve-cut`), Theorem 7.3.2
(`thm:convex-curve-area-functional`), Lemmas 7.3.3–7.3.5.

**Reading.** The paper's curve area functional `𝒥(𝐮_K^{a,b})` of the convex arc is defined through a
parametrization of the arc as a Jordan arc, and Theorem 7.3.2 evaluates it to `½ ∫_{(a,b)} h_K dσ_K`.
We name that value `convexCurveArea K a b`; Theorem 7.3.2 exhibits a parametrization of the arc of
bounded variation, from `v_K⁺(a)` to `v_K⁻(b)` and injective unless the arc is a point, whose curve area
functional is this value. Lemma 7.3.5 (1) (the boundary of the region is a counterclockwise Jordan
curve) is replaced by the computation of the area of the region, which is how the paper uses it.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- The convex curve `𝐮_K^{a,b} = {v_K⁺(a)} ∪ ⋃_{t ∈ (a,b)} e_K(t) ∪ {v_K⁻(b)}`
(Definition 7.3.1, `def:convex-curve`). -/
def convexCurve (K : Set (ℝ × ℝ)) (a b : ℝ) : Set (ℝ × ℝ) :=
  {vplus K a} ∪ (⋃ t ∈ Ioo a b, edge K t) ∪ {vminus K b}

/-- The value `½ ∫_{(a,b)} h_K dσ_K` of the curve area functional of `𝐮_K^{a,b}` (Theorem 7.3.2). -/
noncomputable def convexCurveArea (K : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in Ioo a b, supp K t ∂(sigma K)

/-- The bilinear form `𝓑(K₁, K₂) = ½ ∫_{(a,b)} h_{K₁} dσ_{K₂}` (Lemma 7.3.3). -/
noncomputable def convexCurveBilin (K₁ K₂ : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in Ioo a b, supp K₁ t ∂(sigma K₂)

/-- **Lemma 7.3.1** (`lem:convex-curve-cut`), degenerate case: if `v_K⁺(a) = v_K⁻(b)` then
`v_K(a, b) = v_K⁺(a)` and `𝐮_K^{a,b}` is a single point. -/
theorem lemma7_3_1_degenerate {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a = vminus K b) :
    vint K a b = vplus K a ∧ convexCurve K a b = {vplus K a} := by
  sorry

/-- **Lemma 7.3.1** (`lem:convex-curve-cut`), nondegenerate case: if `v_K⁺(a) ≠ v_K⁻(b)`, then
(1) `v_K(a, b)` is not on the line `l'` through `v_K⁺(a)` and `v_K⁻(b)`; (2) the closed half-plane
bounded by `l'` and containing `v_K(a, b)` has normal angle `t' + π` for some `t' ∈ (a, b)`;
(3) `K' = K ∩ H'` is a convex body with (i) `e_{K'}(t) = {v_K⁺(a)}` for `t ∈ (t' - π, a]`,
(ii) `e_{K'}(t) = e_K(t)` for `t ∈ (a, b)`, (iii) `e_{K'}(t) = {v_K⁻(b)}` for `t ∈ [b, t' + π)`,
(iv) `e_{K'}(t' + π)` is the segment from `v_K⁻(b)` to `v_K⁺(a)`. -/
theorem lemma7_3_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a ≠ vminus K b) :
    ∃ t' ∈ Ioo a b, ∃ c : ℝ,
      vplus K a ∈ line (t' + π) c ∧ vminus K b ∈ line (t' + π) c ∧
      dot (vint K a b) (uvec (t' + π)) < c ∧
      IsConvexBody (K ∩ halfMinus (t' + π) c) ∧
      (∀ t ∈ Ioc (t' - π) a, edge (K ∩ halfMinus (t' + π) c) t = {vplus K a}) ∧
      (∀ t ∈ Ioo a b, edge (K ∩ halfMinus (t' + π) c) t = edge K t) ∧
      (∀ t ∈ Ico b (t' + π), edge (K ∩ halfMinus (t' + π) c) t = {vminus K b}) ∧
      edge (K ∩ halfMinus (t' + π) c) (t' + π) = segment ℝ (vminus K b) (vplus K a) := by
  sorry

/-- **Theorem 7.3.2** (`thm:convex-curve-area-functional`). For `a < b < a + π`, the convex curve
`𝐮_K^{a,b}` is the image of a continuous curve of bounded variation from `v_K⁺(a)` to `v_K⁻(b)`,
injective unless the curve is a point, whose curve area functional is `½ ∫_{(a,b)} h_K dσ_K`. -/
theorem theorem7_3_2 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) :
    ∃ γ : ℝ → ℝ × ℝ, IsCBV γ 0 1 ∧ γ '' Icc 0 1 = convexCurve K a b ∧ γ 0 = vplus K a ∧
      γ 1 = vminus K b ∧ (vplus K a ≠ vminus K b → InjOn γ (Icc 0 1)) ∧
      curveArea γ 0 1 = convexCurveArea K a b := by
  sorry

/-- **Theorem 7.3.2**, last claim: `𝒥(𝐮_K^{a,b})` is quadratic in `K`. -/
theorem theorem7_3_2_quadratic {a b : ℝ} (hab : a < b) (hb : b < a + π) :
    convexBodyDomain.IsQuadratic (fun K => convexCurveArea K.1 a b) := by
  sorry

/-- **Lemma 7.3.3** (`lem:convex-curve-bilinear-computation`).
`𝓑(K₁, K₂) = ½ ∫_{(a,b)} v_{K₁}⁺ × dv_{K₂}⁺ = ½ ∫_{(a,b)} v_{K₁}⁻ × dv_{K₂}⁺`, and in particular
`𝒥(𝐮_K^{a,b}) = ½ ∫_{(a,b)} v_K⁺ × dv_K⁺`. -/
theorem lemma7_3_3 {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {a b : ℝ}
    (hab : a < b) (hb : b < a + π) :
    convexCurveBilin K₁ K₂ a b =
        (1 / 2) * ∫ᵛ t in Ioo a b, vplus K₁ t ∂[crossCLM; lsMeasure (vplus K₂) a b] ∧
      convexCurveBilin K₁ K₂ a b =
        (1 / 2) * ∫ᵛ t in Ioo a b, vminus K₁ t ∂[crossCLM; lsMeasure (vplus K₂) a b] := by
  sorry

theorem lemma7_3_3_self {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) :
    convexCurveArea K a b = (1 / 2) * ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure (vplus K) a b] := by
  sorry

/-- **Lemma 7.3.4** (`lem:convex-curve-concat`). For `a < b < c < a + π`, `𝐮_K^{a,c}` is the
concatenation of `𝐮_K^{a,b}`, `e_K(b)` and `𝐮_K^{b,c}`: the union, meeting only at `v_K⁻(b)` and
`v_K⁺(b)`, with additive curve area functionals. -/
theorem lemma7_3_4 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hc : c < a + π) :
    convexCurve K a c = convexCurve K a b ∪ edge K b ∪ convexCurve K b c ∧
      convexCurve K a b ∩ edge K b = {vminus K b} ∧ edge K b ∩ convexCurve K b c = {vplus K b} ∧
      convexCurveArea K a c =
        convexCurveArea K a b + segArea (vminus K b) (vplus K b) + convexCurveArea K b c := by
  sorry

/-- The region of Lemma 7.3.5: the interior of the triangle `v_K⁺(a), v_K(a, b), v_K⁻(b)` outside
`⋂_{t ∈ [a, b]} H_K(t)`. -/
def convexCurveRegion (K : Set (ℝ × ℝ)) (a b : ℝ) : Set (ℝ × ℝ) :=
  interior (convexHull ℝ {vplus K a, vint K a b, vminus K b}) \ ⋂ t ∈ Icc a b, suppHalf K t

/-- **Lemma 7.3.5** (`lem:convex-curve-jordan-curve`) (2) and (3), with (1) replaced by the area of the
region (see the module docstring): the region lies in the interior of `H_K(a) ∩ H_K(b)`, is disjoint
from `⋂_{t ∈ [a,b]} H_K(t)`, and has area `𝒥(v_K⁺(a), v_K(a,b)) + 𝒥(v_K(a,b), v_K⁻(b)) - 𝒥(𝐮_K^{a,b})`. -/
theorem lemma7_3_5 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (h : vplus K a ≠ vminus K b) :
    convexCurveRegion K a b ⊆ interior (suppHalf K a ∩ suppHalf K b) ∧
      Disjoint (convexCurveRegion K a b) (⋂ t ∈ Icc a b, suppHalf K t) ∧
      area (convexCurveRegion K a b) =
        segArea (vplus K a) (vint K a b) + segArea (vint K a b) (vminus K b) -
          convexCurveArea K a b := by
  sorry

end MovingSofa
