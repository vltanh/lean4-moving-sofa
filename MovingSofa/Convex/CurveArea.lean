module

public import MovingSofa.Convex.ConvexDomain

/-!
# The curve area functional (§7.2)

Definitions 7.2.4 (`def:plane-cross-product`), 7.2.5 (`def:bounded-variation-space`), 7.2.6
(`def:curve-area-functional`), 7.2.8 (`def:curve-area-line-segment`); Propositions 7.2.2, 7.2.4–7.2.6.

**Not formalized from this section.** The Jordan curve theorem (Theorem 7.2.1, cited), Green's theorem
for rectifiable Jordan curves (Theorem 7.2.3, cited from Apostol), the notions of Jordan arcs and
curves and their orientation (Definitions 7.2.1–7.2.3, 7.2.7, 7.2.9) and Proposition 7.2.7 (the
orientation of a Jordan curve with a boundary segment). The paper uses them to compute the areas of
specific regions (Lemmas 8.2.2–8.2.3, Theorem 8.4.6); the formalization computes those areas directly
(Fubini and changes of variables). The curve area functional is defined for every continuous curve of
bounded variation, as in Definition 7.2.6, and concatenation is splitting the parameter interval.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofa

/-- The cross product as a continuous bilinear map, the pairing in `∫ p × dμ`. -/
noncomputable def crossCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => LinearMap.toContinuousLinearMap
        { toFun := fun q => cross p q
          map_add' := fun q r => by simp only [cross, Prod.fst_add, Prod.snd_add]; ring
          map_smul' := fun a q => by
            simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun p r => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          add_apply, Prod.fst_add, Prod.snd_add]; ring
      map_smul' := fun a p => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          RingHom.id_apply]; ring }

@[simp] lemma crossCLM_apply (p q : ℝ × ℝ) : crossCLM p q = cross p q := rfl

/-- The space `C^BV[a, b]` of continuous maps of bounded variation `[a, b] → ℝ²`
(Definition 7.2.5, `def:bounded-variation-space`). -/
def IsCBV (x : ℝ → ℝ × ℝ) (a b : ℝ) : Prop :=
  ContinuousOn x (Icc a b) ∧ BoundedVariationOn x (Icc a b)

/-- The bilinear form `𝓑(x₁, x₂) = ½ ∫_a^b x₁(t) × dx₂(t)`. -/
noncomputable def curveBilin (x₁ x₂ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ᵛ t in Icc a b, x₁ t ∂[crossCLM; lsMeasure x₂ a b]

/-- The curve area functional `𝒥(x) = ½ ∫_a^b x(t) × dx(t)` (Definition 7.2.6,
`def:curve-area-functional`). -/
noncomputable def curveArea (x : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ := curveBilin x x a b

/-- `C^BV[a, b]` as a type. -/
abbrev CBV (a b : ℝ) : Type := {x : ℝ → ℝ × ℝ // IsCBV x a b}

/-- `C^BV[a, b]` is closed under linear combinations. -/
theorem isCBV_comb {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hx : IsCBV x a b) (hy : IsCBV y a b) (c : ℝ) :
    IsCBV ((1 - c) • x + c • y) a b := by
  sorry

/-- `C^BV[a, b]` as a convex domain (a real vector space). -/
noncomputable def cbvDomain (a b : ℝ) : ConvexDomain (CBV a b) where
  comb c x y := ⟨(1 - c) • x.1 + c • y.1, isCBV_comb x.2 y.2 c⟩
  embeds := ⟨ℝ → ℝ × ℝ, inferInstance, inferInstance, Subtype.val, Subtype.val_injective,
    fun _ _ _ _ => rfl⟩

/-- **Proposition 7.2.2** (`pro:curve-area-functional-quadratic`). `𝒥` is quadratic on `C^BV[a, b]`. -/
theorem proposition7_2_2 {a b : ℝ} (hab : a ≤ b) :
    (cbvDomain a b).IsQuadratic (fun x => curveArea x.1 a b) := by
  sorry

/-- For a continuously differentiable curve, `𝒥(x) = ½ ∫_a^b x(t) × x'(t) dt`. -/
theorem curveArea_eq_integral {x : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ContDiffOn ℝ 1 x (Icc a b)) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, cross (x t) (derivWithin x (Icc a b) t) := by
  sorry

/-- The curve area functional of a segment, `𝒥(p, q) = (p × q)/2` (Definition 7.2.8,
`def:curve-area-line-segment`). -/
noncomputable def segArea (p q : ℝ × ℝ) : ℝ := cross p q / 2

/-- **Proposition 7.2.4** (`pro:curve-area-line-segment`). The curve area functional of the oriented
segment from `p` to `q` is `𝒥(p, q)`; if `p, q ∈ l(t, h)` and `q - p = d v_t` then `𝒥(p, q) = hd/2`. -/
theorem proposition7_2_4 (p q : ℝ × ℝ) : curveArea (fun s => p + s • (q - p)) 0 1 = segArea p q := by
  sorry

theorem proposition7_2_4_line {p q : ℝ × ℝ} {t h d : ℝ} (hp : p ∈ line t h) (hq : q ∈ line t h)
    (hd : q - p = d • vvec t) : segArea p q = h * d / 2 := by
  sorry

/-- **Proposition 7.2.5** (`pro:curve-area-line-segment-colinear`). If `p`, `q` and the origin lie on
a common line, then `𝒥(p, q) = 0`. -/
theorem proposition7_2_5 {p q : ℝ × ℝ} {t : ℝ} (hp : p ∈ line t 0) (hq : q ∈ line t 0) :
    segArea p q = 0 := by
  sorry

/-- **Proposition 7.2.6** (`pro:curve-area-functional-additive`). The curve area functional is
additive under concatenation: `𝒥(x|_{[a,c]}) = 𝒥(x|_{[a,b]}) + 𝒥(x|_{[b,c]})`. -/
theorem proposition7_2_6 {x : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hx : IsCBV x a c) : curveArea x a c = curveArea x a b + curveArea x b c := by
  sorry

end MovingSofa
