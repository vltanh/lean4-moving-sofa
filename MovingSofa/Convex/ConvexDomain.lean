module

public import MovingSofa.Injectivity.BoundingArms
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Convex domains and quadratic functionals (§7.1)

Definitions 7.1.1–7.1.7, Theorems 7.1.1 (`thm:convex-body-space`), 7.1.2 (`thm:convex-body-linear`),
7.1.3 (`thm:area-quadratic-expression`, Schneider Remark 5.1.2), Lemma 7.1.4
(`lem:derivative-calculation`), Theorem 7.1.5 (`thm:quadratic-variation`) and Lemma 7.1.6
(`lem:modulo-linear-const`).
-/

@[expose] public section

open Real Set MeasureTheory
open scoped Pointwise

namespace MovingSofa

/-- A convex domain (Definition 7.1.1, `def:convex-spaces`): a set with barycentric operations
`c_λ`, `λ ∈ [0, 1]`, admitting an injective map into a real vector space that turns `c_λ` into
`(1 - λ) x + λ y`. The operation is given for all real `λ`; only `λ ∈ [0, 1]` is used. -/
structure ConvexDomain (V : Type) where
  comb : ℝ → V → V → V
  embeds : ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : V → E), Function.Injective e ∧
    ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w, e (comb c v w) = (1 - c) • e v + c • e w

/-- The real line as a convex domain. -/
def realDomain : ConvexDomain ℝ where
  comb c x y := (1 - c) * x + c * y
  embeds := ⟨ℝ, inferInstance, inferInstance, id, Function.injective_id, fun c _ v w => by simp⟩

/-- A convex-linear map between convex domains (Definition 7.1.2, `def:convex-linear`). -/
def ConvexDomain.IsConvexLinear {V₁ V₂ : Type} (D₁ : ConvexDomain V₁) (D₂ : ConvexDomain V₂)
    (f : V₁ → V₂) : Prop :=
  ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w, f (D₁.comb c v w) = D₂.comb c (f v) (f w)

/-- A convex-bilinear map (Definition 7.1.3, `def:convex-bilinear`). -/
def ConvexDomain.IsConvexBilinear {V₁ V₂ V₃ : Type} (D₁ : ConvexDomain V₁) (D₂ : ConvexDomain V₂)
    (D₃ : ConvexDomain V₃) (g : V₁ → V₂ → V₃) : Prop :=
  (∀ v₁, D₂.IsConvexLinear D₃ (g v₁)) ∧ ∀ v₂, D₁.IsConvexLinear D₃ (fun v₁ => g v₁ v₂)

/-- A quadratic functional on a convex domain (Definition 7.1.4, `def:convex-space-quadratic`). -/
def ConvexDomain.IsQuadratic {V : Type} (D : ConvexDomain V) (h : V → ℝ) : Prop :=
  ∃ g : V → V → ℝ, D.IsConvexBilinear D realDomain g ∧ ∀ v, h v = g v v

/-- The directional derivative `Df(K; K') = d/dλ|_{λ=0} f(c_λ(K, K'))` (Definition 7.1.5,
`def:convex-space-directional-derivative`), as a one-sided derivative on `[0, 1]`. -/
noncomputable def ConvexDomain.dirDeriv {V : Type} (D : ConvexDomain V) (f : V → ℝ) (K K' : V) : ℝ :=
  derivWithin (fun c => f (D.comb c K K')) (Icc 0 1) 0

/-- **Lemma 7.1.4** (`lem:derivative-calculation`). For `f(K) = h(K, K)` with `h` convex-bilinear,
`Df(K; K') = h(K, K') + h(K', K) - 2h(K, K)`. -/
theorem lemma7_1_4 {V : Type} (D : ConvexDomain V) {h : V → V → ℝ}
    (hh : D.IsConvexBilinear D realDomain h) (K K' : V) :
    D.dirDeriv (fun v => h v v) K K' = h K K' + h K' K - 2 * h K K := by
  sorry

/-- A concave functional (Definition 7.1.6, `def:convex-space-concavity`). -/
def ConvexDomain.IsConcave {V : Type} (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, (1 - c) * f K₁ + c * f K₂ ≤ f (D.comb c K₁ K₂)

/-- A convex functional (Definition 7.1.6). -/
def ConvexDomain.IsConvexFun {V : Type} (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, f (D.comb c K₁ K₂) ≤ (1 - c) * f K₁ + c * f K₂

/-- **Theorem 7.1.5** (`thm:quadratic-variation`). A concave quadratic functional attains its maximum
at `K` iff `Df(K; -)` is nonpositive. -/
theorem theorem7_1_5 {V : Type} (D : ConvexDomain V) {f : V → ℝ} (hq : D.IsQuadratic f)
    (hc : D.IsConcave f) (K : V) : (∀ K', f K' ≤ f K) ↔ ∀ K', D.dirDeriv f K K' ≤ 0 := by
  sorry

/-- `f ≡_V g`: the difference `f - g` is convex-linear (Definition 7.1.7, `def:modulo-linear`). -/
def ConvexDomain.EqModLinear {V : Type} (D : ConvexDomain V) (f g : V → ℝ) : Prop :=
  D.IsConvexLinear realDomain (fun v => f v - g v)

/-- A real vector space as a convex domain. -/
def vectorDomain (V : Type) [AddCommGroup V] [Module ℝ V] : ConvexDomain V where
  comb c v w := (1 - c) • v + c • w
  embeds := ⟨V, inferInstance, inferInstance, id, Function.injective_id, fun _ _ _ _ => rfl⟩

/-- **Lemma 7.1.6** (`lem:modulo-linear-const`). For a bilinear `h` and constants `c₁, c₂`,
`h(K, K) ≡_K h(K + c₁, K + c₂)`. -/
theorem lemma7_1_6 {V : Type} [AddCommGroup V] [Module ℝ V] (h : LinearMap.BilinForm ℝ V)
    (c₁ c₂ : V) : (vectorDomain V).EqModLinear (fun K => h K K) (fun K => h (K + c₁) (K + c₂)) := by
  sorry

/-! ### The convex domain of planar convex bodies -/

/-- The planar convex bodies `𝒦`. -/
abbrev ConvexBodySet : Type := {K : Set (ℝ × ℝ) // IsConvexBody K}

/-- The Minkowski combination `(1 - λ) K₁ + λ K₂` of convex bodies is a convex body. -/
theorem isConvexBody_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) : IsConvexBody ((1 - c) • K₁ + c • K₂) := by
  sorry

/-- The support function is affine under Minkowski combinations (Schneider Theorem 1.7.5 (a)). -/
theorem supp_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    supp ((1 - c) • K₁ + c • K₂) t = (1 - c) * supp K₁ t + c * supp K₂ t := by
  sorry

open Classical in
/-- The barycentric operation `c_λ(K₁, K₂) = (1 - λ) K₁ + λ K₂` on convex bodies. -/
noncomputable def convexBodyComb (c : ℝ) (K₁ K₂ : ConvexBodySet) : ConvexBodySet :=
  if hc : c ∈ Icc (0 : ℝ) 1 then ⟨(1 - c) • K₁.1 + c • K₂.1, isConvexBody_comb K₁.2 K₂.2 hc⟩ else K₁

/-- **Theorem 7.1.1** (`thm:convex-body-space`). The planar convex bodies form a convex domain under
Minkowski combinations: `K ↦ h_K` embeds them into the vector space of functions `ℝ → ℝ`. -/
theorem theorem7_1_1 : ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : ConvexBodySet → E),
    Function.Injective e ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w,
      e (convexBodyComb c v w) = (1 - c) • e v + c • e w := by
  sorry

/-- The convex domain `𝒦` of planar convex bodies (Theorem 7.1.1). -/
noncomputable def convexBodyDomain : ConvexDomain ConvexBodySet where
  comb := convexBodyComb
  embeds := theorem7_1_1

/-- **Theorem 7.1.2** (`thm:convex-body-linear`) (1): `h_K` is convex-linear in `K`. -/
theorem theorem7_1_2_supp (t : ℝ) :
    convexBodyDomain.IsConvexLinear realDomain (fun K => supp K.1 t) := by
  sorry

/-- **Theorem 7.1.2** (2): for `a < b < a + π`, the vertices `v_K^±(a)` and `v_K(a, b)` are
convex-linear in `K`. -/
theorem theorem7_1_2_vertices (a b : ℝ) (hab : a < b) (hb : b < a + π) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vplus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vminus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vint K.1 a b) := by
  sorry

/-- **Theorem 7.1.2** (3): the surface area measure is convex-linear in `K`. -/
theorem theorem7_1_2_sigma (K₁ K₂ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    sigma (convexBodyComb c K₁ K₂).1 =
      ENNReal.ofReal (1 - c) • sigma K₁.1 + ENNReal.ofReal c • sigma K₂.1 := by
  sorry

/-- **Theorem 7.1.3** (`thm:area-quadratic-expression`, Schneider Remark 5.1.2).
`|K| = ½ ∫_{S¹} h_K dσ_K`. -/
theorem theorem7_1_3 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    area K = (1 / 2) * ∫ t in Ico 0 (2 * π), supp K t ∂(sigma K) := by
  sorry

/-- **Theorem 7.1.3**, second claim: the area is a quadratic functional on `𝒦`. -/
theorem theorem7_1_3_quadratic : convexBodyDomain.IsQuadratic (fun K => area K.1) := by
  sorry

end MovingSofa
