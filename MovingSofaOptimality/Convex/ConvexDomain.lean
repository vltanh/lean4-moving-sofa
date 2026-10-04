module

public import MovingSofaOptimality.Injectivity.BoundingArms
public import MovingSofaOptimality.External.AreaFormula
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

namespace MovingSofaOptimality

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

/-- A constant multiple of a real-valued convex-bilinear map is convex-bilinear. -/
lemma ConvexDomain.IsConvexBilinear.const_mul {V₁ V₂ : Type} {D₁ : ConvexDomain V₁}
    {D₂ : ConvexDomain V₂} {g : V₁ → V₂ → ℝ} (hg : D₁.IsConvexBilinear D₂ realDomain g) (r : ℝ) :
    D₁.IsConvexBilinear D₂ realDomain (fun v₁ v₂ => r * g v₁ v₂) := by
  refine ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩
  · change r * g v₁ (D₂.comb c v w) = (1 - c) * (r * g v₁ v) + c * (r * g v₁ w)
    rw [hg.1 v₁ c hc v w]; simp only [realDomain]; ring
  · change r * g (D₁.comb c v w) v₂ = (1 - c) * (r * g v v₂) + c * (r * g w v₂)
    rw [show g (D₁.comb c v w) v₂ = _ from hg.2 v₂ c hc v w]; simp only [realDomain]; ring

/-- A quadratic functional on a convex domain (Definition 7.1.4, `def:convex-space-quadratic`). -/
def ConvexDomain.IsQuadratic {V : Type} (D : ConvexDomain V) (h : V → ℝ) : Prop :=
  ∃ g : V → V → ℝ, D.IsConvexBilinear D realDomain g ∧ ∀ v, h v = g v v

/-- The directional derivative `Df(K; K') = d/dλ|_{λ=0} f(c_λ(K, K'))` (Definition 7.1.5,
`def:convex-space-directional-derivative`), as a one-sided derivative on `[0, 1]`. -/
noncomputable def ConvexDomain.dirDeriv {V : Type} (D : ConvexDomain V) (f : V → ℝ) (K K' : V) :
    ℝ :=
  derivWithin (fun c => f (D.comb c K K')) (Icc 0 1) 0

/-- The expansion of a convex-bilinear form along a segment (the display in the proof of
Lemma 7.1.4). -/
lemma cvx_bilin_comb {V : Type} (D : ConvexDomain V) {h : V → V → ℝ}
    (hh : D.IsConvexBilinear D realDomain h) (K K' : V) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    h (D.comb c K K') (D.comb c K K') =
      (1 - c) ^ 2 * h K K + c * (1 - c) * (h K K' + h K' K) + c ^ 2 * h K' K' := by
  have e₀ : h (D.comb c K K') (D.comb c K K') =
      realDomain.comb c (h (D.comb c K K') K) (h (D.comb c K K') K') := hh.1 _ c hc K K'
  have e₁ : h (D.comb c K K') K = realDomain.comb c (h K K) (h K' K) := hh.2 K c hc K K'
  have e₂ : h (D.comb c K K') K' = realDomain.comb c (h K K') (h K' K') := hh.2 K' c hc K K'
  rw [e₀, e₁, e₂]
  simp only [realDomain]
  ring

/-- **Lemma 7.1.4** (`lem:derivative-calculation`). For `f(K) = h(K, K)` with `h` convex-bilinear,
`Df(K; K') = h(K, K') + h(K', K) - 2h(K, K)`. -/
theorem lemma7_1_4 {V : Type} (D : ConvexDomain V) {h : V → V → ℝ}
    (hh : D.IsConvexBilinear D realDomain h) (K K' : V) :
    D.dirDeriv (fun v => h v v) K K' = h K K' + h K' K - 2 * h K K := by
  -- on `[0, 1]`, `λ ↦ h(c_λ(K, K'), c_λ(K, K'))` is the quadratic polynomial of `cvx_bilin_comb`
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hp : ∀ c ∈ Icc (0 : ℝ) 1, h (D.comb c K K') (D.comb c K K') =
      (h K K - (h K K' + h K' K) + h K' K') * c ^ 2 + (h K K' + h K' K - 2 * h K K) * c + h K K :=
    fun c hc => by rw [cvx_bilin_comb D hh K K' hc]; ring
  exact ((hasDerivAt_quad _ _ _ (fun _ => rfl) (by ring)).hasDerivWithinAt.congr hp
    (hp 0 h0)).derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h0)

/-- A concave functional (Definition 7.1.6, `def:convex-space-concavity`). -/
def ConvexDomain.IsConcave {V : Type} (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, (1 - c) * f K₁ + c * f K₂ ≤ f (D.comb c K₁ K₂)

/-- A convex functional (Definition 7.1.6). -/
def ConvexDomain.IsConvexFun {V : Type} (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, f (D.comb c K₁ K₂) ≤ (1 - c) * f K₁ + c * f K₂

/-- **Theorem 7.1.5** (`thm:quadratic-variation`). A concave quadratic functional attains its
maximum at `K` iff `Df(K; -)` is nonpositive. -/
theorem theorem7_1_5 {V : Type} (D : ConvexDomain V) {f : V → ℝ} (hq : D.IsQuadratic f)
    (hc : D.IsConcave f) (K : V) : (∀ K', f K' ≤ f K) ↔ ∀ K', D.dirDeriv f K K' ≤ 0 := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : f = fun v => g v v := funext hfg
  subst hf
  simp only [lemma7_1_4 D hg]
  constructor
  · -- If `Df(K; K') = δ > 0`, then `f(c_λ(K, K')) - f(K) = λδ + λ²E > 0` for small `λ > 0`.
    intro hmax K'
    by_contra hpos
    push Not at hpos
    set δ := g K K' + g K' K - 2 * g K K with hδ
    set E := g K K - (g K K' + g K' K) + g K' K' with hE
    have hle : ∀ c ∈ Icc (0 : ℝ) 1, c * δ + c ^ 2 * E ≤ 0 := by
      intro c hc
      have := hmax (D.comb c K K')
      rw [cvx_bilin_comb D hg K K' hc] at this
      simp only [hδ, hE]
      nlinarith
    set c : ℝ := min 1 (δ / (2 * (|E| + 1))) with hcdef
    have hE1 : 0 < |E| + 1 := by positivity
    have hc0 : 0 < c := lt_min one_pos (by positivity)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hc2 : c ≤ δ / (2 * (|E| + 1)) := min_le_right _ _
    have hcE : c * |E| ≤ δ / 2 := by
      have : c * (|E| + 1) ≤ δ / 2 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|E| + 1))] at hc2
        nlinarith
      nlinarith [abs_nonneg E]
    have h1 := hle c ⟨hc0.le, hc1⟩
    have h2 : -(c * |E|) ≤ c * E := by nlinarith [neg_abs_le E]
    nlinarith
  · -- Concavity at `λ = 1/2` and `Df(K; K') ≤ 0` give `f(K') ≤ f(K)`.
    intro hderiv K'
    have h1 := hderiv K'
    have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have h2 := hc K K' (1 / 2) hhalf
    simp only at h2
    rw [cvx_bilin_comb D hg K K' hhalf] at h2
    nlinarith

/-- `f ≡_V g`: the difference `f - g` is convex-linear (Definition 7.1.7, `def:modulo-linear`). -/
def ConvexDomain.EqModLinear {V : Type} (D : ConvexDomain V) (f g : V → ℝ) : Prop :=
  D.IsConvexLinear realDomain (fun v => f v - g v)

/-- A real vector space as a convex domain. -/
def vectorDomain (V : Type) [AddCommGroup V] [Module ℝ V] : ConvexDomain V where
  comb c v w := (1 - c) • v + c • w
  embeds := ⟨V, inferInstance, inferInstance, id, Function.injective_id, fun _ _ _ _ => rfl⟩

/-- **Lemma 7.1.6** (`lem:modulo-linear-const`). For a convex-bilinear `h` and constants `c₁, c₂`,
`h(K, K) ≡_K h(K + c₁, K + c₂)`.

The formalization reads the lemma in a real vector space, because `K + c` is not defined in a
general convex domain, which has only the operations `c_λ` (REPORT.md, E18). The lemma holds there
for every convex-bilinear `h`, while the paper's proof, `g - f = h(c₁, K) + h(K, c₂) + h(c₁, c₂)`,
covers bilinear `h`. The proof expands `g - f` as the paper does, with the additivity of `h` in
each argument replaced by `h(x + d, y) = h(x, y) + h(d, y) - h(0, y)` (and likewise in `y`), which a
convex-linear map on a vector space satisfies; the terms of the expansion are convex-linear in `K`.
-/
theorem lemma7_1_6 {V : Type} [AddCommGroup V] [Module ℝ V] {h : V → V → ℝ}
    (hh : (vectorDomain V).IsConvexBilinear (vectorDomain V) realDomain h) (c₁ c₂ : V) :
    (vectorDomain V).EqModLinear (fun K => h K K) (fun K => h (K + c₁) (K + c₂)) := by
  -- a convex-linear `g : V → ℝ` is additive up to `g 0`: `g (x + d) + g 0` and `g x + g d` are
  -- both twice the value of `g` at the midpoint of `x` and `d`
  have hadd : ∀ g : V → ℝ, (vectorDomain V).IsConvexLinear realDomain g →
      ∀ x d, g (x + d) = g x + g d - g 0 := by
    intro g hg x d
    have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have e := hg (1 / 2) hc (x + d) 0
    rw [show (vectorDomain V).comb (1 / 2) (x + d) 0 = (vectorDomain V).comb (1 / 2) x d by
      simp only [vectorDomain]; module, hg (1 / 2) hc x d] at e
    simp only [realDomain] at e
    linear_combination -2 * e
  -- the paper's expansion of `f - g`, into terms that are convex-linear in `K`
  have hF : ∀ K, h K K - h (K + c₁) (K + c₂) =
      h K 0 - h K c₂ + h 0 (K + c₂) - h c₁ (K + c₂) := by
    intro K
    have e₁ : h (K + c₁) (K + c₂) = h K (K + c₂) + h c₁ (K + c₂) - h 0 (K + c₂) :=
      hadd (fun x => h x (K + c₂)) (hh.2 (K + c₂)) K c₁
    have e₂ : h K (K + c₂) = h K K + h K c₂ - h K 0 := hadd (h K) (hh.1 K) K c₂
    linear_combination -e₁ - e₂
  have htr : ∀ (c : ℝ) (v w : V), (vectorDomain V).comb c (v + c₂) (w + c₂) =
      (vectorDomain V).comb c v w + c₂ := fun c v w => by simp only [vectorDomain]; module
  intro c hc v w
  have E₁ := hh.2 0 c hc v w
  have E₂ := hh.2 c₂ c hc v w
  have E₃ := hh.1 0 c hc (v + c₂) (w + c₂)
  have E₄ := hh.1 c₁ c hc (v + c₂) (w + c₂)
  rw [htr] at E₃ E₄
  simp only [realDomain] at E₁ E₂ E₃ E₄ ⊢
  rw [hF, hF v, hF w]
  linear_combination E₁ - E₂ + E₃ - E₄

/-! ### The convex domain of planar convex bodies -/

/-- The planar convex bodies `𝒦`. -/
abbrev ConvexBodySet : Type := {K : Set (ℝ × ℝ) // IsConvexBody K}

/-- The Minkowski combination `(1 - λ) K₁ + λ K₂` of convex bodies is a convex body. -/
theorem isConvexBody_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    {c : ℝ} : IsConvexBody ((1 - c) • K₁ + c • K₂) :=
  ⟨h₁.1.smul_set.add h₂.1.smul_set, (h₁.2.1.smul (1 - c)).add (h₂.2.1.smul c),
    (h₁.2.2.smul (1 - c)).add (h₂.2.2.smul c)⟩

/-- The support function is affine under Minkowski combinations (Schneider Theorem 1.7.5 (a)). -/
theorem supp_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    supp ((1 - c) • K₁ + c • K₂) t = (1 - c) * supp K₁ t + c * supp K₂ t := by
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨p₁, hp₁, hp₁e⟩ := exists_dot_eq_supp h₁.2.1 h₁.1 t
    obtain ⟨p₂, hp₂, hp₂e⟩ := exists_dot_eq_supp h₂.2.1 h₂.1 t
    refine ⟨(1 - c) • p₁ + c • p₂,
      Set.add_mem_add (Set.smul_mem_smul_set hp₁) (Set.smul_mem_smul_set hp₂), ?_⟩
    simp only [dot_add_left, dot_smul_left, hp₁e, hp₂e]
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := Set.mem_add.1 hp
    obtain ⟨p₁, hp₁, rfl⟩ := Set.mem_smul_set.1 hq₁
    obtain ⟨p₂, hp₂, rfl⟩ := Set.mem_smul_set.1 hq₂
    simp only [dot_add_left, dot_smul_left]
    have e₁ := dot_le_supp h₁.2.1 hp₁ t
    have e₂ := dot_le_supp h₂.2.1 hp₂ t
    have hc₁ : 0 ≤ 1 - c := by linarith [hc.2]
    nlinarith [hc.1]

open Classical in
/-- The barycentric operation `c_λ(K₁, K₂) = (1 - λ) K₁ + λ K₂` on convex bodies. -/
noncomputable def convexBodyComb (c : ℝ) (K₁ K₂ : ConvexBodySet) : ConvexBodySet :=
  if c ∈ Icc (0 : ℝ) 1 then ⟨(1 - c) • K₁.1 + c • K₂.1, isConvexBody_comb K₁.2 K₂.2⟩ else K₁

/-- For `λ ∈ [0, 1]`, `c_λ(K₁, K₂)` is the Minkowski combination `(1 - λ) K₁ + λ K₂`. -/
lemma cvx_convexBodyComb_val {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) :
    (convexBodyComb c K₁ K₂).1 = (1 - c) • K₁.1 + c • K₂.1 := by
  simp [convexBodyComb, hc]

/-- The support function of `c_λ(K₁, K₂)` is `(1 - λ) h_{K₁} + λ h_{K₂}`. -/
lemma cvx_supp_convexBodyComb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (t : ℝ) :
    supp (convexBodyComb c K₁ K₂).1 t = (1 - c) * supp K₁.1 t + c * supp K₂.1 t := by
  rw [cvx_convexBodyComb_val hc]
  exact supp_comb K₁.2 K₂.2 hc t

/-- **Theorem 7.1.1** (`thm:convex-body-space`). The planar convex bodies form a convex domain under
Minkowski combinations: `K ↦ h_K` embeds them into the vector space of functions `ℝ → ℝ`. -/
theorem theorem7_1_1 : ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : ConvexBodySet → E),
    Function.Injective e ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ v w,
      e (convexBodyComb c v w) = (1 - c) • e v + c • e w := by
  refine ⟨ℝ → ℝ, inferInstance, inferInstance, fun K => supp K.1, ?_, ?_⟩
  · intro K₁ K₂ h
    exact Subtype.ext (eq_of_supp_eq K₁.2 K₂.2 (fun t => congrFun h t))
  · intro c hc v w
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact cvx_supp_convexBodyComb hc v w t

/-- The convex domain `𝒦` of planar convex bodies (Theorem 7.1.1). -/
noncomputable def convexBodyDomain : ConvexDomain ConvexBodySet where
  comb := convexBodyComb
  embeds := theorem7_1_1

/-- **Theorem 7.1.2** (`thm:convex-body-linear`) (1): `h_K` is convex-linear in `K`. -/
theorem theorem7_1_2_supp (t : ℝ) :
    convexBodyDomain.IsConvexLinear realDomain (fun K => supp K.1 t) :=
  fun _ hc v w => cvx_supp_convexBodyComb hc v w t

/-- The vertex `v_K(a, b)` of `c_λ(K₁, K₂)` is the combination of those of `K₁` and `K₂`. -/
lemma cvx_vint_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a b : ℝ) :
    vint (convexBodyComb c K₁ K₂).1 a b = (1 - c) • vint K₁.1 a b + c • vint K₂.1 a b := by
  simp only [vint, cvx_supp_convexBodyComb hc]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    ring

/-- `v_K⁺(a)` of `c_λ(K₁, K₂)` is the combination of those of `K₁` and `K₂` (limit of
`cvx_vint_comb`). -/
lemma cvx_vplus_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a : ℝ) :
    vplus (convexBodyComb c K₁ K₂).1 a = (1 - c) • vplus K₁.1 a + c • vplus K₂.1 a := by
  have h₁ := tendsto_vint_right (convexBodyComb c K₁ K₂).2 a
  have h₂ := ((tendsto_vint_right K₁.2 a).const_smul (1 - c)).add
    ((tendsto_vint_right K₂.2 a).const_smul c)
  simp only [cvx_vint_comb hc] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- `v_K⁻(a)` of `c_λ(K₁, K₂)` is the combination of those of `K₁` and `K₂`. -/
lemma cvx_vminus_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a : ℝ) :
    vminus (convexBodyComb c K₁ K₂).1 a = (1 - c) • vminus K₁.1 a + c • vminus K₂.1 a := by
  have h₁ := tendsto_vint_left (convexBodyComb c K₁ K₂).2 a
  have h₂ := ((tendsto_vint_left K₁.2 a).const_smul (1 - c)).add
    ((tendsto_vint_left K₂.2 a).const_smul c)
  simp only [cvx_vint_comb hc] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- **Theorem 7.1.2** (`thm:convex-body-linear`) (2): for `a < b < a + π`, the vertices `v_K^±(a)`
and `v_K(a, b)` are convex-linear in `K`. -/
theorem theorem7_1_2_vertices (a b : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vplus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vminus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vint K.1 a b) :=
  ⟨fun _ hc v w => cvx_vplus_comb hc v w a, fun _ hc v w => cvx_vminus_comb hc v w a,
    fun _ hc v w => cvx_vint_comb hc v w a b⟩

/-- A bounded measurable function is integrable against the signed measure `f μ`, for a finite
measure `μ` and an integrable density `f`: the integrands of `v_t · d v_K⁺(t)` in the proof of
Theorem 7.1.2 (3). -/
private lemma cvx_integrable_withDensityᵥ {μ : Measure ℝ} [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    (μ.withDensityᵥ f).Integrable g := by
  have := isFiniteMeasure_withDensity (μ := μ) hf.2.ne
  rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hf]
  exact Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- A coordinate of `σ_K = v_t · d v_K⁺(t)`, which follows from Theorem 5.2.2: for a fixed `w`,
`d⟨v_K⁺, w⟩ = ⟨v_t, w⟩ σ_K` on `(a, b]` (`inj_lsMeasure_dot_vplus`), so `⟨v_t, w⟩` is integrable
against `d⟨v_K⁺, w⟩` there and `∫_{(a, b]} ⟨v_t, w⟩ d⟨v_K⁺, w⟩ = ∫_{(a, b]} ⟨v_t, w⟩² dσ_K`. -/
private lemma cvx_integral_dvplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (w : ℝ × ℝ) :
    ((lsMeasure (fun t => dot (vplus K t) w) a b).restrict (Ioc a b)).Integrable
        (fun t => dot (vvec t) w) ∧
      ∫ᵛ t in Ioc a b, dot (vvec t) w ∂• lsMeasure (fun t => dot (vplus K t) w) a b =
        ∫ t in Ioc a b, dot (vvec t) w * dot (vvec t) w ∂(sigma K) := by
  have : IsFiniteMeasure ((sigma K).restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hfc : Continuous fun t => dot (vvec t) w := (continuous_dot w).comp continuous_vvec
  have hb : ∀ t, |dot (vvec t) w| ≤ 2 * ‖w‖ := fun t => by
    have h1 := abs_dot_le (vvec t) w
    have h2 := norm_vvec_le t
    nlinarith [norm_nonneg w]
  rw [inj_lsMeasure_dot_vplus hK hab w]
  exact ⟨cvx_integrable_withDensityᵥ hfc.integrableOn_Ioc hfc.measurable hb,
    inj_integral_withDensityᵥ hfc.integrableOn_Ioc hfc.measurable hfc.measurable hb⟩

/-- `σ_K = v_t · d v_K⁺(t)` on `(a, b]`, which follows from Theorem 5.2.2, coordinate by
coordinate: `σ_K((a, b]) = Σ_w ∫_{(a, b]} ⟨v_t, w⟩ d⟨v_K⁺, w⟩` over `w = (1, 0), (0, 1)`, as
`⟨v_t, v_t⟩ = 1`. -/
private lemma cvx_sigma_Ioc_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b) :
    (sigma K (Ioc a b)).toReal =
      (∫ᵛ t in Ioc a b, dot (vvec t) (1, 0) ∂• lsMeasure (fun t => dot (vplus K t) (1, 0)) a b) +
        ∫ᵛ t in Ioc a b, dot (vvec t) (0, 1) ∂•
          lsMeasure (fun t => dot (vplus K t) (0, 1)) a b := by
  have : IsFiniteMeasure ((sigma K).restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hi : ∀ w : ℝ × ℝ,
      IntegrableOn (fun t => dot (vvec t) w * dot (vvec t) w) (Ioc a b) (sigma K) := fun w =>
    (((continuous_dot w).comp continuous_vvec).mul
      ((continuous_dot w).comp continuous_vvec)).integrableOn_Ioc
  have e : ∀ t, dot (vvec t) (1, 0) * dot (vvec t) (1, 0) +
      dot (vvec t) (0, 1) * dot (vvec t) (0, 1) = 1 := fun t => by
    have h := dot_vvec_self t
    simp only [dot, mul_one, mul_zero, add_zero, zero_add] at h ⊢
    linarith
  rw [(cvx_integral_dvplus hK hab _).2, (cvx_integral_dvplus hK hab _).2,
    ← integral_add (hi _) (hi _)]
  simp_rw [e]
  rw [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- `d v_K⁺` is convex-linear in `K`: `⟨v_K⁺(t), w⟩` is by (2), and the Lebesgue–Stieltjes measure
is linear in the function (Proposition 5.1.1); hence so is `∫_{(a, b]} ⟨v_t, w⟩ d⟨v_K⁺, w⟩`. -/
private lemma cvx_integral_dvplus_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet)
    {a b : ℝ} (hab : a < b) (w : ℝ × ℝ) :
    ∫ᵛ t in Ioc a b, dot (vvec t) w ∂•
        lsMeasure (fun t => dot (vplus (convexBodyComb c K₁ K₂).1 t) w) a b =
      (1 - c) * (∫ᵛ t in Ioc a b, dot (vvec t) w ∂•
          lsMeasure (fun t => dot (vplus K₁.1 t) w) a b) +
        c * ∫ᵛ t in Ioc a b, dot (vvec t) w ∂• lsMeasure (fun t => dot (vplus K₂.1 t) w) a b := by
  have hbv : ∀ K : ConvexBodySet, BoundedVariationOn (fun t => dot (vplus K.1 t) w) (Icc a b) :=
    fun K => by
      simpa [Function.comp_def, dotCLM_apply] using
        (dotCLM w).lipschitzWith.comp_boundedVariationOn (lemma5_2_1 K.2 a b)
  have e : (fun t => dot (vplus (convexBodyComb c K₁ K₂).1 t) w) =
      fun t => (1 - c) * dot (vplus K₁.1 t) w + c * dot (vplus K₂.1 t) w := by
    funext t
    have h : vplus (convexBodyComb c K₁ K₂).1 t = (1 - c) • vplus K₁.1 t + c • vplus K₂.1 t :=
      (theorem7_1_2_vertices t t).1 c hc K₁ K₂
    rw [h, dot_add_left, dot_smul_left, dot_smul_left]
  rw [e, proposition5_1_1 hab.le (hbv K₁) (hbv K₂), VectorMeasure.restrict_add,
    VectorMeasure.restrict_smul, VectorMeasure.restrict_smul,
    VectorMeasure.integral_add_vectorMeasure
      ((cvx_integral_dvplus K₁.2 hab w).1.smul_vectorMeasure _)
      ((cvx_integral_dvplus K₂.2 hab w).1.smul_vectorMeasure _),
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    smul_eq_mul, smul_eq_mul]

/-- **Theorem 7.1.2** (`thm:convex-body-linear`) (3): the surface area measure is convex-linear in
`K`.

As in the paper, (3) comes from (2) and `σ_K = v_t · d v_K⁺(t)`, which follows from
Theorem 5.2.2 (`cvx_sigma_Ioc_eq`, coordinate by coordinate): `d v_K⁺` is convex-linear in `K` by
(2) and Proposition 5.1.1 (`cvx_integral_dvplus_comb`). Both sides agree on the intervals
`(a, b]`. -/
theorem theorem7_1_2_sigma (K₁ K₂ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    sigma (convexBodyComb c K₁ K₂).1 =
      ENNReal.ofReal (1 - c) • sigma K₁.1 + ENNReal.ofReal c • sigma K₂.1 := by
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  have h1 : (0 : ℝ) ≤ 1 - c := by linarith [hc.2]
  -- `σ_K = v_t · d v_K⁺(t)`, with `d v_K⁺` convex-linear in `K`
  have key : (sigma (convexBodyComb c K₁ K₂).1 (Ioc a b)).toReal =
      (1 - c) * (sigma K₁.1 (Ioc a b)).toReal + c * (sigma K₂.1 (Ioc a b)).toReal := by
    rw [cvx_sigma_Ioc_eq (convexBodyComb c K₁ K₂).2 hab, cvx_sigma_Ioc_eq K₁.2 hab,
      cvx_sigma_Ioc_eq K₂.2 hab, cvx_integral_dvplus_comb hc K₁ K₂ hab,
      cvx_integral_dvplus_comb hc K₁ K₂ hab]
    ring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ← ENNReal.ofReal_toReal (measure_Ioc_lt_top (μ := sigma K₁.1) (a := a) (b := b)).ne,
    ← ENNReal.ofReal_toReal (measure_Ioc_lt_top (μ := sigma K₂.1) (a := a) (b := b)).ne,
    ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul hc.1,
    ← ENNReal.ofReal_add (mul_nonneg h1 ENNReal.toReal_nonneg)
      (mul_nonneg hc.1 ENNReal.toReal_nonneg), ← key, ENNReal.ofReal_toReal measure_Ioc_lt_top.ne]

/-- **Theorem 7.1.3** (`thm:area-quadratic-expression`, Schneider Remark 5.1.2).
`|K| = ½ ∫_{S¹} h_K dσ_K`. -/
theorem theorem7_1_3 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    area K = (1 / 2) * ∫ t in Ico 0 (2 * π), supp K t ∂(sigma K) :=
  area_eq_half_integral_supp hK

/-- The integral `∫_X h_{K₁} dσ_{K₂}` over a bounded set is convex-linear in each of
`K₁` and `K₂`. -/
lemma cvx_integral_supp_sigma_bilin {X : Set ℝ} (hXb : Bornology.IsBounded X) :
    convexBodyDomain.IsConvexBilinear convexBodyDomain realDomain
      (fun K₁ K₂ => ∫ t in X, supp K₁.1 t ∂(sigma K₂.1)) := by
  have hint : ∀ K₁ K₂ : ConvexBodySet, IntegrableOn (supp K₁.1) X (sigma K₂.1) := fun K₁ _ =>
    ((continuous_supp K₁.2.2.1).continuousOn.integrableOn_compact
      hXb.isCompact_closure).mono_set subset_closure
  constructor
  · intro K₁ c hc v w
    show ∫ t in X, supp K₁.1 t ∂(sigma (convexBodyComb c v w).1) =
      (1 - c) * ∫ t in X, supp K₁.1 t ∂(sigma v.1) + c * ∫ t in X, supp K₁.1 t ∂(sigma w.1)
    rw [theorem7_1_2_sigma v w hc, Measure.restrict_add, integral_add_measure,
      Measure.restrict_smul, Measure.restrict_smul, integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (by linarith [hc.2]), ENNReal.toReal_ofReal hc.1, smul_eq_mul,
      smul_eq_mul]
    · rw [Measure.restrict_smul]; exact (hint K₁ v).smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul]; exact (hint K₁ w).smul_measure ENNReal.ofReal_ne_top
  · intro K₂ c hc v w
    show ∫ t in X, supp (convexBodyComb c v w).1 t ∂(sigma K₂.1) =
      (1 - c) * ∫ t in X, supp v.1 t ∂(sigma K₂.1) + c * ∫ t in X, supp w.1 t ∂(sigma K₂.1)
    simp only [cvx_supp_convexBodyComb hc]
    rw [integral_add ((hint v K₂).const_mul _) ((hint w K₂).const_mul _), integral_const_mul,
      integral_const_mul]

/-- **Theorem 7.1.3** (`thm:area-quadratic-expression`), second claim: the area is a quadratic
functional on `𝒦`. -/
theorem theorem7_1_3_quadratic : convexBodyDomain.IsQuadratic (fun K => area K.1) :=
  ⟨_, (cvx_integral_supp_sigma_bilin (Metric.isBounded_Ico 0 (2 * π))).const_mul (1 / 2),
    fun K => theorem7_1_3 K.2⟩

end MovingSofaOptimality
