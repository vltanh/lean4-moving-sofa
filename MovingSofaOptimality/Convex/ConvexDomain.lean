module

public import MovingSofaOptimality.Injectivity.BoundingArms
public import MovingSofaOptimality.External.AreaFormula
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

/-- A quadratic functional on a convex domain (Definition 7.1.4, `def:convex-space-quadratic`). -/
def ConvexDomain.IsQuadratic {V : Type} (D : ConvexDomain V) (h : V → ℝ) : Prop :=
  ∃ g : V → V → ℝ, D.IsConvexBilinear D realDomain g ∧ ∀ v, h v = g v v

/-- The directional derivative `Df(K; K') = d/dλ|_{λ=0} f(c_λ(K, K'))` (Definition 7.1.5,
`def:convex-space-directional-derivative`), as a one-sided derivative on `[0, 1]`. -/
noncomputable def ConvexDomain.dirDeriv {V : Type} (D : ConvexDomain V) (f : V → ℝ) (K K' : V) : ℝ :=
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

private lemma cvx_hasDerivAt_quad (A B C : ℝ) :
    HasDerivAt (fun c : ℝ => A + c * (B - 2 * A) + c * c * (A - B + C)) (B - 2 * A) 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).mul_const (B - 2 * A)
  have h2 := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (A - B + C)
  have := (h1.add h2).const_add A
  convert this using 1
  · funext c; simp [add_assoc]
  · simp

/-- **Lemma 7.1.4** (`lem:derivative-calculation`). For `f(K) = h(K, K)` with `h` convex-bilinear,
`Df(K; K') = h(K, K') + h(K', K) - 2h(K, K)`. -/
theorem lemma7_1_4 {V : Type} (D : ConvexDomain V) {h : V → V → ℝ}
    (hh : D.IsConvexBilinear D realDomain h) (K K' : V) :
    D.dirDeriv (fun v => h v v) K K' = h K K' + h K' K - 2 * h K K := by
  unfold ConvexDomain.dirDeriv
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hp : ∀ c ∈ Icc (0 : ℝ) 1, h (D.comb c K K') (D.comb c K K') =
      h K K + c * ((h K K' + h K' K) - 2 * h K K) +
        c * c * (h K K - (h K K' + h K' K) + h K' K') := by
    intro c hc
    rw [cvx_bilin_comb D hh K K' hc]
    ring
  rw [derivWithin_congr (f := fun c : ℝ => h K K + c * ((h K K' + h K' K) - 2 * h K K) +
      c * c * (h K K - (h K K' + h K' K) + h K' K')) (fun c hc => hp c hc) (hp 0 h0)]
  rw [(cvx_hasDerivAt_quad _ _ _).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc zero_lt_one 0 h0)]

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
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : f = fun v => g v v := funext hfg
  subst hf
  simp only [lemma7_1_4 D hg]
  constructor
  · intro hmax K'
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
  · intro hderiv K'
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

/-- **Lemma 7.1.6** (`lem:modulo-linear-const`). For a bilinear `h` and constants `c₁, c₂`,
`h(K, K) ≡_K h(K + c₁, K + c₂)`. -/
theorem lemma7_1_6 {V : Type} [AddCommGroup V] [Module ℝ V] (h : LinearMap.BilinForm ℝ V)
    (c₁ c₂ : V) : (vectorDomain V).EqModLinear (fun K => h K K) (fun K => h (K + c₁) (K + c₂)) := by
  intro c _ v w
  simp only [vectorDomain, realDomain, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

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

/-- **Theorem 7.1.1** (`thm:convex-body-space`). The planar convex bodies form a convex domain under
Minkowski combinations: `K ↦ h_K` embeds them into the vector space of functions `ℝ → ℝ`. -/
lemma cvx_convexBodyComb_val {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) :
    (convexBodyComb c K₁ K₂).1 = (1 - c) • K₁.1 + c • K₂.1 := by
  simp [convexBodyComb, hc]

lemma cvx_supp_convexBodyComb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (t : ℝ) :
    supp (convexBodyComb c K₁ K₂).1 t = (1 - c) * supp K₁.1 t + c * supp K₂.1 t := by
  rw [cvx_convexBodyComb_val hc]
  exact supp_comb K₁.2 K₂.2 hc t

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
    convexBodyDomain.IsConvexLinear realDomain (fun K => supp K.1 t) := by
  intro c hc v w
  exact cvx_supp_convexBodyComb hc v w t

lemma cvx_vint_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a b : ℝ) :
    vint (convexBodyComb c K₁ K₂).1 a b = (1 - c) • vint K₁.1 a b + c • vint K₂.1 a b := by
  simp only [vint, cvx_supp_convexBodyComb hc]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    ring

lemma cvx_vplus_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a : ℝ) :
    vplus (convexBodyComb c K₁ K₂).1 a = (1 - c) • vplus K₁.1 a + c • vplus K₂.1 a := by
  have h₁ := tendsto_vint_right (convexBodyComb c K₁ K₂).2 a
  have h₂ := ((tendsto_vint_right K₁.2 a).const_smul (1 - c)).add
    ((tendsto_vint_right K₂.2 a).const_smul c)
  simp only [cvx_vint_comb hc] at h₁
  exact tendsto_nhds_unique h₁ h₂

lemma cvx_vminus_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (a : ℝ) :
    vminus (convexBodyComb c K₁ K₂).1 a = (1 - c) • vminus K₁.1 a + c • vminus K₂.1 a := by
  have h₁ := tendsto_vint_left (convexBodyComb c K₁ K₂).2 a
  have h₂ := ((tendsto_vint_left K₁.2 a).const_smul (1 - c)).add
    ((tendsto_vint_left K₂.2 a).const_smul c)
  simp only [cvx_vint_comb hc] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- **Theorem 7.1.2** (2): for `a < b < a + π`, the vertices `v_K^±(a)` and `v_K(a, b)` are
convex-linear in `K`. -/
theorem theorem7_1_2_vertices (a b : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vplus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vminus K.1 a) ∧
      convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vint K.1 a b) :=
  ⟨fun _ hc v w => cvx_vplus_comb hc v w a, fun _ hc v w => cvx_vminus_comb hc v w a,
    fun _ hc v w => cvx_vint_comb hc v w a b⟩

lemma cvx_sigmaFun_comb {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) (t : ℝ) :
    sigmaFun (convexBodyComb c K₁ K₂).1 t =
      (1 - c) * sigmaFun K₁.1 t + c * sigmaFun K₂.1 t := by
  have hi₁ : IntervalIntegrable (supp K₁.1) volume 0 t :=
    (continuous_supp K₁.2.2.1).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (supp K₂.1) volume 0 t :=
    (continuous_supp K₂.2.2.1).intervalIntegrable _ _
  simp only [sigmaFun, cvx_vplus_comb hc, cvx_supp_convexBodyComb hc, dot_add_left,
    dot_smul_left]
  rw [intervalIntegral.integral_add (hi₁.const_mul _) (hi₂.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- **Theorem 7.1.2** (3): the surface area measure is convex-linear in `K`. -/
theorem theorem7_1_2_sigma (K₁ K₂ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    sigma (convexBodyComb c K₁ K₂).1 =
      ENNReal.ofReal (1 - c) • sigma K₁.1 + ENNReal.ofReal c • sigma K₂.1 := by
  have hS : sigmaStieltjes (convexBodyComb c K₁ K₂).1 =
      (1 - c).toNNReal • sigmaStieltjes K₁.1 + c.toNNReal • sigmaStieltjes K₂.1 := by
    ext t
    have h1 : (0 : ℝ) ≤ 1 - c := by linarith [hc.2]
    simp only [sigmaStieltjes, (convexBodyComb c K₁ K₂).2, K₁.2, K₂.2, dite_true,
      StieltjesFunction.add_apply]
    change sigmaFun _ t = ((1 - c).toNNReal : ℝ) * sigmaFun _ t + (c.toNNReal : ℝ) * sigmaFun _ t
    rw [Real.coe_toNNReal _ h1, Real.coe_toNNReal _ hc.1]
    exact cvx_sigmaFun_comb hc K₁ K₂ t
  simp only [sigma, hS, StieltjesFunction.measure_add, StieltjesFunction.measure_smul]
  rfl

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
  have hint : ∀ K₁ K₂ : ConvexBodySet, IntegrableOn (supp K₁.1) X (sigma K₂.1) := by
    intro K₁ K₂
    obtain ⟨R, hR⟩ := hXb.subset_closedBall 0
    have hsub : X ⊆ Icc (-R) R := by
      intro x hx
      have := hR hx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    exact ((continuous_supp K₁.2.2.1).integrableOn_Icc).mono_set hsub
  constructor
  · intro K₁ c hc v w
    show ∫ t in X, supp K₁.1 t ∂(sigma (convexBodyComb c v w).1) =
      (1 - c) * ∫ t in X, supp K₁.1 t ∂(sigma v.1) + c * ∫ t in X, supp K₁.1 t ∂(sigma w.1)
    rw [theorem7_1_2_sigma v w hc, Measure.restrict_add, integral_add_measure, Measure.restrict_smul,
      Measure.restrict_smul, integral_smul_measure, integral_smul_measure,
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

/-- **Theorem 7.1.3**, second claim: the area is a quadratic functional on `𝒦`. -/
theorem theorem7_1_3_quadratic : convexBodyDomain.IsQuadratic (fun K => area K.1) := by
  have hb := cvx_integral_supp_sigma_bilin (X := Ico 0 (2 * π)) (Metric.isBounded_Ico _ _)
  refine ⟨fun K₁ K₂ => (1 / 2) * ∫ t in Ico 0 (2 * π), supp K₁.1 t ∂(sigma K₂.1), ⟨?_, ?_⟩,
    fun K => theorem7_1_3 K.2⟩
  · intro K₁ c hc v w
    have := hb.1 K₁ c hc v w
    simp only [realDomain] at this ⊢
    rw [this]
    ring
  · intro K₂ c hc v w
    have := hb.2 K₂ c hc v w
    simp only [realDomain] at this ⊢
    rw [this]
    ring

end MovingSofaOptimality
