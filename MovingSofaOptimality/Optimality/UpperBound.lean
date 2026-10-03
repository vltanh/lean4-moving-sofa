module

public import MovingSofaOptimality.Optimality.Domain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Definition of `𝒬` (§8.2)

Definitions 8.2.1 (`def:right-left-tails`), 8.2.2 (`def:upper-bound-q`), Proposition 8.2.1, Lemmas
8.2.2 (`lem:cap-left-right-tail`), 8.2.3 (`lem:cap-middle-lower-estimate`) and Theorem 8.2.4
(`thm:upper-bound-q`). The curve area functionals of the tails are the values of Theorem 7.3.2, and
that of the core is the curve area functional of the rotation path on `[φ^R, φ^L]`.
-/

@[expose] public section

open Real Set
open scoped Pointwise

namespace MovingSofaOptimality

attribute [local simp] dot_mk

/-! ### Auxiliary facts: convex domains, regularity of `𝐱_K`, curve areas -/

section ConvexDomainAux

variable {U V W : Type}

/-- A composition of convex-linear maps is convex-linear. -/
lemma opt_isConvexLinear_comp {D₁ : ConvexDomain U} {D₂ : ConvexDomain V} {D₃ : ConvexDomain W}
    {f : U → V} {g : V → W} (hf : D₁.IsConvexLinear D₂ f) (hg : D₂.IsConvexLinear D₃ g) :
    D₁.IsConvexLinear D₃ (fun u => g (f u)) := fun c hc v w => by
  simp only [hf c hc, hg c hc]

/-- A quadratic functional composed with a convex-linear map is quadratic. -/
lemma opt_isQuadratic_comp {D₁ : ConvexDomain U} {D₂ : ConvexDomain V} {pr : U → V}
    (hpr : D₁.IsConvexLinear D₂ pr) {f : V → ℝ} (hf : D₂.IsQuadratic f) :
    D₁.IsQuadratic (fun v => f (pr v)) := by
  obtain ⟨g, ⟨hg1, hg2⟩, hfg⟩ := hf
  refine ⟨fun v w => g (pr v) (pr w), ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩,
    fun v => hfg _⟩
  · simp only [hpr c hc]; exact hg1 _ c hc _ _
  · simp only [hpr c hc]; exact hg2 _ c hc _ _

/-- A sum of quadratic functionals is quadratic. -/
lemma opt_isQuadratic_add {D : ConvexDomain U} {f g : U → ℝ} (hf : D.IsQuadratic f)
    (hg : D.IsQuadratic g) : D.IsQuadratic (fun v => f v + g v) := by
  obtain ⟨F, ⟨hF1, hF2⟩, hfF⟩ := hf
  obtain ⟨G, ⟨hG1, hG2⟩, hgG⟩ := hg
  refine ⟨fun v w => F v w + G v w, ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩,
    fun v => by simp only [hfF, hgG]⟩
  · have h1 := hF1 v₁ c hc v w
    have h2 := hG1 v₁ c hc v w
    simp only [realDomain] at h1 h2 ⊢
    rw [h1, h2]; ring
  · have h1 := hF2 v₂ c hc v w
    have h2 := hG2 v₂ c hc v w
    simp only [realDomain] at h1 h2 ⊢
    rw [h1, h2]; ring

/-- The negative of a quadratic functional is quadratic. -/
lemma opt_isQuadratic_neg {D : ConvexDomain U} {f : U → ℝ} (hf : D.IsQuadratic f) :
    D.IsQuadratic (fun v => -f v) := by
  obtain ⟨F, ⟨hF1, hF2⟩, hfF⟩ := hf
  refine ⟨fun v w => -F v w, ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩,
    fun v => by simp only [hfF]⟩
  · have h1 := hF1 v₁ c hc v w
    simp only [realDomain] at h1 ⊢
    rw [h1]; ring
  · have h1 := hF2 v₂ c hc v w
    simp only [realDomain] at h1 ⊢
    rw [h1]; ring

/-- A difference of quadratic functionals is quadratic. -/
lemma opt_isQuadratic_sub {D : ConvexDomain U} {f g : U → ℝ} (hf : D.IsQuadratic f)
    (hg : D.IsQuadratic g) : D.IsQuadratic (fun v => f v - g v) := by
  simpa only [sub_eq_add_neg] using opt_isQuadratic_add hf (opt_isQuadratic_neg hg)

/-- `𝒥(P(v), Q(v))` is quadratic when `P, Q` are convex-linear. -/
lemma opt_isQuadratic_segArea {D : ConvexDomain U} {P Q : U → ℝ × ℝ}
    (hP : D.IsConvexLinear (vectorDomain (ℝ × ℝ)) P)
    (hQ : D.IsConvexLinear (vectorDomain (ℝ × ℝ)) Q) :
    D.IsQuadratic (fun v => segArea (P v) (Q v)) := by
  refine ⟨fun v w => segArea (P v) (Q w), ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩,
    fun v => rfl⟩
  · simp only [realDomain, segArea, hQ c hc, vectorDomain, cross_add_right, cross_smul_right]
    ring
  · simp only [realDomain, segArea, hP c hc, vectorDomain, cross_add_left, cross_smul_left]
    ring

end ConvexDomainAux

/-- The projection `(K, B, D) ↦ K` is convex-linear on `𝓛`. -/
lemma opt_projK_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.1) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

/-- The projection `(K, B, D) ↦ B` is convex-linear on `𝓛`. -/
lemma opt_projB_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.2.1) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

/-- The projection `(K, B, D) ↦ D` is convex-linear on `𝓛`. -/
lemma opt_projD_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.2.2) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

/-- `K ↦ 𝐱_K(t)` is convex-linear. -/
lemma opt_innerCorner_linear (t : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => innerCorner K.1 t) := by
  intro c hc K₁ K₂
  show innerCorner (convexBodyComb c K₁ K₂).1 t =
    (1 - c) • innerCorner K₁.1 t + c • innerCorner K₂.1 t
  rw [cvx_convexBodyComb_val hc, opt_innerCorner_comb K₁.2 K₂.2 hc]; rfl

/-- `K ↦ v_K⁺(a)` is convex-linear (Theorem 7.1.2). -/
lemma opt_vplus_linear (a : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vplus K.1 a) :=
  (theorem7_1_2_vertices a (a + 1)).1

/-- `K ↦ v_K⁻(a)` is convex-linear (Theorem 7.1.2). -/
lemma opt_vminus_linear (a : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vminus K.1 a) :=
  (theorem7_1_2_vertices a (a + 1)).2.1

/-! #### Regularity of the support function and of `𝐱_K`, `𝐲_K` -/

/-- The bilinear map `((α, β), (u, v)) ↦ α u + β v`. -/
noncomputable def opt_frameCLM : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- The value of `opt_frameCLM`. -/
lemma opt_frameCLM_apply (ab : ℝ × ℝ) (uv : (ℝ × ℝ) × (ℝ × ℝ)) :
    opt_frameCLM ab uv = ab.1 • uv.1 + ab.2 • uv.2 := by
  simp [opt_frameCLM]

/-- `t ↦ (h_K(t) + α) u_t + (h_K(t + π/2) + β) v_t` has bounded variation on intervals. -/
lemma opt_frame_bv {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (α β : ℝ) (a b : ℝ) :
    BoundedVariationOn
      (fun t => opt_frameCLM (supp K t + α, supp K (t + π / 2) + β) (uvec t, vvec t))
      (Icc a b) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_supp hK hne
  have h1 : LipschitzWith C (fun t => supp K t + α) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_add_right]; exact hC.dist_le_mul s t
  have h2 : LipschitzWith C (fun t => supp K (t + π / 2) + β) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_add_right]
      have := hC.dist_le_mul (s + π / 2) (t + π / 2)
      rwa [dist_add_right] at this
  have hF := boundedVariationOn_of_lipschitz (h1.prodMk h2) a b
  have hG := boundedVariationOn_of_lipschitz (lipschitz_uvec.prodMk lipschitz_vvec) a b
  exact hF.bilinear_comp hG opt_frameCLM

/-- `𝐱_K` in the form of `opt_frame_bv`. -/
lemma opt_innerCorner_eq_frame (K : Set (ℝ × ℝ)) (t : ℝ) :
    innerCorner K t =
      opt_frameCLM (supp K t + (-1), supp K (t + π / 2) + (-1)) (uvec t, vvec t) := by
  rw [proposition2_2_2_innerCorner, opt_frameCLM_apply]
  simp only [sub_eq_add_neg]

/-- `𝐲_K` in the form of `opt_frame_bv`. -/
lemma opt_outerCorner_eq_frame (K : Set (ℝ × ℝ)) (t : ℝ) :
    outerCorner K t = opt_frameCLM (supp K t + 0, supp K (t + π / 2) + 0) (uvec t, vvec t) := by
  rw [proposition2_2_2_outerCorner, opt_frameCLM_apply]
  simp only [add_zero]

/-- The inner corner `𝐱_K` of a convex body is continuous. -/
lemma opt_innerCorner_continuous {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (innerCorner K) := by
  have hs := continuous_supp hK.2.1
  have : innerCorner K = fun t => (supp K t - 1) • uvec t + (supp K (t + π / 2) - 1) • vvec t :=
    funext (proposition2_2_2_innerCorner K)
  rw [this]
  unfold uvec vvec
  fun_prop

/-- The outer corner `𝐲_K` of a convex body is continuous. -/
lemma opt_outerCorner_continuous {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (outerCorner K) := by
  have hs := continuous_supp hK.2.1
  have : outerCorner K = fun t => supp K t • uvec t + supp K (t + π / 2) • vvec t :=
    funext (proposition2_2_2_outerCorner K)
  rw [this]
  unfold uvec vvec
  fun_prop

/-- `𝐱_K ∈ C^BV[a, b]`. -/
lemma opt_innerCorner_cbv {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IsCBV (innerCorner K) a b := by
  refine ⟨(opt_innerCorner_continuous hK).continuousOn, ?_⟩
  have h := opt_frame_bv hK.2.1 hK.1 (-1) (-1) a b
  have e : innerCorner K = fun t =>
      opt_frameCLM (supp K t + (-1), supp K (t + π / 2) + (-1)) (uvec t, vvec t) :=
    funext (opt_innerCorner_eq_frame K)
  rwa [e]

/-- `𝐲_K ∈ C^BV[a, b]`. -/
lemma opt_outerCorner_cbv {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IsCBV (outerCorner K) a b := by
  refine ⟨(opt_outerCorner_continuous hK).continuousOn, ?_⟩
  have h := opt_frame_bv hK.2.1 hK.1 0 0 a b
  have e : outerCorner K = fun t =>
      opt_frameCLM (supp K t + 0, supp K (t + π / 2) + 0) (uvec t, vvec t) :=
    funext (opt_outerCorner_eq_frame K)
  rwa [e]

/-- The inner corner `𝐱_K|_{[a, b]}` as an element of `C^BV[a, b]`. -/
noncomputable def opt_innerCBV (a b : ℝ) (K : ConvexBodySet) : CBV a b :=
  ⟨innerCorner K.1, opt_innerCorner_cbv K.2 a b⟩

/-- `K ↦ 𝐱_K|_{[a, b]}` is convex-linear. -/
lemma opt_innerCBV_linear (a b : ℝ) :
    convexBodyDomain.IsConvexLinear (cbvDomain a b) (opt_innerCBV a b) := by
  intro c hc K₁ K₂
  apply Subtype.ext
  show innerCorner (convexBodyComb c K₁ K₂).1 = (1 - c) • innerCorner K₁.1 + c • innerCorner K₂.1
  rw [cvx_convexBodyComb_val hc, opt_innerCorner_comb K₁.2 K₂.2 hc]

/-! #### Areas of plane regions (for Lemma 8.2.3) -/

/-- The area of the region `{a < y < b, α₁ + β₁ y < x < α₂ + β₂ y}`. -/
lemma opt_volume_hregion {a b α₁ β₁ α₂ β₂ : ℝ} (hab : a ≤ b)
    (hle : ∀ y ∈ Ioo a b, α₁ + β₁ * y ≤ α₂ + β₂ * y) :
    MeasureTheory.volume
        {p : ℝ × ℝ | a < p.2 ∧ p.2 < b ∧ α₁ + β₁ * p.2 < p.1 ∧ p.1 < α₂ + β₂ * p.2} =
      ENNReal.ofReal ((α₂ - α₁) * (b - a) + (β₂ - β₁) * (b ^ 2 - a ^ 2) / 2) := by
  have hset : {p : ℝ × ℝ | a < p.2 ∧ p.2 < b ∧ α₁ + β₁ * p.2 < p.1 ∧ p.1 < α₂ + β₂ * p.2} =
      Prod.swap ⁻¹' regionBetween (fun y => α₁ + β₁ * y) (fun y => α₂ + β₂ * y) (Ioo a b) := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, regionBetween, Prod.fst_swap, Prod.snd_swap, mem_Ioo]
    tauto
  have hf : Continuous fun y : ℝ => α₁ + β₁ * y := by fun_prop
  have hg : Continuous fun y : ℝ => α₂ + β₂ * y := by fun_prop
  rw [hset, MeasureTheory.Measure.volume_eq_prod,
    (MeasureTheory.Measure.measurePreserving_swap).measure_preimage
      (measurableSet_regionBetween hf.measurable hg.measurable measurableSet_Ioo).nullMeasurableSet,
    volume_regionBetween_eq_integral (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (hg.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo hle,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  congr 1
  have : (fun y => α₂ + β₂ * y) - (fun y => α₁ + β₁ * y) = fun y => (α₂ - α₁) + (β₂ - β₁) * y := by
    funext y; simp only [Pi.sub_apply]; ring
  rw [this, ang_integral_affine]
  ring

/-- The area of the region below a graph-like curve `t ↦ (X t, Y t)`, `t ∈ (a, b)`, with `X`
strictly decreasing, down to the horizontal line `y = -H`. -/
lemma opt_volume_under_curve {X Y X' : ℝ → ℝ} {a b H : ℝ} (hab : a < b)
    (hX : Continuous X) (hY : Continuous Y)
    (hXd : ∀ t ∈ Icc a b, HasDerivAt X (X' t) t) (hX'c : ContinuousOn X' (Icc a b))
    (hanti : StrictAntiOn X (Icc a b)) (hX'neg : ∀ t ∈ Icc a b, X' t ≤ 0)
    (hH : ∀ t ∈ Icc a b, 0 < Y t + H) :
    MeasureTheory.volume ((fun q : ℝ × ℝ => (X q.1, Y q.1 - q.2)) ''
        {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < Y q.1 + H}) =
      ENNReal.ofReal (∫ t in a..b, -X' t * (Y t + H)) := by
  -- The region is the image of `S = {(t, s) | t ∈ (a, b), 0 < s < Y(t) + H}` under the injective
  -- map `Φ(t, s) = (X(t), Y(t) - s)`; its vertical slice over `X(t)` is `(-H, Y(t))`.
  set S := {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < Y q.1 + H} with hSdef
  set Φ := fun q : ℝ × ℝ => (X q.1, Y q.1 - q.2) with hΦdef
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {q : ℝ × ℝ | q.1 ∈ Ioo a b} :=
      measurableSet_Ioo.preimage measurable_fst
    have h2 : MeasurableSet {q : ℝ × ℝ | 0 < q.2} :=
      measurableSet_lt measurable_const measurable_snd
    have h3 : MeasurableSet {q : ℝ × ℝ | q.2 < Y q.1 + H} :=
      measurableSet_lt measurable_snd ((hY.measurable.comp measurable_fst).add_const H)
    exact h1.inter (h2.inter h3)
  have hinj : InjOn Φ S := by
    rintro ⟨t, s⟩ ⟨ht, -⟩ ⟨t', s'⟩ ⟨ht', -⟩ h
    simp only [hΦdef, Prod.mk.injEq] at h
    have htt : t = t' := hanti.injOn ⟨ht.1.le, ht.2.le⟩ ⟨ht'.1.le, ht'.2.le⟩ h.1
    subst htt
    simp only [Prod.mk.injEq, true_and]
    linarith [h.2]
  have hG : MeasurableSet (Φ '' S) :=
    hSm.image_of_continuousOn_injOn (by rw [hΦdef]; fun_prop) hinj
  -- Fubini over vertical slices, then the change of variables `x = X(t)`
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply hG]
  set g := fun x : ℝ => MeasureTheory.volume (Prod.mk x ⁻¹' (Φ '' S)) with hgdef
  have hsupp : Function.support g ⊆ X '' Ioo a b := by
    intro x hx
    by_contra hxn
    apply hx
    simp only [hgdef]
    convert MeasureTheory.measure_empty (μ := MeasureTheory.volume)
    ext y
    simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
    rintro ⟨t, s⟩ ⟨ht, -⟩ h
    simp only [hΦdef, Prod.mk.injEq] at h
    exact hxn ⟨t, ht, h.1⟩
  have hval : ∀ t ∈ Ioo a b, g (X t) = ENNReal.ofReal (Y t + H) := by
    intro t ht
    have e : Prod.mk (X t) ⁻¹' (Φ '' S) = Ioo (-H) (Y t) := by
      ext y
      simp only [mem_preimage, mem_image, mem_Ioo]
      constructor
      · rintro ⟨⟨t', s'⟩, ⟨ht', hs1, hs2⟩, h⟩
        simp only [hΦdef, Prod.mk.injEq] at h
        have htt : t' = t := hanti.injOn ⟨ht'.1.le, ht'.2.le⟩ ⟨ht.1.le, ht.2.le⟩ h.1
        subst htt
        constructor <;> linarith [h.2]
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨t, Y t - y⟩, ⟨ht, by simp only; linarith, by simp only; linarith⟩,
          by simp [hΦdef]⟩
    simp only [hgdef, e, Real.volume_Ioo]
    congr 1
    ring
  rw [← MeasureTheory.setLIntegral_eq_of_support_subset hsupp,
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun t ht => (hXd t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt)
      (hanti.injOn.mono Ioo_subset_Icc_self),
    MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
      (fun t ht => by rw [hval t ht])]
  have hcont : ContinuousOn (fun t => -X' t * (Y t + H)) (Icc a b) :=
    (hX'c.neg).mul (hY.continuousOn.add continuousOn_const)
  rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [abs_of_nonpos (hX'neg t ⟨ht.1.le, ht.2.le⟩), ← ENNReal.ofReal_mul
      (neg_nonneg.mpr (hX'neg t ⟨ht.1.le, ht.2.le⟩))]
  · exact (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    exact Filter.Eventually.of_forall fun t ht => mul_nonneg
      (neg_nonneg.mpr (hX'neg t ⟨ht.1.le, ht.2.le⟩)) (hH t ⟨ht.1.le, ht.2.le⟩).le

/-- The right tail `𝐛_B = 𝐮_B^{π + φ^R, 3π/2}` (Definition 8.2.1). -/
def tailB (φ : ℝ) (B : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := convexCurve B (π + φ) (3 * π / 2)
/-- Its starting point `X_B = v_B⁺(π + φ^R)`. -/
noncomputable def xB (φ : ℝ) (B : Set (ℝ × ℝ)) : ℝ × ℝ := vplus B (π + φ)
/-- Its ending point `W_B = v_B⁻(3π/2)`. -/
noncomputable def wB (B : Set (ℝ × ℝ)) : ℝ × ℝ := vminus B (3 * π / 2)
/-- The left tail `𝐝_D = 𝐮_D^{3π/2, 3π/2 + φ^L}` (Definition 8.2.1). -/
def tailD (φ : ℝ) (D : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  convexCurve D (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
/-- Its starting point `Z_D = v_D⁺(3π/2)`. -/
noncomputable def zD (D : Set (ℝ × ℝ)) : ℝ × ℝ := vplus D (3 * π / 2)
/-- Its ending point `Y_D = v_D⁻(3π/2 + φ^L)`. -/
noncomputable def yD (φ : ℝ) (D : Set (ℝ × ℝ)) : ℝ × ℝ := vminus D (3 * π / 2 + (π / 2 - φ))

/-- The upper bound
`𝒬(K, B, D) = |K| + 𝒥(𝐝_D) + 𝒥(Y_D, 𝐱_K^L) - 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^R, X_B) + 𝒥(𝐛_B)`
(Definition 8.2.2, `def:upper-bound-q`). -/
noncomputable def upperQ (φ : ℝ) (K B D : Set (ℝ × ℝ)) : ℝ :=
  area K + convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) + segArea (yD φ D) (xLeft φ K) -
    curveArea (innerCorner K) φ (π / 2 - φ) + segArea (xRight φ K) (xB φ B) +
    convexCurveArea B (π + φ) (3 * π / 2)

/-- `𝒬` as a function on the convex domain `𝓛`. -/
noncomputable def upperQL (φ : ℝ) (x : LTriple φ) : ℝ := upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

/-- **Proposition 8.2.1** (`pro:upper-bound-q-quadratic`). `𝒬` is a quadratic functional on `𝓛`. -/
theorem proposition8_2_1 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (lDomain φ).IsQuadratic (upperQL φ) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have t1 : (lDomain φ).IsQuadratic (fun x => area x.1.1.1) :=
    opt_isQuadratic_comp (opt_projK_linear φ) theorem7_1_3_quadratic
  have t2 : (lDomain φ).IsQuadratic
      (fun x => convexCurveArea x.1.2.2.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ))) :=
    opt_isQuadratic_comp (opt_projD_linear φ) (theorem7_3_2_quadratic)
  have t3 : (lDomain φ).IsQuadratic (fun x => segArea (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : LTriple φ => x.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (opt_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun x : LTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (opt_projK_linear φ) (opt_innerCorner_linear _))
  have t4 : (lDomain φ).IsQuadratic
      (fun x => curveArea (innerCorner x.1.1.1) φ (π / 2 - φ)) :=
    opt_isQuadratic_comp
      (opt_isConvexLinear_comp (opt_projK_linear φ) (opt_innerCBV_linear φ (π / 2 - φ)))
      (proposition7_2_2 (by linarith))
  have t5 : (lDomain φ).IsQuadratic (fun x => segArea (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : LTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (opt_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun x : LTriple φ => x.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (opt_projB_linear φ) (opt_vplus_linear _))
  have t6 : (lDomain φ).IsQuadratic (fun x => convexCurveArea x.1.2.1.1 (π + φ) (3 * π / 2)) :=
    opt_isQuadratic_comp (opt_projB_linear φ) (theorem7_3_2_quadratic)
  exact opt_isQuadratic_add (opt_isQuadratic_add (opt_isQuadratic_sub
    (opt_isQuadratic_add (opt_isQuadratic_add t1 t2) t3) t4) t5) t6

/-! #### The tails and the lines they end on -/

/-- If `h_C(3π/2) = 0`, the vertex `v_C⁺(3π/2)` lies on the `x`-axis. -/
lemma opt_snd_vplus_three_pi_div_two {C : Set (ℝ × ℝ)} (h : supp C (3 * π / 2) = 0) :
    (vplus C (3 * π / 2)).2 = 0 := by
  have e := dot_vplus_uvec C (3 * π / 2)
  rw [dot_uvec_three_pi_div_two, h] at e
  linarith

/-- If `h_C(3π/2) = 0`, the vertex `v_C⁻(3π/2)` lies on the `x`-axis. -/
lemma opt_snd_vminus_three_pi_div_two {C : Set (ℝ × ℝ)} (h : supp C (3 * π / 2) = 0) :
    (vminus C (3 * π / 2)).2 = 0 := by
  have e := dot_vminus_uvec C (3 * π / 2)
  rw [dot_uvec_three_pi_div_two, h] at e
  linarith

/-- The corner `v_B(π + φ, 3π/2)` is `W_K^R` when `l_B(π + φ) = b_K(φ)` and
`l_B(3π/2) = l(π/2, 0)`. -/
lemma opt_vint_right_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) {K B : Set (ℝ × ℝ)}
    (hBa : supp B (π + φ) = 1 - supp K φ) (hB3 : supp B (3 * π / 2) = 0) :
    vint B (π + φ) (3 * π / 2) = wRight φ K := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], hφ.2⟩
  have e := sin_sq_add_cos_sq φ
  rw [opt_wRight_eq]
  simp only [vint]
  rw [show 3 * π / 2 - (π + φ) = π / 2 - φ by ring, cos_pi_div_two_sub, sin_pi_div_two_sub,
    hB3, hBa, show π + φ = φ + π by ring, uvec_add_pi, vvec_add_pi]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_neg, uvec_fst, vvec_fst, smul_eq_mul]
    field_simp
    linear_combination (supp K φ - 1) * e
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_neg, uvec_snd, vvec_snd, smul_eq_mul]
    field_simp
    ring

/-- The corner `v_D(3π/2, 3π/2 + φ^L)` is `Z_K^L` when `l_D(3π/2) = l(π/2, 0)` and
`l_D(3π/2 + φ^L) = d_K(φ^L)`. -/
lemma opt_vint_left_eq {φ : ℝ} {K D : Set (ℝ × ℝ)} (hD3 : supp D (3 * π / 2) = 0)
    (hDb : supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ)) :
    vint D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) = zLeft φ K := by
  rw [opt_zLeft_eq]
  simp only [vint, hD3, hDb, show 3 * π / 2 + (π / 2 - φ) - 3 * π / 2 = π / 2 - φ by ring,
    sin_pi_div_two_sub, vvec_three_pi_div_two, zero_smul, zero_add, zero_mul, sub_zero]
  ext <;> simp

/-- `X_B`, `W_K^R` and `𝐱_K^R` lie on the line `b_K^R = l(φ, h_K(φ) - 1)` when
`l_B(π + φ) = b_K^R`. -/
lemma opt_right_mem_line {φ : ℝ} (hc : cos φ ≠ 0) {K B : Set (ℝ × ℝ)}
    (hBa : supp B (π + φ) = 1 - supp K φ) :
    xB φ B ∈ line φ (supp K φ - 1) ∧ wRight φ K ∈ line φ (supp K φ - 1) ∧
      xRight φ K ∈ line φ (supp K φ - 1) := by
  refine ⟨?_, ?_, (cn_innerCorner_dot K φ).1⟩
  · have h := dot_vplus_uvec B (π + φ)
    rw [show uvec (π + φ) = -uvec φ by rw [add_comm, uvec_add_pi], dot_neg_right, hBa] at h
    show dot (vplus B (π + φ)) (uvec φ) = supp K φ - 1
    linarith
  · show dot (wRight φ K) (uvec φ) = supp K φ - 1
    simp only [opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp

/-- `Y_D`, `Z_K^L` and `𝐱_K^L` lie on the line `d_K^L = l(π - φ, h_K(π - φ) - 1)` when
`l_D(3π/2 + φ^L) = d_K^L`. -/
lemma opt_left_mem_line {φ : ℝ} (hc : cos φ ≠ 0) {K D : Set (ℝ × ℝ)}
    (hDb : supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ)) :
    yD φ D ∈ line (π - φ) (supp K (π - φ) - 1) ∧ zLeft φ K ∈ line (π - φ) (supp K (π - φ) - 1) ∧
      xLeft φ K ∈ line (π - φ) (supp K (π - φ) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := dot_vminus_uvec D (3 * π / 2 + (π / 2 - φ))
    rw [show uvec (3 * π / 2 + (π / 2 - φ)) = -uvec (π - φ) by
      rw [show 3 * π / 2 + (π / 2 - φ) = π - φ + π by ring, uvec_add_pi], dot_neg_right,
      hDb] at h
    show dot (vminus D (3 * π / 2 + (π / 2 - φ))) (uvec (π - φ)) = supp K (π - φ) - 1
    linarith
  · show dot (zLeft φ K) (uvec (π - φ)) = supp K (π - φ) - 1
    simp only [opt_zLeft_eq, dot, uvec, cos_pi_sub, zero_mul, add_zero]
    field_simp
    ring
  · have h := (cn_innerCorner_dot K (π / 2 - φ)).2
    rw [show π / 2 - φ + π / 2 = π - φ by ring] at h
    exact h

/-- The area cut off by a tail `𝐮_C^{a,b}` (Lemma 7.3.5): if `C ⊆ K` with `K` convex,
`v_C(a, b) ∈ K`, and every point of `K \ C` in `H_C(a) ∩ H_C(b)` lies in a set `S` of finite
measure, then `𝒥(v_C⁺(a), v_C(a, b)) + 𝒥(v_C(a, b), v_C⁻(b)) - 𝒥(𝐮_C^{a,b}) ≤ |S|`. (When the
tail is a single point the left side is `0`.) -/
lemma opt_tail_area_le {C K S : Set (ℝ × ℝ)} (hC : IsConvexBody C) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) (hCK : C ⊆ K) (hK : Convex ℝ K) (hv : vint C a b ∈ K)
    (hS : MeasureTheory.volume S ≠ ⊤)
    (hsub : ∀ p ∈ K, p ∉ C → p ∈ suppHalf C a ∩ suppHalf C b → p ∈ S) :
    segArea (vplus C a) (vint C a b) + segArea (vint C a b) (vminus C b) -
      convexCurveArea C a b ≤ area S := by
  by_cases hdeg : vplus C a = vminus C b
  · -- the tail is the single point `v_C⁺(a) = v_C(a, b) = v_C⁻(b)`, of curve area `0`
    obtain ⟨hv', hcurve⟩ := lemma7_3_1_degenerate hC hab hb hdeg
    obtain ⟨γ, -, himg, -, -, -, harea⟩ := theorem7_3_2 hC hab hb
    have hcca : convexCurveArea C a b = 0 := by
      rw [← harea]
      refine curveArea_const zero_le_one (P := vplus C a) fun t ht => ?_
      have : γ t ∈ convexCurve C a b := himg ▸ mem_image_of_mem γ ht
      rwa [hcurve] at this
    rw [hcca, hv', ← hdeg, segArea_self, add_zero, sub_zero]
    exact ENNReal.toReal_nonneg
  · -- the region of Lemma 7.3.5 lies in the triangle `v_C⁺(a), v_C(a, b), v_C⁻(b)` (so in `K`),
    -- outside `C`, and inside `H_C(a) ∩ H_C(b)`
    obtain ⟨hsubH, -, harea⟩ := lemma7_3_5 hC hab hb hdeg
    rw [← harea]
    refine ENNReal.toReal_mono hS (MeasureTheory.measure_mono fun p hp =>
      hsub p ?_ ?_ (interior_subset (hsubH hp)))
    · refine convexHull_min ?_ hK (interior_subset hp.1)
      intro q hq
      simp only [mem_insert_iff, mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact hCK (vplus_mem_edge hC _).1
      · exact hv
      · exact hCK (vminus_mem_edge hC _).1
    · exact fun hpC => hp.2 (mem_iInter₂.mpr fun t _ => dot_le_supp hC.2.1 hpC t)

/-- **Lemma 8.2.2** (`lem:cap-left-right-tail`). For `K ∈ 𝒦^i`, `B = B_K`, `D = D_K`:
`|𝒩(K) ∩ H̆_K^R| ≥ 𝒥(X_B, W_K^R) - 𝒥(𝐛_B)` and `|𝒩(K) ∩ H̆_K^L| ≥ 𝒥(Z_K^L, Y_D) - 𝒥(𝐝_D)`. -/
theorem lemma8_2_2 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    segArea (xB φ (rightBody φ K)) (wRight φ K) -
          convexCurveArea (rightBody φ K) (π + φ) (3 * π / 2) ≤
        area (niche K (π / 2) ∩ hRight φ K) ∧
      segArea (zLeft φ K) (yD φ (leftBody φ K)) -
          convexCurveArea (leftBody φ K) (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) ≤
        area (niche K (π / 2) ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hcap := hK.1
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  have hL := theorem8_1_8 hφ hK
  obtain ⟨hB3, hD3, hBa, hDb⟩ := opt_inL_supp hL
  obtain ⟨-, hBcb, hDcb, hBK, hDK, -⟩ := hL
  have hfin : ∀ S ⊆ niche K (π / 2), MeasureTheory.volume S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top (nef_niche_isBounded hcap).measure_lt_top.ne
      (MeasureTheory.measure_mono hS)
  constructor
  · -- The right tail runs from `X_B` to `v_B⁻(3π/2)` on the `x`-axis, with corner
    -- `v_B(π + φ, 3π/2) = W_K^R`. A point of `K \ B_K` between the lines `b_K^R` and `l(π/2, 0)`
    -- leaves some `H_K^b(s)`, `s ∈ (φ, π/2)`, so lies in the wedge `T_K(s)` (Lemma 8.1.6).
    have hvint := opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
    have hsub : ∀ p ∈ K, p ∉ rightBody φ K →
        p ∈ suppHalf (rightBody φ K) (π + φ) ∩ suppHalf (rightBody φ K) (3 * π / 2) →
        p ∈ niche K (π / 2) ∩ hRight φ K := by
      intro p hpK hpB ⟨hpR', hp2⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hBa] at hpR'
      rw [show π + φ = φ + π by ring, dot_uvec_add_pi] at hpR'
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hB3, dot_uvec_three_pi_div_two] at hp2
      have hpR : p ∈ hRight φ K := by
        simp only [hRight, halfB, halfPlus, mem_ofPred_eq]; linarith
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc φ (π / 2), p ∉ halfB K s := by
        by_contra hcon
        push Not at hcon
        exact hpB ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hsφ : φ < s := lt_of_le_of_ne hs.1 (by rintro rfl; exact hps hpR)
      have hsπ : s < π / 2 := lt_of_le_of_ne hs.2 (by
        rintro rfl
        apply hps
        simp only [halfB, halfPlus, mem_ofPred_eq, hcap.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hpw : p ∈ wedge K (π / 2) s := by
        have : p ∈ (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K s := by
          refine ⟨⟨hpR, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (lemma8_1_6_right hφ' hK ⟨hsφ, hsπ.le⟩).2.2] at this
        exact this.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨by linarith, hsπ⟩, hpw.2⟩⟩, hpR⟩
    have h := opt_tail_area_le hBcb (by linarith) (by linarith) hBK hcap.2.1.2.2
      (by rw [hvint]; exact (lemma8_1_5 hφ hK).1.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero rfl (opt_snd_vminus_three_pi_div_two hB3), add_zero] at h
  · -- The left tail runs from `v_D⁺(3π/2)` on the `x`-axis to `Y_D`, with corner
    -- `v_D(3π/2, 3π/2 + φ^L) = Z_K^L`; the mirror image of the right case.
    have hvint := opt_vint_left_eq hD3 hDb
    have hsub : ∀ p ∈ K, p ∉ leftBody φ K →
        p ∈ suppHalf (leftBody φ K) (3 * π / 2) ∩
          suppHalf (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) →
        p ∈ niche K (π / 2) ∩ hLeft φ K := by
      intro p hpK hpD ⟨hp2, hpL'⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hD3, dot_uvec_three_pi_div_two] at hp2
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hDb] at hpL'
      rw [show 3 * π / 2 + (π / 2 - φ) = π - φ + π by ring, dot_uvec_add_pi] at hpL'
      have hpL : p ∈ hLeft φ K := by
        simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, show π / 2 - φ + π / 2 = π - φ by ring]
        linarith
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc 0 (π / 2 - φ), p ∉ halfD K s := by
        by_contra hcon
        push Not at hcon
        exact hpD ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by
        rintro rfl
        apply hps
        simp only [halfD, halfPlus, mem_ofPred_eq, zero_add, hcap.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hsψ : s < π / 2 - φ := lt_of_le_of_ne hs.2 (by rintro rfl; exact hps hpL)
      have hpw : p ∈ wedge K (π / 2) s := by
        have : p ∈ (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K s := by
          refine ⟨⟨hpL, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (lemma8_1_6_left hφ' hK ⟨hs0.le, hsψ⟩).2.2] at this
        exact this.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨hs0, by linarith⟩, hpw.2⟩⟩, hpL⟩
    have h := opt_tail_area_le hDcb (by linarith) (by linarith) hDK hcap.2.1.2.2
      (by rw [hvint]; exact (lemma8_1_5 hφ hK).2.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3) (by rw [opt_zLeft_eq]),
      zero_add] at h

/-! #### Auxiliary lemmas for Lemma 8.2.3 -/

/-- `p ∉ H̆_K^R` iff `p` is left of the line `b_K^R`: `p.1 < w - p.2 tan φ`, with `w` the
`x`-coordinate of `W_K^R`. -/
lemma opt_notMem_hRight_iff {φ : ℝ} (hc : 0 < cos φ) (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    p ∉ hRight φ K ↔ p.1 < (supp K φ - 1) / cos φ - p.2 * (sin φ / cos φ) := by
  simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
  rw [show (supp K φ - 1) / cos φ - p.2 * (sin φ / cos φ) =
      (supp K φ - 1 - p.2 * sin φ) / cos φ by field_simp, lt_div_iff₀ hc]
  constructor <;> intro h <;> linarith

/-- `p ∉ H̆_K^L` iff `p` is right of the line `d_K^L`: `z + p.2 tan φ < p.1`, with `z` the
`x`-coordinate of `Z_K^L`. -/
lemma opt_notMem_hLeft_iff {φ : ℝ} (hc : 0 < cos φ) (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    p ∉ hLeft φ K ↔ (1 - supp K (π - φ)) / cos φ + p.2 * (sin φ / cos φ) < p.1 := by
  simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, dot, uvec,
    show π / 2 - φ + π / 2 = π - φ by ring, cos_pi_sub, sin_pi_sub]
  rw [show (1 - supp K (π - φ)) / cos φ + p.2 * (sin φ / cos φ) =
      (1 - supp K (π - φ) + p.2 * sin φ) / cos φ by field_simp, div_lt_iff₀ hc]
  constructor <;> intro h <;> linarith

/-- The points vertically below the core curve lie in `Q_K⁻(t)`, outside `H̆_K^R` and `H̆_K^L`. -/
lemma opt_l823_curve_pt {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {t s : ℝ} (ht : t ∈ Ioo φ (π / 2 - φ)) (hs : 0 < s) :
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hRight φ K ∧
      ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hLeft φ K ∧
      ((innerCorner K t).1, (innerCorner K t).2 - s) ∈ qMinus K t := by
  have hpi := pi_pos
  have ht' : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1]⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht'.1 (by linarith [ht'.2])
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht'.1], ht'.2⟩
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have e1 := opt_innerCorner_lt_right hφ hK (t := t) ⟨ht.1, by linarith [ht.2, hφ.1]⟩
  have e2 := opt_innerCorner_lt_left hφ hK (t := t) ⟨ht'.1.le, ht.2⟩
  have e3 := (cn_innerCorner_dot K t).1
  have e4 := opt_innerCorner_dot_v K t
  simp only [dot, uvec, vvec] at e1 e2 e3 e4
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at e2
  refine ⟨?_, ?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos hs hs0]
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two, dot, vvec,
      sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos hs hs0]
  · rw [proposition2_2_2_qMinus]
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two]
    simp only [dot, uvec, vvec]
    constructor <;> nlinarith [mul_pos hs hst, mul_pos hs hct]

/-- The points right of and below `𝐱_K^R`, outside `H̆_K^R`, lie in `Q_K⁻(φ)` and outside
`H̆_K^L`. -/
lemma opt_l823_tri1_pt {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {p : ℝ × ℝ} (h1 : (innerCorner K φ).1 < p.1) (h2 : p.2 < (innerCorner K φ).2)
    (h3 : p ∉ hRight φ K) : p ∉ hLeft φ K ∧ p ∈ qMinus K φ := by
  have hpi := pi_pos
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc0 : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e2 := opt_innerCorner_lt_left hφ hK (t := φ) ⟨hφ.1.le, by linarith [hφ.2]⟩
  have e4 := opt_innerCorner_dot_v K φ
  simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e2 e4
  refine ⟨?_, ?_⟩
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two, dot, vvec,
      sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hc0, mul_pos (sub_pos.mpr h2) hs0]
  · rw [proposition2_2_2_qMinus]
    simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two]
    refine ⟨h3, ?_⟩
    simp only [dot, vvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hs0, mul_pos (sub_pos.mpr h2) hc0]

/-- The points left of and below `𝐱_K^L`, outside `H̆_K^L`, lie in `Q_K⁻(φ^L)` and outside
`H̆_K^R`. -/
lemma opt_l823_tri2_pt {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {p : ℝ × ℝ} (h1 : p.1 < (innerCorner K (π / 2 - φ)).1)
    (h2 : p.2 < (innerCorner K (π / 2 - φ)).2) (h3 : p ∉ hLeft φ K) :
    p ∉ hRight φ K ∧ p ∈ qMinus K (π / 2 - φ) := by
  have hpi := pi_pos
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc0 : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e1 := opt_innerCorner_lt_right hφ hK (t := π / 2 - φ)
    ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  have e3 := (cn_innerCorner_dot K (π / 2 - φ)).1
  simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e1 e3
  refine ⟨?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hc0, mul_pos (sub_pos.mpr h2) hs0]
  · rw [proposition2_2_2_qMinus]
    simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq]
    refine ⟨?_, h3⟩
    simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hs0, mul_pos (sub_pos.mpr h2) hc0]

/-- Under the injectivity condition, `𝐱_K'` is continuous on `[a, b] ⊆ (0, π/2)`. -/
lemma opt_inj_deriv_continuousOn {K : Set (ℝ × ℝ)} (h2 : InjCond2 K) {a b : ℝ} (ha : 0 < a)
    (hb : b < π / 2) : ContinuousOn (deriv (innerCorner K)) (Icc a b) := by
  have hpi := pi_pos
  have hcw := h2.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith : (0 : ℝ) < π / 2)) le_rfl
  refine (hcw.mono (Icc_subset_Icc ha.le hb.le)).congr ?_
  intro t ht
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))).symm

/-- `𝒥(𝐱_K|_{[a,b]})` for a cap with the injectivity condition, after an integration by parts. -/
lemma opt_curveArea_inner_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (h2 : InjCond2 K) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < π / 2) :
    curveArea (innerCorner K) a b =
      ((innerCorner K b).1 * (innerCorner K b).2 - (innerCorner K a).1 * (innerCorner K a).2 -
        2 * ∫ t in a..b, (deriv (innerCorner K) t).1 * (innerCorner K t).2) / 2 := by
  set x := innerCorner K with hxdef
  have hd : ∀ t ∈ Icc a b, HasDerivAt x (deriv x t) t := fun t ht =>
    opt_inj_hasDerivAt h2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdc := opt_inj_deriv_continuousOn h2 ha hb
  have hxc : Continuous x := opt_innerCorner_continuous hK
  have hX'i : IntervalIntegrable (fun t => (deriv x t).1) MeasureTheory.volume a b :=
    (continuous_fst.comp_continuousOn hdc).intervalIntegrable_of_Icc hab.le
  have hY'i : IntervalIntegrable (fun t => (deriv x t).2) MeasureTheory.volume a b :=
    (continuous_snd.comp_continuousOn hdc).intervalIntegrable_of_Icc hab.le
  have hmem : ∀ t ∈ Ioo (min a b) (max a b), t ∈ Icc a b := by
    intro t ht
    rw [min_eq_left hab.le, max_eq_right hab.le] at ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => (x t).1) (v := fun t => (x t).2) (u' := fun t => (deriv x t).1)
    (v' := fun t => (deriv x t).2) (continuous_fst.comp hxc).continuousOn
    (continuous_snd.comp hxc).continuousOn (fun t ht => hasDerivAt_fst (hd t (hmem t ht)))
    (fun t ht => hasDerivAt_snd (hd t (hmem t ht))) hX'i hY'i
  rw [curveArea_eq_integral hab.le (h2.mono (Icc_subset_Icc ha.le hb.le))]
  have e : ∫ t in a..b, cross (x t) (derivWithin x (Icc a b) t) =
      (∫ t in a..b, (x t).1 * (deriv x t).2) - ∫ t in a..b, (deriv x t).1 * (x t).2 := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab.le] at ht
      simp only [cross]
      rw [(hd t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
      ring
    · exact ((continuous_fst.comp hxc).continuousOn.mul
        (continuous_snd.comp_continuousOn hdc)).intervalIntegrable_of_Icc hab.le
    · exact ((continuous_fst.comp_continuousOn hdc).mul
        (continuous_snd.comp hxc).continuousOn).intervalIntegrable_of_Icc hab.le
  rw [e, hIBP]
  ring

/-- The area under the core curve: `∫_a^b -X'(Y + H) = -∫_a^b X' Y - H (X(b) - X(a))`. -/
lemma opt_integral_under_inner {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (h2 : InjCond2 K) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < π / 2) (H : ℝ) :
    ∫ t in a..b, -(deriv (innerCorner K) t).1 * ((innerCorner K t).2 + H) =
      -(∫ t in a..b, (deriv (innerCorner K) t).1 * (innerCorner K t).2) -
        H * ((innerCorner K b).1 - (innerCorner K a).1) := by
  set x := innerCorner K with hxdef
  have hd : ∀ t ∈ Icc a b, HasDerivAt x (deriv x t) t := fun t ht =>
    opt_inj_hasDerivAt h2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdc := opt_inj_deriv_continuousOn h2 ha hb
  have hxc : Continuous x := opt_innerCorner_continuous hK
  have hX'i : IntervalIntegrable (fun t => (deriv x t).1) MeasureTheory.volume a b :=
    (continuous_fst.comp_continuousOn hdc).intervalIntegrable_of_Icc hab.le
  have hFTC : ∫ t in a..b, (deriv x t).1 = (x b).1 - (x a).1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_fst (hd t (by rwa [uIcc_of_le hab.le] at ht))) hX'i
  have e : (fun t => -(deriv x t).1 * ((x t).2 + H)) =
      fun t => -((deriv x t).1 * (x t).2) - H * (deriv x t).1 := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, hFTC]
  · exact (((continuous_fst.comp_continuousOn hdc).mul
      (continuous_snd.comp hxc).continuousOn).intervalIntegrable_of_Icc hab.le).neg
  · exact hX'i.const_mul H

/-- Under the injectivity condition, the `x`-coordinate of `𝐱_K` decreases strictly. -/
lemma opt_inj_X'_neg {K : Set (ℝ × ℝ)} (h3 : InjCond3 K) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    (deriv (innerCorner K) t).1 < 0 := by
  obtain ⟨hu, hv⟩ := h3 t ht
  have e := dot_uvec_eq_cos_add_sin (deriv (innerCorner K) t) 0 t
  rw [uvec_zero] at e
  simp only [dot_mk, mul_one, mul_zero, add_zero, zero_sub, cos_neg, sin_neg] at e
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  rw [e]
  nlinarith [mul_pos hct (neg_pos.mpr hu), mul_pos hst hv]

/-- `Z_K^L` is to the left of `W_K^R` (this uses `|K| ≥ 2.2`). -/
lemma opt_l823_wz {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    (1 - supp K (π - φ)) / cos φ < (supp K φ - 1) / cos φ := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have harea := opt_area_mul_cos_le hK.1 hc hs0.le
  have : 2 < supp K φ + supp K (π - φ) := by nlinarith [mul_le_mul_of_nonneg_right hK.2.2 hc.le]
  rw [div_lt_div_iff_of_pos_right hc]
  linarith

/-- `|A| - |R| ≤ |N|` when `A \ R ⊆ N`, for `R` and `N` of finite measure. -/
lemma opt_area_sub_le {A R N : Set (ℝ × ℝ)} (hR : MeasureTheory.volume R ≠ ⊤)
    (hN : MeasureTheory.volume N ≠ ⊤) (h : A \ R ⊆ N) : area A - area R ≤ area N := by
  have hA : MeasureTheory.volume A ≤ MeasureTheory.volume N + MeasureTheory.volume R :=
    (MeasureTheory.measure_mono (subset_sdiff_union A R)).trans
      ((MeasureTheory.measure_union_le _ _).trans
        (add_le_add (MeasureTheory.measure_mono h) le_rfl))
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hN, hR⟩) hA
  rw [ENNReal.toReal_add hN hR] at this
  unfold area
  linarith

/-- The numerical facts on the triangles and the trapezoid of the proof of Lemma 8.2.3. -/
lemma opt_l823_numerics {Xφ Yφ Xψ Yψ τ H w z B : ℝ} (hτ : 0 < τ) (hH : 0 < H)
    (hwX : w = Xφ + Yφ * τ) (hzX : z = Xψ - Yψ * τ) (hwz : z < w) :
    (∀ y ∈ Ioo (-H) Yφ, Xφ + 0 * y ≤ w + -τ * y) ∧
      (∀ y ∈ Ioo (-H) Yψ, z + τ * y ≤ Xψ + 0 * y) ∧
      (∀ y ∈ Ioo (-H) 0, z + τ * y ≤ w + -τ * y) ∧
      0 ≤ (w - Xφ) * (Yφ - -H) + (-τ - 0) * (Yφ ^ 2 - (-H) ^ 2) / 2 ∧
      0 ≤ (Xψ - z) * (Yψ - -H) + (0 - τ) * (Yψ ^ 2 - (-H) ^ 2) / 2 ∧
      0 ≤ (w - z) * (0 - -H) + (-τ - τ) * (0 ^ 2 - (-H) ^ 2) / 2 ∧
      w * Yφ / 2 + (Xψ * Yψ - Xφ * Yφ - 2 * B) / 2 + -Yψ * z / 2 =
        (-B - H * (Xψ - Xφ)) + ((w - Xφ) * (Yφ - -H) + (-τ - 0) * (Yφ ^ 2 - (-H) ^ 2) / 2) +
          ((Xψ - z) * (Yψ - -H) + (0 - τ) * (Yψ ^ 2 - (-H) ^ 2) / 2) -
          ((w - z) * (0 - -H) + (-τ - τ) * (0 ^ 2 - (-H) ^ 2) / 2) := by
  subst hwX hzX
  refine ⟨fun y hy => by nlinarith [mul_pos hτ (sub_pos.mpr hy.2)],
    fun y hy => by nlinarith [mul_pos hτ (sub_pos.mpr hy.2)],
    fun y hy => by nlinarith [mul_pos hτ (neg_pos.mpr hy.2)], ?_, ?_, ?_, by ring⟩
  · nlinarith [mul_nonneg hτ.le (sq_nonneg (Yφ + H))]
  · nlinarith [mul_nonneg hτ.le (sq_nonneg (Yψ + H))]
  · nlinarith [mul_pos hτ (mul_pos hH hH), mul_pos (sub_pos.mpr hwz) hH]

/-- **Lemma 8.2.3** (`lem:cap-middle-lower-estimate`). For `K ∈ 𝒦^i`,
`|𝒩(K) \ H̆_K^R \ H̆_K^L| ≥ 𝒥(W_K^R, 𝐱_K^R) + 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^L, Z_K^L)`.

The proof compares areas below a low line `y = -H`: the region `G₀` between the core curve
`𝐱_K|_{[φ, φ^L]}` and that line, with the triangles `T₁` below `𝐱_K^R` and `T₂` below `𝐱_K^L`, minus
the trapezoid `R` below `y = 0` between the lines `b_K^R` and `d_K^L`, lies in
`𝒩(K) \ H̆_K^R \ H̆_K^L`, and its signed area is the right side. -/
theorem lemma8_2_3 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
        segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hpi := two_le_pi
  have hcap := hK.1
  have h2 := hK.2.1.2.1
  have h3 := hK.2.1.2.2
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  have hψφ : φ < π / 2 - φ := by linarith
  have hψ2 : π / 2 - φ < π / 2 := by linarith
  -- Step 1: `p ∉ H̆_K^R ↔ p.1 < w - τ p.2` and `p ∉ H̆_K^L ↔ z + τ p.2 < p.1`, where `w`, `z` are
  -- the `x`-coordinates of `W_K^R`, `Z_K^L` and `τ = tan φ`.
  obtain ⟨τ, hτ⟩ : ∃ v : ℝ, v = sin φ / cos φ := ⟨_, rfl⟩
  have hτpos : 0 < τ := by rw [hτ]; exact div_pos hs0 hc
  obtain ⟨w, hw⟩ : ∃ v : ℝ, v = (supp K φ - 1) / cos φ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ v : ℝ, v = (1 - supp K (π - φ)) / cos φ := ⟨_, rfl⟩
  have hnR : ∀ p : ℝ × ℝ, p ∉ hRight φ K ↔ p.1 < w - p.2 * τ := by
    intro p; rw [hw, hτ]; exact opt_notMem_hRight_iff hc K p
  have hnL : ∀ p : ℝ × ℝ, p ∉ hLeft φ K ↔ z + p.2 * τ < p.1 := by
    intro p; rw [hz, hτ]; exact opt_notMem_hLeft_iff hc K p
  -- Step 2: the core curve `t ↦ (X(t), Y(t)) = 𝐱_K(t)`, `t ∈ [φ, φ^L]`, with `X` strictly
  -- decreasing.
  have hIcc : ∀ t ∈ Icc φ (π / 2 - φ), t ∈ Ioo 0 (π / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hxc : Continuous (innerCorner K) := opt_innerCorner_continuous hcap.2.1
  have hXc : Continuous fun t => (innerCorner K t).1 := continuous_fst.comp hxc
  have hYc : Continuous fun t => (innerCorner K t).2 := continuous_snd.comp hxc
  have hdc := opt_inj_deriv_continuousOn h2 hφ0 hψ2
  have hXd : ∀ t ∈ Icc φ (π / 2 - φ),
      HasDerivAt (fun t => (innerCorner K t).1) (deriv (innerCorner K) t).1 t := fun t ht =>
    hasDerivAt_fst (opt_inj_hasDerivAt h2 (hIcc t ht))
  have hX'neg : ∀ t ∈ Icc φ (π / 2 - φ), (deriv (innerCorner K) t).1 < 0 := fun t ht =>
    opt_inj_X'_neg h3 (hIcc t ht)
  have hanti : StrictAntiOn (fun t => (innerCorner K t).1) (Icc φ (π / 2 - φ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hXc.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hXd t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact hX'neg t ⟨ht.1.le, ht.2.le⟩
  -- Step 3: a horizontal line `y = -H` below the core curve.
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hYc.continuousOn (s := Icc φ (π / 2 - φ)))
  obtain ⟨H, hH⟩ : ∃ v : ℝ, v = M + 1 := ⟨_, rfl⟩
  have hYH : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2 + H := by
    intro t ht
    have := hM t ht
    rw [Real.norm_eq_abs, abs_le] at this
    linarith
  have hH0 : 0 < H := by
    have := hM φ ⟨le_rfl, hψφ.le⟩
    linarith [norm_nonneg ((innerCorner K φ).2)]
  -- Step 4: the endpoints `𝐱_K^R = (Xφ, Yφ)` on `b_K^R` and `𝐱_K^L = (Xψ, Yψ)` on `d_K^L`; and
  -- `z < w` (this uses `|K| ≥ 2.2`).
  obtain ⟨Xφ, hXφ⟩ : ∃ v : ℝ, v = (innerCorner K φ).1 := ⟨_, rfl⟩
  obtain ⟨Yφ, hYφ⟩ : ∃ v : ℝ, v = (innerCorner K φ).2 := ⟨_, rfl⟩
  obtain ⟨Xψ, hXψ⟩ : ∃ v : ℝ, v = (innerCorner K (π / 2 - φ)).1 := ⟨_, rfl⟩
  obtain ⟨Yψ, hYψ⟩ : ∃ v : ℝ, v = (innerCorner K (π / 2 - φ)).2 := ⟨_, rfl⟩
  have hwX : w = Xφ + Yφ * τ := by
    have := (cn_innerCorner_dot K φ).1
    simp only [dot, uvec] at this
    rw [← hXφ, ← hYφ] at this
    rw [hw, hτ]; field_simp; linarith
  have hzX : z = Xψ - Yψ * τ := by
    have := opt_innerCorner_dot_v K (π / 2 - φ)
    simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub,
      show π / 2 - φ + π / 2 = π - φ by ring] at this
    rw [← hXψ, ← hYψ] at this
    rw [hz, hτ]; field_simp; linarith
  have hXφψ : Xψ < Xφ := by
    rw [hXψ, hXφ]; exact hanti ⟨le_rfl, hψφ.le⟩ ⟨hψφ.le, le_rfl⟩ hψφ
  have hYφH : -H < Yφ := by have := hYH φ ⟨le_rfl, hψφ.le⟩; rw [hYφ]; linarith
  have hYψH : -H < Yψ := by have := hYH (π / 2 - φ) ⟨hψφ.le, le_rfl⟩; rw [hYψ]; linarith
  have hwz : z < w := by rw [hw, hz]; exact opt_l823_wz hφ hK
  obtain ⟨n1, n2, n3, hT1v, hT2v, hRv, -⟩ :=
    opt_l823_numerics (Xφ := Xφ) (Yφ := Yφ) (Xψ := Xψ) (Yψ := Yψ) (B := 0) hτpos hH0 hwX hzX hwz
  -- Step 5: the regions `G₀`, `T₁`, `T₂` and `R`, and their areas.
  have hopen : ∀ a b α₁ β₁ α₂ β₂ : ℝ,
      IsOpen {p : ℝ × ℝ | a < p.2 ∧ p.2 < b ∧ α₁ + β₁ * p.2 < p.1 ∧ p.1 < α₂ + β₂ * p.2} := by
    intro a b α₁ β₁ α₂ β₂
    exact (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_fst).inter (isOpen_lt continuous_fst (by fun_prop))))
  obtain ⟨G₀, hG₀⟩ : ∃ G : Set (ℝ × ℝ), G =
      (fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
        {q : ℝ × ℝ | q.1 ∈ Ioo φ (π / 2 - φ) ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2 + H} :=
    ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ G : Set (ℝ × ℝ), G =
      {p : ℝ × ℝ | -H < p.2 ∧ p.2 < Yφ ∧ Xφ + 0 * p.2 < p.1 ∧ p.1 < w + -τ * p.2} := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ G : Set (ℝ × ℝ), G =
      {p : ℝ × ℝ | -H < p.2 ∧ p.2 < Yψ ∧ z + τ * p.2 < p.1 ∧ p.1 < Xψ + 0 * p.2} := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ G : Set (ℝ × ℝ), G =
      {p : ℝ × ℝ | -H < p.2 ∧ p.2 < 0 ∧ z + τ * p.2 < p.1 ∧ p.1 < w + -τ * p.2} := ⟨_, rfl⟩
  have vG₀ : MeasureTheory.volume G₀ =
      ENNReal.ofReal (∫ t in φ..(π / 2 - φ), -(deriv (innerCorner K) t).1 *
        ((innerCorner K t).2 + H)) := by
    rw [hG₀]
    exact opt_volume_under_curve hψφ hXc hYc hXd
      (continuous_fst.comp_continuousOn hdc) hanti (fun t ht => (hX'neg t ht).le) hYH
  have vT₁ : MeasureTheory.volume T₁ =
      ENNReal.ofReal ((w - Xφ) * (Yφ - -H) + (-τ - 0) * (Yφ ^ 2 - (-H) ^ 2) / 2) := by
    rw [hT₁]
    exact opt_volume_hregion hYφH.le n1
  have vT₂ : MeasureTheory.volume T₂ =
      ENNReal.ofReal ((Xψ - z) * (Yψ - -H) + (0 - τ) * (Yψ ^ 2 - (-H) ^ 2) / 2) := by
    rw [hT₂]
    exact opt_volume_hregion hYψH.le n2
  have vR : MeasureTheory.volume R =
      ENNReal.ofReal ((w - z) * (0 - -H) + (-τ - τ) * (0 ^ 2 - (-H) ^ 2) / 2) := by
    rw [hR]
    exact opt_volume_hregion (by linarith) n3
  -- `G₀`, `T₁` and `T₂` are disjoint: `G₀` lies strictly between `x = Xψ` and `x = Xφ`
  have hG₀fst : ∀ p ∈ G₀, Xψ < p.1 ∧ p.1 < Xφ := by
    rw [hG₀]
    rintro _ ⟨⟨t, s⟩, ⟨ht, -, -⟩, rfl⟩
    rw [hXψ, hXφ]
    exact ⟨hanti ⟨ht.1.le, ht.2.le⟩ ⟨hψφ.le, le_rfl⟩ ht.2,
      hanti ⟨le_rfl, hψφ.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1⟩
  have d1 : Disjoint G₀ T₁ := Set.disjoint_left.mpr fun p hp hq => by
    have := hG₀fst p hp
    rw [hT₁] at hq
    have := hq.2.2.1
    linarith
  have d2 : Disjoint (G₀ ∪ T₁) T₂ := Set.disjoint_left.mpr fun p hp hq => by
    rw [hT₂] at hq
    have := hq.2.2.2
    rcases hp with hp | hp
    · have := hG₀fst p hp; linarith
    · rw [hT₁] at hp; have := hp.2.2.1; linarith
  have vG : MeasureTheory.volume (G₀ ∪ T₁ ∪ T₂) =
      MeasureTheory.volume G₀ + MeasureTheory.volume T₁ + MeasureTheory.volume T₂ := by
    rw [MeasureTheory.measure_union d2 (by rw [hT₂]; exact (hopen _ _ _ _ _ _).measurableSet),
      MeasureTheory.measure_union d1 (by rw [hT₁]; exact (hopen _ _ _ _ _ _).measurableSet)]
  -- Step 6: `(G₀ ∪ T₁ ∪ T₂) \ R ⊆ 𝒩(K) \ H̆_K^R \ H̆_K^L`.
  set N' := (niche K (π / 2) \ hRight φ K) \ hLeft φ K with hN'def
  have hsub : (G₀ ∪ T₁ ∪ T₂) \ R ⊆ N' := by
    rintro p ⟨hpG, hpR⟩
    -- every point of `G₀ ∪ T₁ ∪ T₂` is outside `H̆_K^R` and `H̆_K^L`, above `y = -H`, and in some
    -- quadrant `Q_K⁻(t)`
    have key : p ∉ hRight φ K ∧ p ∉ hLeft φ K ∧ -H < p.2 ∧
        ∃ t ∈ Ioo 0 (π / 2), p ∈ qMinus K t := by
      rcases hpG with (hp | hp) | hp
      · rw [hG₀] at hp
        obtain ⟨⟨t, s⟩, ⟨ht, hs1, hs2⟩, rfl⟩ := hp
        obtain ⟨a1, a2, a3⟩ := opt_l823_curve_pt hφ' hK ht hs1
        exact ⟨a1, a2, by simp only; linarith, t, hIcc t ⟨ht.1.le, ht.2.le⟩, a3⟩
      · rw [hT₁] at hp
        obtain ⟨k3, k4, k5, k6⟩ := hp
        have hnr : p ∉ hRight φ K := (hnR p).mpr (by linarith)
        obtain ⟨a2, a3⟩ := opt_l823_tri1_pt hφ' hK (by rw [← hXφ]; linarith)
          (by rw [← hYφ]; exact k4) hnr
        exact ⟨hnr, a2, k3, φ, ⟨hφ0, by linarith⟩, a3⟩
      · rw [hT₂] at hp
        obtain ⟨k3, k4, k5, k6⟩ := hp
        have hnl : p ∉ hLeft φ K := (hnL p).mpr (by linarith)
        obtain ⟨a1, a3⟩ := opt_l823_tri2_pt hφ' hK (by rw [← hXψ]; linarith)
          (by rw [← hYψ]; exact k4) hnl
        exact ⟨a1, hnl, k3, π / 2 - φ, ⟨by linarith, hψ2⟩, a3⟩
    obtain ⟨k1, k2, k3, t, ht, hq⟩ := key
    have k1' := (hnR p).mp k1
    have k2' := (hnL p).mp k2
    -- and outside `R` it is above `y = 0`, so in the fan
    have hp2 : 0 ≤ p.2 := by
      by_contra hneg
      push Not at hneg
      rw [hR] at hpR
      exact hpR ⟨k3, hneg, by linarith, by linarith⟩
    refine ⟨⟨⟨?_, mem_iUnion₂.mpr ⟨t, ht, hq⟩⟩, k1⟩, k2⟩
    simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, uvec_pi_div_two, dot_mk]
    constructor <;> linarith
  -- Step 7: hence `|G₀| + |T₁| + |T₂| - |R| ≤ |N'|`, and the left side is the curve area sum.
  have hN'fin : MeasureTheory.volume N' ≠ ⊤ :=
    ne_top_of_le_ne_top (nef_niche_isBounded hcap).measure_lt_top.ne
      (MeasureTheory.measure_mono (sdiff_subset.trans sdiff_subset))
  have hRfin : MeasureTheory.volume R ≠ ⊤ := by rw [vR]; exact ENNReal.ofReal_ne_top
  have hle := opt_area_sub_le hRfin hN'fin hsub
  have hA0 := opt_integral_under_inner hcap.2.1 h2 hφ0 hψφ hψ2 H
  set B := ∫ t in φ..(π / 2 - φ), (deriv (innerCorner K) t).1 * (innerCorner K t).2 with hB
  have hA0v : 0 ≤ ∫ t in φ..(π / 2 - φ), -(deriv (innerCorner K) t).1 *
      ((innerCorner K t).2 + H) :=
    intervalIntegral.integral_nonneg hψφ.le fun t ht =>
      mul_nonneg (neg_nonneg.mpr (hX'neg t ht).le) (hYH t ht).le
  have aG : area (G₀ ∪ T₁ ∪ T₂) = (∫ t in φ..(π / 2 - φ), -(deriv (innerCorner K) t).1 *
      ((innerCorner K t).2 + H)) + ((w - Xφ) * (Yφ - -H) + (-τ - 0) * (Yφ ^ 2 - (-H) ^ 2) / 2) +
      ((Xψ - z) * (Yψ - -H) + (0 - τ) * (Yψ ^ 2 - (-H) ^ 2) / 2) := by
    unfold area
    rw [vG, vG₀, vT₁, vT₂, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩) ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hA0v, ENNReal.toReal_ofReal hT1v,
      ENNReal.toReal_ofReal hT2v]
  have aR : area R = (w - z) * (0 - -H) + (-τ - τ) * (0 ^ 2 - (-H) ^ 2) / 2 := by
    unfold area; rw [vR, ENNReal.toReal_ofReal hRv]
  have hCA := opt_curveArea_inner_eq hcap.2.1 h2 hφ0 hψφ hψ2
  rw [← hB] at hCA
  have hsegR : segArea (wRight φ K) (xRight φ K) = w * Yφ / 2 := by
    rw [opt_wRight_eq, xRight, hw, hYφ]; simp only [segArea, cross]; ring
  have hsegL : segArea (xLeft φ K) (zLeft φ K) = -Yψ * z / 2 := by
    rw [opt_zLeft_eq, xLeft, hz, hYψ]; simp only [segArea, cross]; ring
  rw [hsegR, hsegL, hCA, ← hXφ, ← hYφ, ← hXψ, ← hYψ]
  have key : w * Yφ / 2 + (Xψ * Yψ - Xφ * Yφ - 2 * B) / 2 + -Yψ * z / 2 =
      area (G₀ ∪ T₁ ∪ T₂) - area R := by
    rw [aG, aR, hA0, ← hXφ, ← hXψ]
    exact (opt_l823_numerics (B := B) hτpos hH0 hwX hzX hwz).2.2.2.2.2.2
  linarith

/-- **Theorem 8.2.4** (`thm:upper-bound-q`). For `K ∈ 𝒦^i`, `𝒜(K) ≤ 𝒬(K, B_K, D_K)`.
(The decomposition of `𝒩(K)` uses `𝒩(K) ∩ H̆_K^R ∩ H̆_K^L = ∅`, `opt_niche_hRight_hLeft`; the paper
derives it from Lemma 8.1.4, which needs `𝒩(K) ⊆ K`.) -/
theorem theorem8_2_4 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    sofaArea (π / 2) K ≤ upperQ φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  obtain ⟨-, -, hBa, hDb⟩ := opt_inL_supp (theorem8_1_8 hφ hK)
  set N := niche K (π / 2) with hNdef
  -- Step 1: `|𝒩(K)| = |𝒩(K) ∩ H̆_K^R| + |𝒩(K) ∩ H̆_K^L| + |𝒩(K) \ H̆_K^R \ H̆_K^L|`, since
  -- `𝒩(K) ∩ H̆_K^R ∩ H̆_K^L = ∅`
  have hRm : MeasurableSet (hRight φ K) := (isClosed_halfPlus _ _).measurableSet
  have hLm : MeasurableSet (hLeft φ K) := (isClosed_halfPlus _ _).measurableSet
  have hfin : ∀ S ⊆ N, MeasureTheory.volume S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top (nef_niche_isBounded hcap).measure_lt_top.ne
      (MeasureTheory.measure_mono hS)
  have hdecomp : area N = area (N ∩ hRight φ K) + area (N ∩ hLeft φ K) +
      area ((N \ hRight φ K) \ hLeft φ K) := by
    unfold area
    have e1 := MeasureTheory.measure_inter_add_sdiff (μ := MeasureTheory.volume) N hRm
    have e2 := MeasureTheory.measure_inter_add_sdiff (μ := MeasureTheory.volume)
      (N \ hRight φ K) hLm
    have e3 : (N \ hRight φ K) ∩ hLeft φ K = N ∩ hLeft φ K := by
      ext p
      simp only [mem_inter_iff, mem_sdiff]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, fun h2 => ?_⟩, h3⟩
        exact Set.disjoint_left.mp (opt_niche_hRight_hLeft hφ hK) ⟨h1, h2⟩ h3
    rw [e3] at e2
    rw [← e1, ← e2, ENNReal.toReal_add (hfin _ inter_subset_left)
      (ENNReal.add_ne_top.mpr ⟨hfin _ inter_subset_left, hfin _ (sdiff_subset.trans sdiff_subset)⟩),
      ENNReal.toReal_add (hfin _ inter_subset_left) (hfin _ (sdiff_subset.trans sdiff_subset))]
    ring
  -- Step 2: bound the three parts (Lemmas 8.2.2 and 8.2.3), and combine the segment terms on the
  -- lines `b_K^R` and `d_K^L`
  have h22 := lemma8_2_2 hφ hK
  have h23 := lemma8_2_3 hφ hK
  obtain ⟨hXB, hWl, hxR⟩ := opt_right_mem_line hc.ne' hBa
  obtain ⟨hYD, hZl, hxL⟩ := opt_left_mem_line hc.ne' hDb
  have c1 := segArea_add_of_mem_line hXB hWl hxR
  have c2 := segArea_add_of_mem_line hxL hZl hYD
  have s1 := segArea_swap (xRight φ K) (xB φ (rightBody φ K))
  have s2 := segArea_swap (yD φ (leftBody φ K)) (xLeft φ K)
  unfold sofaArea upperQ
  linarith [h22.1, h22.2, h23]

end MovingSofaOptimality
