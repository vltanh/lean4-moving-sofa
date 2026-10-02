module

public import MovingSofa.Optimality.Domain
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

namespace MovingSofa

attribute [local simp] opt_dot_mk

/-! ### Auxiliary facts (package I): convex domains, regularity of `𝐱_K`, curve areas -/

section ConvexDomainAux

variable {U V W : Type}

lemma opt_isConvexLinear_comp {D₁ : ConvexDomain U} {D₂ : ConvexDomain V} {D₃ : ConvexDomain W}
    {f : U → V} {g : V → W} (hf : D₁.IsConvexLinear D₂ f) (hg : D₂.IsConvexLinear D₃ g) :
    D₁.IsConvexLinear D₃ (fun u => g (f u)) := fun c hc v w => by
  simp only [hf c hc, hg c hc]

lemma opt_isQuadratic_comp {D₁ : ConvexDomain U} {D₂ : ConvexDomain V} {pr : U → V}
    (hpr : D₁.IsConvexLinear D₂ pr) {f : V → ℝ} (hf : D₂.IsQuadratic f) :
    D₁.IsQuadratic (fun v => f (pr v)) := by
  obtain ⟨g, ⟨hg1, hg2⟩, hfg⟩ := hf
  refine ⟨fun v w => g (pr v) (pr w), ⟨fun v₁ c hc v w => ?_, fun v₂ c hc v w => ?_⟩,
    fun v => hfg _⟩
  · simp only [hpr c hc]; exact hg1 _ c hc _ _
  · simp only [hpr c hc]; exact hg2 _ c hc _ _

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

lemma opt_convexBodyComb_val {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : ConvexBodySet) :
    (convexBodyComb c K₁ K₂).1 = (1 - c) • K₁.1 + c • K₂.1 := by
  simp [convexBodyComb, hc]

lemma opt_projK_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.1) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

lemma opt_projB_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.2.1) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

lemma opt_projD_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear convexBodyDomain (fun x : LTriple φ => x.1.2.2) := by
  intro c hc x y
  simp only [lDomain, LTriple.comb, hc, ↓reduceDIte]
  rfl

lemma opt_innerCorner_linear (t : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => innerCorner K.1 t) := by
  intro c hc K₁ K₂
  show innerCorner (convexBodyComb c K₁ K₂).1 t = (1 - c) • innerCorner K₁.1 t + c • innerCorner K₂.1 t
  rw [opt_convexBodyComb_val hc, opt_innerCorner_comb K₁.2 K₂.2 hc]; rfl

lemma opt_outerCorner_linear (t : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => outerCorner K.1 t) := by
  intro c hc K₁ K₂
  show outerCorner (convexBodyComb c K₁ K₂).1 t = (1 - c) • outerCorner K₁.1 t + c • outerCorner K₂.1 t
  rw [opt_convexBodyComb_val hc, opt_outerCorner_comb K₁.2 K₂.2 hc]; rfl

lemma opt_vplus_linear (a : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vplus K.1 a) :=
  (theorem7_1_2_vertices a (a + 1)).1

lemma opt_vminus_linear (a : ℝ) :
    convexBodyDomain.IsConvexLinear (vectorDomain (ℝ × ℝ)) (fun K => vminus K.1 a) :=
  (theorem7_1_2_vertices a (a + 1)).2.1

/-! #### Regularity of the support function and of `𝐱_K`, `𝐲_K` -/

lemma opt_supp_lipschitz {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : NNReal, LipschitzWith C (supp K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hne.some_mem)
  have key : ∀ s t, supp K s ≤ supp K t + 2 * R * |s - t| := by
    intro s t
    show sSup _ ≤ _
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    have h1 := dot_le_supp hK hp t
    have hp1 : |p.1| ≤ R := (norm_fst_le p).trans (hR p hp)
    have hp2 : |p.2| ≤ R := (norm_snd_le p).trans (hR p hp)
    have hc := abs_cos_sub_cos_le s t
    have hs := abs_sin_sub_sin_le s t
    have e : dot p (uvec s) - dot p (uvec t) = p.1 * (cos s - cos t) + p.2 * (sin s - sin t) := by
      simp only [dot, uvec]; ring
    have b1 : p.1 * (cos s - cos t) ≤ R * |s - t| := by
      calc p.1 * (cos s - cos t) ≤ |p.1 * (cos s - cos t)| := le_abs_self _
        _ = |p.1| * |cos s - cos t| := abs_mul _ _
        _ ≤ R * |s - t| := mul_le_mul hp1 hc (abs_nonneg _) hR0
    have b2 : p.2 * (sin s - sin t) ≤ R * |s - t| := by
      calc p.2 * (sin s - sin t) ≤ |p.2 * (sin s - sin t)| := le_abs_self _
        _ = |p.2| * |sin s - sin t| := abs_mul _ _
        _ ≤ R * |s - t| := mul_le_mul hp2 hs (abs_nonneg _) hR0
    linarith
  refine ⟨⟨2 * R, by positivity⟩, LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  show dist (supp K s) (supp K t) ≤ 2 * R * dist s t
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  have := key s t
  have := key t s
  rw [abs_sub_comm t s] at this
  constructor <;> linarith

lemma opt_uvec_lipschitz : LipschitzWith 1 uvec :=
  LipschitzWith.of_dist_le_mul fun s t => by
    simp only [Prod.dist_eq, uvec, Real.dist_eq, NNReal.coe_one, one_mul]
    exact max_le (abs_cos_sub_cos_le s t) (abs_sin_sub_sin_le s t)

lemma opt_vvec_lipschitz : LipschitzWith 1 vvec :=
  LipschitzWith.of_dist_le_mul fun s t => by
    simp only [Prod.dist_eq, vvec, Real.dist_eq, NNReal.coe_one, one_mul]
    refine max_le ?_ (abs_cos_sub_cos_le s t)
    rw [show -sin s - -sin t = -(sin s - sin t) by ring, abs_neg]
    exact abs_sin_sub_sin_le s t

/-- The bilinear map `((α, β), (u, v)) ↦ α u + β v`. -/
noncomputable def opt_frameCLM : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

lemma opt_frameCLM_apply (ab : ℝ × ℝ) (uv : (ℝ × ℝ) × (ℝ × ℝ)) :
    opt_frameCLM ab uv = ab.1 • uv.1 + ab.2 • uv.2 := by
  simp [opt_frameCLM]

lemma opt_lipschitz_bv {E : Type*} [PseudoEMetricSpace E] {f : ℝ → E} {C : NNReal}
    (hf : LipschitzWith C f) (a b : ℝ) : BoundedVariationOn f (Icc a b) := by
  have := hf.locallyBoundedVariationOn univ a b (mem_univ _) (mem_univ _)
  rwa [univ_inter] at this

lemma opt_frame_bv {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (α β : ℝ) (a b : ℝ) :
    BoundedVariationOn
      (fun t => opt_frameCLM (supp K t + α, supp K (t + π / 2) + β) (uvec t, vvec t)) (Icc a b) := by
  obtain ⟨C, hC⟩ := opt_supp_lipschitz hK hne
  have h1 : LipschitzWith C (fun t => supp K t + α) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_add_right]; exact hC.dist_le_mul s t
  have h2 : LipschitzWith C (fun t => supp K (t + π / 2) + β) :=
    LipschitzWith.of_dist_le_mul fun s t => by
      rw [dist_add_right]
      have := hC.dist_le_mul (s + π / 2) (t + π / 2)
      rwa [dist_add_right] at this
  have hF := opt_lipschitz_bv (h1.prodMk h2) a b
  have hG := opt_lipschitz_bv (opt_uvec_lipschitz.prodMk opt_vvec_lipschitz) a b
  exact hF.bilinear_comp hG opt_frameCLM

lemma opt_innerCorner_eq_frame (K : Set (ℝ × ℝ)) (t : ℝ) :
    innerCorner K t = opt_frameCLM (supp K t + (-1), supp K (t + π / 2) + (-1)) (uvec t, vvec t) := by
  rw [proposition2_2_2_innerCorner, opt_frameCLM_apply]
  simp only [sub_eq_add_neg]

lemma opt_outerCorner_eq_frame (K : Set (ℝ × ℝ)) (t : ℝ) :
    outerCorner K t = opt_frameCLM (supp K t + 0, supp K (t + π / 2) + 0) (uvec t, vvec t) := by
  rw [proposition2_2_2_outerCorner, opt_frameCLM_apply]
  simp only [add_zero]

lemma opt_innerCorner_continuous {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (innerCorner K) := by
  have hs := continuous_supp hK.2.1
  have : innerCorner K = fun t => (supp K t - 1) • uvec t + (supp K (t + π / 2) - 1) • vvec t :=
    funext (proposition2_2_2_innerCorner K)
  rw [this]
  unfold uvec vvec
  fun_prop

lemma opt_outerCorner_continuous {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Continuous (outerCorner K) := by
  have hs := continuous_supp hK.2.1
  have : outerCorner K = fun t => supp K t • uvec t + supp K (t + π / 2) • vvec t :=
    funext (proposition2_2_2_outerCorner K)
  rw [this]
  unfold uvec vvec
  fun_prop

lemma opt_innerCorner_cbv {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IsCBV (innerCorner K) a b := by
  refine ⟨(opt_innerCorner_continuous hK).continuousOn, ?_⟩
  have h := opt_frame_bv hK.2.1 hK.1 (-1) (-1) a b
  have e : innerCorner K = fun t =>
      opt_frameCLM (supp K t + (-1), supp K (t + π / 2) + (-1)) (uvec t, vvec t) :=
    funext (opt_innerCorner_eq_frame K)
  rwa [e]

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

lemma opt_innerCBV_linear (a b : ℝ) :
    convexBodyDomain.IsConvexLinear (cbvDomain a b) (opt_innerCBV a b) := by
  intro c hc K₁ K₂
  apply Subtype.ext
  show innerCorner (convexBodyComb c K₁ K₂).1 = (1 - c) • innerCorner K₁.1 + c • innerCorner K₂.1
  rw [opt_convexBodyComb_val hc, opt_innerCorner_comb K₁.2 K₂.2 hc]

/-! #### Curve areas -/

lemma opt_clampFun_congr {α : Type*} {x y : ℝ → α} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn x y (Icc a b)) : clampFun x a b = clampFun y a b := by
  funext t
  simp only [clampFun]
  exact h ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- The curve area functional only depends on the values of the curve on `[a, b]`. -/
lemma opt_curveArea_congr {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn x y (Icc a b)) :
    curveArea x a b = curveArea y a b := by
  unfold curveArea curveBilin lsMeasure
  rw [opt_clampFun_congr hab h]
  congr 1
  exact MeasureTheory.VectorMeasure.setIntegral_congr_fun h

/-- A curve that is constant on `[a, b]` has zero curve area functional. -/
lemma opt_curveArea_const {x : ℝ → ℝ × ℝ} {a b : ℝ} {P : ℝ × ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, x t = P) : curveArea x a b = 0 := by
  rw [opt_curveArea_congr hab (y := fun _ => P) h]
  have hc : ContDiffOn ℝ 1 (fun _ : ℝ => P) (Icc a b) := contDiffOn_const
  rw [curveArea_eq_integral hab hc]
  have : ∀ t ∈ Set.uIcc a b, cross P (derivWithin (fun _ : ℝ => P) (Icc a b) t) = 0 := by
    intro t _
    rw [derivWithin_fun_const]; simp [cross]
  rw [intervalIntegral.integral_congr this]
  simp

/-- Collinear points: `𝒥(p, q) + 𝒥(q, r) = 𝒥(p, r)`. -/
lemma opt_segArea_collinear {p q r : ℝ × ℝ} {t c : ℝ} (hp : p ∈ line t c) (hq : q ∈ line t c)
    (hr : r ∈ line t c) : segArea p q + segArea q r = segArea p r := by
  simp only [line, mem_ofPred_eq, dot, uvec] at hp hq hr
  simp only [segArea, cross]
  have h1 : (p.1 * q.2 - p.2 * q.1 + (q.1 * r.2 - q.2 * r.1) - (p.1 * r.2 - p.2 * r.1)) * cos t = 0 := by
    linear_combination (q.2 - r.2) * hp + (r.2 - p.2) * hq + (p.2 - q.2) * hr
  have h2 : (p.1 * q.2 - p.2 * q.1 + (q.1 * r.2 - q.2 * r.1) - (p.1 * r.2 - p.2 * r.1)) * sin t = 0 := by
    linear_combination (-(q.1 - r.1)) * hp + (-(r.1 - p.1)) * hq + (-(p.1 - q.1)) * hr
  have hD : p.1 * q.2 - p.2 * q.1 + (q.1 * r.2 - q.2 * r.1) - (p.1 * r.2 - p.2 * r.1) = 0 := by
    have := sin_sq_add_cos_sq t
    linear_combination (sin t) * h2 + (cos t) * h1 -
      (p.1 * q.2 - p.2 * q.1 + (q.1 * r.2 - q.2 * r.1) - (p.1 * r.2 - p.2 * r.1)) * this
  linear_combination hD / 2

lemma opt_segArea_swap (p q : ℝ × ℝ) : segArea p q = -segArea q p := by
  simp only [segArea, cross]; ring

lemma opt_segArea_self (p : ℝ × ℝ) : segArea p p = 0 := by
  simp only [segArea, cross]; ring

/-- Two points on the `x`-axis have zero curve area functional. -/
lemma opt_segArea_xaxis {p q : ℝ × ℝ} (hp : p.2 = 0) (hq : q.2 = 0) : segArea p q = 0 := by
  simp only [segArea, cross, hp, hq]; ring



/-! #### Areas of plane regions (for Lemma 8.2.3) -/

lemma opt_integral_affine (a b α β : ℝ) :
    ∫ y in a..b, (α + β * y) = α * (b - a) + β * (b ^ 2 - a ^ 2) / 2 := by
  have h : ∀ y ∈ uIcc a b, HasDerivAt (fun y => α * y + β * (y * y / 2)) (α + β * y) y := by
    intro y _
    have := ((hasDerivAt_id y).const_mul α).add
      ((((hasDerivAt_id y).mul (hasDerivAt_id y)).div_const 2).const_mul β)
    convert this using 1
    · funext z; simp only [Pi.add_apply, Pi.mul_apply, id]
    · simp only [id]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun y : ℝ => α + β * y).intervalIntegrable a b)]
  ring

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
  rw [this, opt_integral_affine]

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
def tailD (φ : ℝ) (D : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := convexCurve D (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
/-- Its starting point `Z_D = v_D⁺(3π/2)`. -/
noncomputable def zD (D : Set (ℝ × ℝ)) : ℝ × ℝ := vplus D (3 * π / 2)
/-- Its ending point `Y_D = v_D⁻(3π/2 + φ^L)`. -/
noncomputable def yD (φ : ℝ) (D : Set (ℝ × ℝ)) : ℝ × ℝ := vminus D (3 * π / 2 + (π / 2 - φ))

/-- The upper bound `𝒬(K, B, D) = |K| + 𝒥(𝐝_D) + 𝒥(Y_D, 𝐱_K^L) - 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^R, X_B)
+ 𝒥(𝐛_B)` (Definition 8.2.2, `def:upper-bound-q`). -/
noncomputable def upperQ (φ : ℝ) (K B D : Set (ℝ × ℝ)) : ℝ :=
  area K + convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) + segArea (yD φ D) (xLeft φ K) -
    curveArea (innerCorner K) φ (π / 2 - φ) + segArea (xRight φ K) (xB φ B) +
    convexCurveArea B (π + φ) (3 * π / 2)

/-- `𝒬` as a function on the convex domain `𝓛`. -/
noncomputable def upperQL (φ : ℝ) (x : LTriple φ) : ℝ := upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

/-- **Proposition 8.2.1** (`pro:upper-bound-q-quadratic`). `𝒬` is a quadratic functional on `𝓛`. -/
theorem proposition8_2_1 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) : (lDomain φ).IsQuadratic (upperQL φ) := by
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

/-- **Lemma 8.2.2** (`lem:cap-left-right-tail`). For `K ∈ 𝒦^i`, `B = B_K`, `D = D_K`:
`|𝒩(K) ∩ H̆_K^R| ≥ 𝒥(X_B, W_K^R) - 𝒥(𝐛_B)` and `|𝒩(K) ∩ H̆_K^L| ≥ 𝒥(Z_K^L, Y_D) - 𝒥(𝐝_D)`. -/
theorem lemma8_2_2 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    segArea (xB φ (rightBody φ K)) (wRight φ K) - convexCurveArea (rightBody φ K) (π + φ) (3 * π / 2) ≤
        area (niche K (π / 2) ∩ hRight φ K) ∧
      segArea (zLeft φ K) (yD φ (leftBody φ K)) -
          convexCurveArea (leftBody φ K) (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) ≤
        area (niche K (π / 2) ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  obtain ⟨-, hBcb, hDcb, hBK, hDK, -, eB1, eB2, -, eD1, eD2⟩ := theorem8_1_8 hφ hK
  have hfin : ∀ S ⊆ niche K (π / 2), MeasureTheory.volume S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top (nef_niche_isBounded hcap).measure_lt_top.ne
      (MeasureTheory.measure_mono hS)
  have hW := (lemma8_1_5 hφ hK).1.1.1
  have hZ := (lemma8_1_5 hφ hK).2.1.1
  constructor
  · set B := rightBody φ K with hBdef
    have hB3 : supp B (3 * π / 2) = 0 := by
      rw [show 3 * π / 2 = π + π / 2 by ring]; linarith [hcap.2.2.2.1]
    have hBa : supp B (π + φ) = 1 - supp K φ := by linarith
    have hvint : vint B (π + φ) (3 * π / 2) = wRight φ K := by
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
    have hWB : (vminus B (3 * π / 2)).2 = 0 := by
      have := dot_vminus_uvec B (3 * π / 2)
      rw [hB3, opt_uvec_three_pi_div_two] at this
      simp at this
      linarith
    have hab : π + φ < 3 * π / 2 := by linarith
    have hba : 3 * π / 2 < π + φ + π := by linarith
    by_cases hdeg : vplus B (π + φ) = vminus B (3 * π / 2)
    · obtain ⟨hv, hcurve⟩ := lemma7_3_1_degenerate hBcb hab hba hdeg
      have hcca : convexCurveArea B (π + φ) (3 * π / 2) = 0 := by
        obtain ⟨γ, -, himg, -, -, -, harea⟩ := theorem7_3_2 hBcb hab hba
        rw [← harea]
        apply opt_curveArea_const zero_le_one (P := vplus B (π + φ))
        intro t ht
        have : γ t ∈ convexCurve B (π + φ) (3 * π / 2) := himg ▸ mem_image_of_mem γ ht
        rw [hcurve] at this
        exact this
      rw [hcca, xB, ← hv, hvint, opt_segArea_self, sub_zero]
      exact ENNReal.toReal_nonneg
    · obtain ⟨hsub, -, harea⟩ := lemma7_3_5 hBcb hab hba hdeg
      rw [hvint, opt_segArea_xaxis rfl hWB, add_zero] at harea
      rw [xB, ← harea]
      apply ENNReal.toReal_mono (hfin _ inter_subset_left)
      apply MeasureTheory.measure_mono
      intro p hp
      have hpK : p ∈ K := by
        have hsubK : ({vplus B (π + φ), vint B (π + φ) (3 * π / 2), vminus B (3 * π / 2)} :
            Set (ℝ × ℝ)) ⊆ K := by
          intro q hq
          simp only [mem_insert_iff, mem_singleton_iff] at hq
          rcases hq with rfl | rfl | rfl
          · exact hBK (vplus_mem_edge hBcb _).1
          · rw [hvint]; exact hW
          · exact hBK (vminus_mem_edge hBcb _).1
        exact convexHull_min hsubK hcap.2.1.2.2 (interior_subset hp.1)
      have hpH := interior_subset (hsub hp)
      simp only [suppHalf, halfMinus, mem_inter_iff, mem_ofPred_eq, hB3,
        opt_uvec_three_pi_div_two, opt_dot_mk, show π + φ = φ + π by ring, uvec_add_pi,
        dot_neg_right] at hpH
      obtain ⟨hpR', hp2⟩ := hpH
      have hBa' : supp B (φ + π) = 1 - supp K φ := by rw [add_comm]; exact hBa
      have hpR : p ∈ hRight φ K := by
        simp only [hRight, halfB, halfPlus, mem_ofPred_eq]; linarith
      have hp2' : 0 ≤ p.2 := by linarith
      have hpB : p ∉ B := by
        intro hpB
        apply hp.2
        simp only [mem_iInter₂]
        intro t _
        exact dot_le_supp hBcb.2.1 hpB t
      have : ∃ s ∈ Icc φ (π / 2), p ∉ halfB K s := by
        by_contra hcon
        push Not at hcon
        exact hpB ⟨hpK, mem_iInter₂.mpr hcon⟩
      obtain ⟨s, hs, hps⟩ := this
      have hsφ : φ < s := by
        rcases eq_or_lt_of_le hs.1 with h | h
        · subst h; exact absurd hpR hps
        · exact h
      have hsπ : s < π / 2 := by
        rcases eq_or_lt_of_le hs.2 with h | h
        · subst h
          exfalso; apply hps
          simp only [halfB, halfPlus, mem_ofPred_eq, hcap.2.2.2.1, opt_uvec_pi_div_two, opt_dot_mk]
          linarith
        · exact h
      have hw := (lemma8_1_6_right hφ' hK ⟨hsφ, hsπ.le⟩).2.2
      have hpw : p ∈ wedge K (π / 2) s := by
        have : p ∈ (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K s := by
          refine ⟨⟨hpR, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, opt_uvec_pi_div_two, opt_dot_mk]; linarith
        rw [← hw] at this
        exact this.2
      refine ⟨⟨hpw.1, ?_⟩, hpR⟩
      simp only [mem_iUnion]
      exact ⟨s, ⟨by linarith, hsπ⟩, hpw.2⟩
  · set D := leftBody φ K with hDdef
    have hD3 : supp D (3 * π / 2) = 0 := by
      simp only [add_zero] at eD1; linarith [hcap.2.2.2.1]
    have hDb : supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
      rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at eD2; linarith
    have hvint : vint D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) = zLeft φ K := by
      rw [opt_zLeft_eq]
      simp only [vint, hD3, hDb, show 3 * π / 2 + (π / 2 - φ) - 3 * π / 2 = π / 2 - φ by ring,
        sin_pi_div_two_sub, opt_vvec_three_pi_div_two, zero_smul, zero_add, zero_mul, sub_zero]
      ext
      · simp
      · simp
    have hZD : (vplus D (3 * π / 2)).2 = 0 := by
      have := dot_vplus_uvec D (3 * π / 2)
      rw [hD3, opt_uvec_three_pi_div_two] at this
      simp at this
      linarith
    have hab : 3 * π / 2 < 3 * π / 2 + (π / 2 - φ) := by linarith
    have hba : 3 * π / 2 + (π / 2 - φ) < 3 * π / 2 + π := by linarith
    by_cases hdeg : vplus D (3 * π / 2) = vminus D (3 * π / 2 + (π / 2 - φ))
    · obtain ⟨hv, hcurve⟩ := lemma7_3_1_degenerate hDcb hab hba hdeg
      have hcca : convexCurveArea D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) = 0 := by
        obtain ⟨γ, -, himg, -, -, -, harea⟩ := theorem7_3_2 hDcb hab hba
        rw [← harea]
        apply opt_curveArea_const zero_le_one (P := vplus D (3 * π / 2))
        intro t ht
        have : γ t ∈ convexCurve D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) :=
          himg ▸ mem_image_of_mem γ ht
        rw [hcurve] at this
        exact this
      rw [hcca, yD, ← hdeg, ← hv, hvint, opt_segArea_self, sub_zero]
      exact ENNReal.toReal_nonneg
    · obtain ⟨hsub, -, harea⟩ := lemma7_3_5 hDcb hab hba hdeg
      rw [hvint, opt_segArea_xaxis hZD (by rw [opt_zLeft_eq]), zero_add] at harea
      rw [yD, ← harea]
      apply ENNReal.toReal_mono (hfin _ inter_subset_left)
      apply MeasureTheory.measure_mono
      intro p hp
      have hpK : p ∈ K := by
        have hsubK : ({vplus D (3 * π / 2), vint D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)),
            vminus D (3 * π / 2 + (π / 2 - φ))} : Set (ℝ × ℝ)) ⊆ K := by
          intro q hq
          simp only [mem_insert_iff, mem_singleton_iff] at hq
          rcases hq with rfl | rfl | rfl
          · exact hDK (vplus_mem_edge hDcb _).1
          · rw [hvint]; exact hZ
          · exact hDK (vminus_mem_edge hDcb _).1
        exact convexHull_min hsubK hcap.2.1.2.2 (interior_subset hp.1)
      have hpH := interior_subset (hsub hp)
      simp only [suppHalf, halfMinus, mem_inter_iff, mem_ofPred_eq, hD3,
        opt_uvec_three_pi_div_two, opt_dot_mk,
        show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring, uvec_add_pi,
        dot_neg_right, uvec_add_pi_div_two] at hpH
      obtain ⟨hp2, hpL'⟩ := hpH
      have hDb' : supp D (π / 2 - φ + π / 2 + π) = 1 - supp K (π / 2 - φ + π / 2) := by
        rw [show π / 2 - φ + π / 2 + π = 3 * π / 2 + (π / 2 - φ) by ring,
          show π / 2 - φ + π / 2 = π - φ by ring]
        exact hDb
      have hpL : p ∈ hLeft φ K := by
        simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, uvec_add_pi_div_two]
        linarith
      have hp2' : 0 ≤ p.2 := by linarith
      have hpD : p ∉ D := by
        intro hpD
        apply hp.2
        simp only [mem_iInter₂]
        intro t _
        exact dot_le_supp hDcb.2.1 hpD t
      have : ∃ s ∈ Icc 0 (π / 2 - φ), p ∉ halfD K s := by
        by_contra hcon
        push Not at hcon
        exact hpD ⟨hpK, mem_iInter₂.mpr hcon⟩
      obtain ⟨s, hs, hps⟩ := this
      have hs0 : 0 < s := by
        rcases eq_or_lt_of_le hs.1 with h | h
        · subst h
          exfalso; apply hps
          simp only [halfD, halfPlus, mem_ofPred_eq, zero_add, hcap.2.2.2.1, opt_uvec_pi_div_two,
            opt_dot_mk]
          linarith
        · exact h
      have hsψ : s < π / 2 - φ := by
        rcases eq_or_lt_of_le hs.2 with h | h
        · subst h; exact absurd hpL hps
        · exact h
      have hw := (lemma8_1_6_left hφ' hK ⟨hs0.le, hsψ⟩).2.2
      have hpw : p ∈ wedge K (π / 2) s := by
        have : p ∈ (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K s := by
          refine ⟨⟨hpL, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, opt_uvec_pi_div_two, opt_dot_mk]; linarith
        rw [← hw] at this
        exact this.2
      refine ⟨⟨hpw.1, ?_⟩, hpL⟩
      simp only [mem_iUnion]
      exact ⟨s, ⟨hs0, by linarith⟩, hpw.2⟩

/-! #### Auxiliary lemmas for Lemma 8.2.3 -/

lemma opt_notMem_hRight_iff {φ : ℝ} (hc : 0 < cos φ) (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    p ∉ hRight φ K ↔ p.1 < (supp K φ - 1) / cos φ - p.2 * (sin φ / cos φ) := by
  simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
  rw [show (supp K φ - 1) / cos φ - p.2 * (sin φ / cos φ) =
      (supp K φ - 1 - p.2 * sin φ) / cos φ by field_simp, lt_div_iff₀ hc]
  constructor <;> intro h <;> linarith

lemma opt_notMem_hLeft_iff {φ : ℝ} (hc : 0 < cos φ) (K : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    p ∉ hLeft φ K ↔ (1 - supp K (π - φ)) / cos φ + p.2 * (sin φ / cos φ) < p.1 := by
  simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, dot, uvec,
    show π / 2 - φ + π / 2 = π - φ by ring, cos_pi_sub, sin_pi_sub]
  rw [show (1 - supp K (π - φ)) / cos φ + p.2 * (sin φ / cos φ) =
      (1 - supp K (π - φ) + p.2 * sin φ) / cos φ by field_simp, div_lt_iff₀ hc]
  constructor <;> intro h <;> linarith

/-- The points vertically below the core curve. -/
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
  have e3 := opt_innerCorner_dot_u K t
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

/-- The points of the right side triangle below `𝐱_K^R`. -/
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

/-- The points of the left side triangle below `𝐱_K^L`. -/
lemma opt_l823_tri2_pt {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    {p : ℝ × ℝ} (h1 : p.1 < (innerCorner K (π / 2 - φ)).1)
    (h2 : p.2 < (innerCorner K (π / 2 - φ)).2) (h3 : p ∉ hLeft φ K) :
    p ∉ hRight φ K ∧ p ∈ qMinus K (π / 2 - φ) := by
  have hpi := pi_pos
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc0 : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e1 := opt_innerCorner_lt_right hφ hK (t := π / 2 - φ)
    ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  have e3 := opt_innerCorner_dot_u K (π / 2 - φ)
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
    (continuous_snd.comp hxc).continuousOn
    (fun t ht => (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd t (hmem t ht)))
    (fun t ht => (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd t (hmem t ht)))
    hX'i hY'i
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
      (fun t ht => (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
        (hd t (by rwa [uIcc_of_le hab.le] at ht))) hX'i
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
  have e := opt_dot_frame_u (deriv (innerCorner K) t) 0 t
  rw [opt_uvec_zero] at e
  simp only [opt_dot_mk, mul_one, mul_zero, add_zero, zero_sub, cos_neg, sin_neg] at e
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], ht.2⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  rw [e]
  nlinarith [mul_pos hct (neg_pos.mpr hu), mul_pos hst hv]

/-- `Z_K^L` is to the left of `W_K^R` (this uses `|K| ≥ 2.2`). -/
lemma opt_l823_wz {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    (1 - supp K (π - φ)) / cos φ < (supp K φ - 1) / cos φ := by
  obtain ⟨hφ0, hφ4, hs4, hc9, hs0⟩ := opt_phi_bounds hφ
  have hc : 0 < cos φ := by linarith
  have hcap := hK.1
  have harea := opt_area_le_of_fst_bounds hcap
    (fun q hq => opt_cap_fst_le_phi hcap hc hs0.le hq)
  have hKa := hK.2.2
  have e : supp K φ / cos φ - -supp K (π - φ) / cos φ =
      (supp K φ + supp K (π - φ)) / cos φ := by ring
  rw [e, le_div_iff₀ hc] at harea
  have : 2 < supp K φ + supp K (π - φ) := by nlinarith [mul_le_mul_of_nonneg_right hKa hc.le]
  rw [div_lt_div_iff_of_pos_right hc]
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
`|𝒩(K) \ H̆_K^R \ H̆_K^L| ≥ 𝒥(W_K^R, 𝐱_K^R) + 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^L, Z_K^L)`. -/
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
  obtain ⟨τ, hτ⟩ : ∃ v : ℝ, v = sin φ / cos φ := ⟨_, rfl⟩
  have hτpos : 0 < τ := by rw [hτ]; exact div_pos hs0 hc
  obtain ⟨w, hw⟩ : ∃ v : ℝ, v = (supp K φ - 1) / cos φ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ v : ℝ, v = (1 - supp K (π - φ)) / cos φ := ⟨_, rfl⟩
  have hnR : ∀ p : ℝ × ℝ, p ∉ hRight φ K ↔ p.1 < w - p.2 * τ := by
    intro p; rw [hw, hτ]; exact opt_notMem_hRight_iff hc K p
  have hnL : ∀ p : ℝ × ℝ, p ∉ hLeft φ K ↔ z + p.2 * τ < p.1 := by
    intro p; rw [hz, hτ]; exact opt_notMem_hLeft_iff hc K p
  -- the core curve
  have hIcc : ∀ t ∈ Icc φ (π / 2 - φ), t ∈ Ioo 0 (π / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hxc : Continuous (innerCorner K) := opt_innerCorner_continuous hcap.2.1
  have hXc : Continuous fun t => (innerCorner K t).1 := continuous_fst.comp hxc
  have hYc : Continuous fun t => (innerCorner K t).2 := continuous_snd.comp hxc
  have hdc := opt_inj_deriv_continuousOn h2 hφ0 hψ2
  have hXd : ∀ t ∈ Icc φ (π / 2 - φ),
      HasDerivAt (fun t => (innerCorner K t).1) (deriv (innerCorner K) t).1 t := fun t ht =>
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
      (opt_inj_hasDerivAt h2 (hIcc t ht))
  have hX'neg : ∀ t ∈ Icc φ (π / 2 - φ), (deriv (innerCorner K) t).1 < 0 := fun t ht =>
    opt_inj_X'_neg h3 (hIcc t ht)
  have hanti : StrictAntiOn (fun t => (innerCorner K t).1) (Icc φ (π / 2 - φ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hXc.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hXd t ⟨ht.1.le, ht.2.le⟩).deriv]
    exact hX'neg t ⟨ht.1.le, ht.2.le⟩
  -- a low horizontal line `y = -H`
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
  -- the endpoints `𝐱_K^R` and `𝐱_K^L`
  obtain ⟨Xφ, hXφ⟩ : ∃ v : ℝ, v = (innerCorner K φ).1 := ⟨_, rfl⟩
  obtain ⟨Yφ, hYφ⟩ : ∃ v : ℝ, v = (innerCorner K φ).2 := ⟨_, rfl⟩
  obtain ⟨Xψ, hXψ⟩ : ∃ v : ℝ, v = (innerCorner K (π / 2 - φ)).1 := ⟨_, rfl⟩
  obtain ⟨Yψ, hYψ⟩ : ∃ v : ℝ, v = (innerCorner K (π / 2 - φ)).2 := ⟨_, rfl⟩
  have hwX : w = Xφ + Yφ * τ := by
    have := opt_innerCorner_dot_u K φ
    simp only [dot, uvec] at this
    rw [← hXφ, ← hYφ] at this
    rw [hw, hτ]; field_simp; linarith
  have hzX : z = Xψ - Yψ * τ := by
    have := opt_innerCorner_dot_v K (π / 2 - φ)
    simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub,
      show π / 2 - φ + π / 2 = π - φ by ring] at this
    rw [← hXψ, ← hYψ] at this
    rw [hz, hτ]; field_simp; linarith
  have hRd : z + Yφ * τ < Xφ := by
    have h1 : -Xφ * cos φ + Yφ * sin φ < supp K (π - φ) - 1 := by
      have := opt_innerCorner_lt_left hφ' hK (t := φ) ⟨hφ0.le, hψφ⟩
      simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub,
        show π / 2 - φ + π / 2 = π - φ by ring] at this
      rw [hXφ, hYφ]; linarith
    have e : (z + Yφ * τ) * cos φ = 1 - supp K (π - φ) + Yφ * sin φ := by
      rw [hz, hτ]; field_simp
    have : (z + Yφ * τ) * cos φ < Xφ * cos φ := by rw [e]; linarith
    exact lt_of_mul_lt_mul_right this hc.le
  have hLb : Xψ < w - Yψ * τ := by
    have h1 : Xψ * cos φ + Yψ * sin φ < supp K φ - 1 := by
      have := opt_innerCorner_lt_right hφ' hK (t := π / 2 - φ) ⟨hψφ, by linarith⟩
      simp only [dot, uvec] at this
      rw [hXψ, hYψ]; exact this
    have e : (w - Yψ * τ) * cos φ = supp K φ - 1 - Yψ * sin φ := by
      rw [hw, hτ]; field_simp
    have : Xψ * cos φ < (w - Yψ * τ) * cos φ := by rw [e]; linarith
    exact lt_of_mul_lt_mul_right this hc.le
  have hXφψ : Xψ < Xφ := by
    rw [hXψ, hXφ]; exact hanti ⟨le_rfl, hψφ.le⟩ ⟨hψφ.le, le_rfl⟩ hψφ
  have hYφH : -H < Yφ := by have := hYH φ ⟨le_rfl, hψφ.le⟩; rw [hYφ]; linarith
  have hYψH : -H < Yψ := by have := hYH (π / 2 - φ) ⟨hψφ.le, le_rfl⟩; rw [hYψ]; linarith
  -- `W_K^R` is right of `Z_K^L` (uses `|K| ≥ 2.2`)
  have hwz : z < w := by rw [hw, hz]; exact opt_l823_wz hφ hK
  obtain ⟨n1, n2, n3, hT1v, hT2v, hRv, -⟩ :=
    opt_l823_numerics (Xφ := Xφ) (Yφ := Yφ) (Xψ := Xψ) (Yψ := Yψ) (B := 0) hτpos hH0 hwX hzX hwz
  -- the regions
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
  -- their areas
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
  -- disjointness
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
  -- the inclusion `G \ R ⊆ 𝒩(K) \ H̆^R \ H̆^L`
  set N' := (niche K (π / 2) \ hRight φ K) \ hLeft φ K with hN'def
  have hsub : (G₀ ∪ T₁ ∪ T₂) \ R ⊆ N' := by
    rintro p ⟨hpG, hpR⟩
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
    have hp2 : 0 ≤ p.2 := by
      by_contra hneg
      push Not at hneg
      rw [hR] at hpR
      exact hpR ⟨k3, hneg, by linarith, by linarith⟩
    refine ⟨⟨⟨?_, ?_⟩, k1⟩, k2⟩
    · simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, opt_uvec_pi_div_two, opt_dot_mk]
      constructor <;> linarith
    · simp only [mem_iUnion]
      exact ⟨t, ht, hq⟩
  -- `N'` is bounded
  have hN'box : N' ⊆ Icc z w ×ˢ Icc 0 ((w - z) / (2 * τ)) := by
    rintro p ⟨⟨⟨hfan, -⟩, hnr⟩, hnl⟩
    have k1 := (hnR p).mp hnr
    have k2 := (hnL p).mp hnl
    have hp2 : 0 ≤ p.2 := by
      simp only [fan, halfPlus, mem_inter_iff, mem_ofPred_eq, opt_uvec_pi_div_two,
        opt_dot_mk] at hfan
      linarith [hfan.1]
    have hp2τ : 0 ≤ p.2 * τ := mul_nonneg hp2 hτpos.le
    refine ⟨⟨by linarith, by linarith⟩, hp2, ?_⟩
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hN'fin : MeasureTheory.volume N' ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
      (MeasureTheory.measure_mono hN'box)
  -- comparison of areas
  have hA0 := opt_integral_under_inner hcap.2.1 h2 hφ0 hψφ hψ2 H
  set B := ∫ t in φ..(π / 2 - φ), (deriv (innerCorner K) t).1 * (innerCorner K t).2 with hB
  have hA0v : 0 ≤ ∫ t in φ..(π / 2 - φ), -(deriv (innerCorner K) t).1 *
      ((innerCorner K t).2 + H) :=
    intervalIntegral.integral_nonneg hψφ.le fun t ht =>
      mul_nonneg (neg_nonneg.mpr (hX'neg t ht).le) (hYH t ht).le
  have hGfin : MeasureTheory.volume (G₀ ∪ T₁ ∪ T₂) ≠ ⊤ := by
    rw [vG, vG₀, vT₁, vT₂]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
  have hRfin : MeasureTheory.volume R ≠ ⊤ := by rw [vR]; exact ENNReal.ofReal_ne_top
  have hDfin : MeasureTheory.volume ((G₀ ∪ T₁ ∪ T₂) \ R) ≠ ⊤ :=
    ne_top_of_le_ne_top hN'fin (MeasureTheory.measure_mono hsub)
  have hdiff : area (G₀ ∪ T₁ ∪ T₂) ≤ area ((G₀ ∪ T₁ ∪ T₂) \ R) + area R := by
    unfold area
    rw [← ENNReal.toReal_add hDfin hRfin]
    apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hDfin, hRfin⟩)
    calc MeasureTheory.volume (G₀ ∪ T₁ ∪ T₂)
        ≤ MeasureTheory.volume (((G₀ ∪ T₁ ∪ T₂) \ R) ∪ R) := by
          apply MeasureTheory.measure_mono
          intro p hp
          by_cases h : p ∈ R
          · exact Or.inr h
          · exact Or.inl ⟨hp, h⟩
      _ ≤ _ := MeasureTheory.measure_union_le _ _
  have hmono : area ((G₀ ∪ T₁ ∪ T₂) \ R) ≤ area N' :=
    ENNReal.toReal_mono hN'fin (MeasureTheory.measure_mono hsub)
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
  -- the curve area functional
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
  have hpi := two_le_pi
  have hcap := hK.1
  obtain ⟨-, hBcb, hDcb, hBK, hDK, -, eB1, eB2, -, eD1, eD2⟩ := theorem8_1_8 hφ hK
  have h22 := lemma8_2_2 hφ hK
  have h23 := lemma8_2_3 hφ hK
  set N := niche K (π / 2) with hNdef
  set B := rightBody φ K with hBdef
  set D := leftBody φ K with hDdef
  -- decomposition of the niche
  have hRm : MeasurableSet (hRight φ K) := (opt_halfPlus_isClosed _ _).measurableSet
  have hLm : MeasurableSet (hLeft φ K) := (opt_halfPlus_isClosed _ _).measurableSet
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
  -- collinearity on `b_K^R`
  have hXB : xB φ B ∈ line φ (supp K φ - 1) := by
    have h1 := dot_vplus_uvec B (π + φ)
    have h2 : uvec (π + φ) = -uvec φ := by rw [add_comm, uvec_add_pi]
    rw [h2, dot_neg_right] at h1
    show dot (vplus B (π + φ)) (uvec φ) = supp K φ - 1
    linarith
  have hWl : wRight φ K ∈ line φ (supp K φ - 1) := by
    show dot (wRight φ K) (uvec φ) = supp K φ - 1
    simp only [opt_wRight_eq, dot, uvec, zero_mul, add_zero]
    field_simp
  have hxR : xRight φ K ∈ line φ (supp K φ - 1) := opt_innerCorner_dot_u K φ
  -- collinearity on `d_K^L`
  have hYD : yD φ D ∈ line (π / 2 - φ + π / 2) (supp K (π / 2 - φ + π / 2) - 1) := by
    have := dot_vminus_uvec D (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring, uvec_add_pi,
      dot_neg_right] at this
    have e : supp D (π / 2 - φ + π / 2 + π) = 1 - supp K (π / 2 - φ + π / 2) := by
      rw [show π / 2 - φ + π / 2 + π = 3 * π / 2 + (π / 2 - φ) by ring,
        show π / 2 - φ + π / 2 = π / 2 + (π / 2 - φ) by ring]
      linarith
    simp only [line, mem_ofPred_eq, yD]
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring]
    linarith
  have hZl : zLeft φ K ∈ line (π / 2 - φ + π / 2) (supp K (π / 2 - φ + π / 2) - 1) := by
    simp only [line, mem_ofPred_eq, opt_zLeft_eq]
    rw [uvec_add_pi_div_two, show π / 2 - φ + π / 2 = π - φ by ring]
    simp only [dot, vvec, sin_pi_div_two_sub, zero_mul, add_zero]
    field_simp
    ring
  have hxL : xLeft φ K ∈ line (π / 2 - φ + π / 2) (supp K (π / 2 - φ + π / 2) - 1) := by
    simp only [line, mem_ofPred_eq, xLeft, uvec_add_pi_div_two]
    exact opt_innerCorner_dot_v K _
  have c1 := opt_segArea_collinear hXB hWl hxR
  have c2 := opt_segArea_collinear hxL hZl hYD
  have s1 := opt_segArea_swap (xRight φ K) (xB φ B)
  have s2 := opt_segArea_swap (yD φ D) (xLeft φ K)
  unfold sofaArea upperQ
  linarith [h22.1, h22.2, h23]

end MovingSofa
