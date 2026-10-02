module

public import MovingSofa.Optimality.UpperBound
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Concavity of `𝒬` (§8.3)

Definitions 8.3.1–8.3.4, Theorems 8.3.1–8.3.2, Lemmas 8.3.3–8.3.7 and Theorem 8.3.8
(`thm:upper-bound-concave`).

**Reading of Definition 8.3.3.** The paper writes `ℛ_B = 𝓜_B(π/2 + φ^R, 3π/2; 𝐥_B^{3π/2})`; the tail
`𝐛_B` and Lemma 8.3.4 use the interval `(π + φ^R, 3π/2)`, which we use.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped Pointwise

namespace MovingSofa

attribute [local simp] opt_dot_mk

/-! ### Lebesgue–Stieltjes measures of continuous curves (package I) -/

section LSAux

variable {x y : ℝ → ℝ × ℝ} {a b : ℝ}

lemma opt_clamp_mem (hab : a ≤ b) (s : ℝ) : max a (min b s) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma opt_clampFun_eqOn {α : Type*} (f : ℝ → α) :
    EqOn (clampFun f a b) f (Icc a b) := by
  intro s hs
  simp only [clampFun, min_eq_right hs.2, max_eq_right hs.1]

lemma opt_clampFun_continuous {E : Type*} [TopologicalSpace E] {f : ℝ → E} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : Continuous (clampFun f a b) :=
  hf.comp_continuous (by fun_prop) (opt_clamp_mem hab)

lemma opt_clampFun_bv {E : Type*} [PseudoEMetricSpace E] {f : ℝ → E} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) : BoundedVariationOn (clampFun f a b) univ := by
  have hmono : MonotoneOn (fun t : ℝ => max a (min b t)) univ :=
    fun s _ t _ hst => max_le_max le_rfl (min_le_min le_rfl hst)
  exact ne_top_of_le_ne_top hf
    (eVariationOn.comp_le_of_monotoneOn f (fun t => max a (min b t)) hmono
      (fun t _ => opt_clamp_mem hab t))

lemma opt_lsMeasure_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) :
    lsMeasure f a b = (opt_clampFun_bv hab hf).vectorMeasure := by
  rw [lsMeasure, dite_eq_left_of_eq_true (eq_true (opt_clampFun_bv hab hf))]

lemma opt_rightLim_eq {E : Type*} [TopologicalSpace E] [T2Space E] {f : ℝ → E} (hf : Continuous f)
    (s : ℝ) : Function.rightLim f s = f s :=
  rightLim_eq_of_tendsto ((hf.tendsto s).mono_left nhdsWithin_le_nhds)

lemma opt_leftLim_eq {E : Type*} [TopologicalSpace E] [T2Space E] {f : ℝ → E} (hf : Continuous f)
    (s : ℝ) : Function.leftLim f s = f s :=
  leftLim_eq_of_tendsto ((hf.tendsto s).mono_left nhdsWithin_le_nhds)

/-- The Lebesgue–Stieltjes measure of a continuous curve of bounded variation on intervals. -/
lemma opt_lsMeasure_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hf : BoundedVariationOn f (Icc a b))
    {c d : ℝ} (hcd : c ≤ d) :
    lsMeasure f a b (Icc c d) = clampFun f a b d - clampFun f a b c := by
  rw [opt_lsMeasure_eq hab hf, BoundedVariationOn.vectorMeasure_Icc _ hcd,
    opt_rightLim_eq (opt_clampFun_continuous hab hfc), opt_leftLim_eq (opt_clampFun_continuous hab hfc)]

/-- An integral against a vector measure vanishes if the pairing kills all the values of the
measure. -/
lemma opt_integral_eq_zero_of_pairing {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}
    (h : ∀ s r, B r (μ s) = 0) (f : X → E) : ∫ᵛ x, f x ∂[B; μ] = 0 := by
  rw [VectorMeasure.integral_eq_setToFun]
  apply setToFun_zero_left'
  intro s _ _
  ext r
  exact h s r


lemma opt_integrable_restrict_Icc {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : VectorMeasure ℝ F}
    [IsFiniteMeasure μ.variation] {f : ℝ → E} (hf : ContinuousOn f (Icc a b)) :
    (μ.restrict (Icc a b)).Integrable f := by
  show Integrable f (μ.restrict (Icc a b)).variation
  rw [VectorMeasure.variation_restrict measurableSet_Icc]
  exact hf.integrableOn_compact isCompact_Icc

/-- The curve area functional of a curve running along a line `s ↦ P + Λ(s) w`. -/
lemma opt_curveArea_line (hab : a ≤ b) {P w : ℝ × ℝ} {Λ : ℝ → ℝ}
    (hΛc : ContinuousOn Λ (Icc a b)) (hΛ : BoundedVariationOn Λ (Icc a b))
    (hx : ∀ s ∈ Icc a b, x s = P + Λ s • w) :
    curveArea x a b = (Λ b - Λ a) * cross P w / 2 := by
  set y : ℝ → ℝ × ℝ := fun s => P + Λ s • w with hy
  rw [opt_curveArea_congr hab (y := y) hx]
  have hA : LipschitzWith (‖w‖₊) (fun r : ℝ => P + r • w) :=
    LipschitzWith.of_dist_le_mul fun r r' => by
      rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]
      simp
  have hyc : ContinuousOn y (Icc a b) := hA.continuous.comp_continuousOn hΛc
  have hyb : BoundedVariationOn y (Icc a b) :=
    hA.comp_boundedVariationOn hΛ
  have hfin := opt_clampFun_bv hab hyb
  set L : (ℝ × ℝ) →L[ℝ] ℝ := crossCLM w with hL
  have hzero : (lsMeasure y a b).mapRange L.toLinearMap.toAddMonoidHom
      (by exact L.continuous) = 0 := by
    apply VectorMeasure.ext_of_Icc
    intro c d hcd
    show L (lsMeasure y a b (Icc c d)) = 0
    rw [opt_lsMeasure_Icc hab hyc hyb hcd]
    simp only [clampFun, hy, hL, crossCLM_apply, cross, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hline : ∀ S, cross w (lsMeasure y a b S) = 0 := by
    intro S
    have := congrArg (fun ν : VectorMeasure ℝ ℝ => ν S) hzero
    exact this
  have hI : ∀ S, cross w ((lsMeasure y a b).restrict (Icc a b) S) = 0 := by
    intro S
    by_cases hS : MeasurableSet S
    · rw [VectorMeasure.restrict_apply _ measurableSet_Icc hS]; exact hline _
    · rw [VectorMeasure.not_measurable _ hS]; simp [cross]
  rw [opt_lsMeasure_eq hab hyb] at hI
  unfold curveArea curveBilin
  rw [opt_lsMeasure_eq hab hyb]
  set C : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight w with hC
  have hsplit : (fun s => y s) = fun s => (fun _ => P) s + C (Λ s) := by
    funext s; simp [hy, hC]
  have hPi : (hfin.vectorMeasure.restrict (Icc a b)).Integrable (fun _ : ℝ => P) :=
    opt_integrable_restrict_Icc continuousOn_const
  have hΛi : (hfin.vectorMeasure.restrict (Icc a b)).Integrable Λ :=
    opt_integrable_restrict_Icc hΛc
  have hCi : (hfin.vectorMeasure.restrict (Icc a b)).Integrable (fun s => C (Λ s)) :=
    opt_integrable_restrict_Icc (C.continuous.comp_continuousOn hΛc)
  rw [hsplit, VectorMeasure.integral_fun_add hPi hCi, VectorMeasure.setIntegral_const,
    VectorMeasure.integral_continuousLinearMap_comp hΛi,
    opt_integral_eq_zero_of_pairing (B := crossCLM ∘L C) (fun S r => by
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hC,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, crossCLM_apply,
        cross_smul_left]
      rw [hI S, mul_zero]) Λ, add_zero, ← opt_lsMeasure_eq hab hyb,
    opt_lsMeasure_Icc hab hyc hyb hab]
  simp only [crossCLM_apply, clampFun, hy, min_self, max_eq_right hab, min_eq_right hab,
    max_self, cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

end LSAux

/-- The parametrization `𝐥_K^t : (t - π, t] → ℝ²` of the supporting line `l_K(t)`:
`𝐥_K^t(s) = v_K(s, t)` for `s < t` and `𝐥_K^t(t) = v_K⁻(t)` (Definition 8.3.1). -/
noncomputable def tangentParam (K : Set (ℝ × ℝ)) (t s : ℝ) : ℝ × ℝ :=
  if s < t then vint K s t else vminus K t

/-! ### The tangent line parametrization (package I) -/

lemma opt_vint_dot_vvec (K : Set (ℝ × ℝ)) {s t : ℝ} (hst : sin (t - s) ≠ 0) :
    dot (vint K s t) (vvec t) = (supp K t * cos (t - s) - supp K s) / sin (t - s) := by
  simp only [vint, dot_add_left, dot_smul_left, dot_uvec_vvec', dot_vvec_vvec]
  rw [show sin (s - t) = -sin (t - s) by rw [← sin_neg, neg_sub],
    show cos (s - t) = cos (t - s) by rw [← cos_neg, neg_sub]]
  field_simp
  linear_combination (-supp K s) * sin_sq_add_cos_sq (t - s)

lemma opt_tangentParam_dot_uvec (K : Set (ℝ × ℝ)) {s t : ℝ} (hs : s ∈ Ioc (t - π) t) :
    dot (tangentParam K t s) (uvec t) = supp K t := by
  by_cases hst : s < t
  · simp only [tangentParam, hst, ↓reduceIte]
    exact vint_mem_line_right K (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs.1])).ne'
  · simp only [tangentParam, hst, ↓reduceIte]
    exact dot_vminus_uvec K t

lemma opt_tangentParam_eq (K : Set (ℝ × ℝ)) {s t : ℝ} (hs : s ∈ Ioc (t - π) t) :
    tangentParam K t s = supp K t • uvec t + dot (tangentParam K t s) (vvec t) • vvec t := by
  conv_lhs => rw [eq_dot_uvec_smul_add (tangentParam K t s) t]
  rw [opt_tangentParam_dot_uvec K hs]

/-- The position of `𝐥_K^t(s)` along `l_K(t)` is monotone in `s ∈ (t - π, t]`. -/
lemma opt_tangentParam_mono {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    MonotoneOn (fun s => dot (tangentParam K t s) (vvec t)) (Ioc (t - π) t) := by
  intro s₁ hs₁ s₂ hs₂ h12
  rcases eq_or_lt_of_le h12 with h | h12
  · rw [h]
  have hs1t : s₁ < t := lt_of_lt_of_le h12 hs₂.2
  have hS1 : 0 < sin (t - s₁) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs₁.1])
  simp only [tangentParam, hs1t, ↓reduceIte]
  rw [opt_vint_dot_vvec K hS1.ne']
  rcases eq_or_lt_of_le hs₂.2 with h2 | h2
  · rw [h2]
    simp only [lt_irrefl, ↓reduceIte]
    have hQ := (vminus_mem_edge hK t).1
    have hQu := dot_vminus_uvec K t
    have hle := dot_le_supp hK.2.1 hQ s₁
    have e := opt_dot_frame_u (vminus K t) s₁ t
    rw [hQu, show s₁ - t = -(t - s₁) by ring, cos_neg, sin_neg] at e
    rw [div_le_iff₀ hS1]
    nlinarith
  · have hS2 : 0 < sin (t - s₂) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs₂.1])
    have hS21 : 0 < sin (s₂ - s₁) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs₁.1])
    simp only [h2, ↓reduceIte]
    rw [opt_vint_dot_vvec K hS2.ne', div_le_div_iff₀ hS1 hS2]
    have key : ∀ p : ℝ × ℝ, dot p (uvec s₂) * sin (t - s₁) =
        sin (t - s₂) * dot p (uvec s₁) + sin (s₂ - s₁) * dot p (uvec t) := by
      intro p; simp only [dot, uvec, sin_sub]; ring
    have hsub : supp K s₂ ≤ (supp K s₁ * sin (t - s₂) + supp K t * sin (s₂ - s₁)) / sin (t - s₁) := by
      show sSup _ ≤ _
      refine csSup_le (hK.1.image _) ?_
      rintro _ ⟨p, hp, rfl⟩
      rw [le_div_iff₀ hS1, key p]
      nlinarith [dot_le_supp hK.2.1 hp s₁, dot_le_supp hK.2.1 hp t]
    rw [le_div_iff₀ hS1] at hsub
    have e : cos (t - s₂) * sin (t - s₁) - cos (t - s₁) * sin (t - s₂) = sin (s₂ - s₁) := by
      have := sin_sub (t - s₁) (t - s₂)
      rw [show t - s₁ - (t - s₂) = s₂ - s₁ by ring] at this
      linarith
    have e2 : (supp K t * cos (t - s₂) - supp K s₂) * sin (t - s₁) -
        (supp K t * cos (t - s₁) - supp K s₁) * sin (t - s₂) =
        supp K t * (cos (t - s₂) * sin (t - s₁) - cos (t - s₁) * sin (t - s₂)) +
          supp K s₁ * sin (t - s₂) - supp K s₂ * sin (t - s₁) := by ring
    rw [e] at e2
    linarith

lemma opt_tangentParam_dot_continuousOn {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t a b : ℝ}
    (ha : t - π < a) (hb : b ≤ t) :
    ContinuousOn (fun s => dot (tangentParam K t s) (vvec t)) (Icc a b) := by
  have hsupp := continuous_supp hK.2.1 hK.1
  intro s hs
  rcases lt_or_eq_of_le (hs.2.trans hb) with hst | hst
  · have hS : 0 < sin (t - s) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hs.1])
    have hcont : ContinuousAt (fun r => (supp K t * cos (t - r) - supp K r) / sin (t - r)) s :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hS.ne'
    have heq : (fun r => (supp K t * cos (t - r) - supp K r) / sin (t - r)) =ᶠ[𝓝 s]
        (fun r => dot (tangentParam K t r) (vvec t)) := by
      filter_upwards [Iio_mem_nhds hst, Ioi_mem_nhds (by linarith [hs.1] : t - π < s)] with r hr1 hr2
      simp only [tangentParam, (show r < t from hr1), ↓reduceIte]
      rw [opt_vint_dot_vvec K (sin_pos_of_pos_of_lt_pi (by linarith [show r < t from hr1])
        (by linarith [show t - π < r from hr2])).ne']
    exact (hcont.congr heq).continuousWithinAt
  · have hlim : Tendsto (fun r => dot (tangentParam K t r) (vvec t)) (𝓝[<] t)
        (𝓝 (dot (tangentParam K t t) (vvec t))) := by
      have h1 := tendsto_vint_left hK t
      have hd : Continuous fun p : ℝ × ℝ => dot p (vvec t) := by unfold dot; fun_prop
      have h2 := (hd.tendsto _).comp h1
      simp only [tangentParam, lt_irrefl, ↓reduceIte]
      apply h2.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [Function.comp_apply, (show r < t from hr), ↓reduceIte]
    have hcw : ContinuousWithinAt (fun r => dot (tangentParam K t r) (vvec t)) (Iio t) t := hlim
    rw [continuousWithinAt_Iio_iff_Iic] at hcw
    rw [hst]
    exact hcw.mono fun r hr => hr.2.trans hb


/-- **Theorem 8.3.1** (`thm:tangent-line-parametrization`). For `a ≤ b` in `(t - π, t]`, `𝐥_K^t`
restricted to `[a, b]` is a continuous parametrization of bounded variation of the segment from
`𝐥_K^t(a)` to `𝐥_K^t(b)`, and `𝒥(𝐥_K^t|_{[a,b]}) = 𝒥(𝐥_K^t(a), 𝐥_K^t(b))`. -/
theorem theorem8_3_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t a b : ℝ} (ha : t - π < a)
    (hab : a ≤ b) (hb : b ≤ t) :
    IsCBV (tangentParam K t) a b ∧
      tangentParam K t '' Icc a b = segment ℝ (tangentParam K t a) (tangentParam K t b) ∧
      curveArea (tangentParam K t) a b = segArea (tangentParam K t a) (tangentParam K t b) := by
  set lam : ℝ → ℝ := fun s => dot (tangentParam K t s) (vvec t) with hlam
  set A : ℝ → ℝ × ℝ := fun r => supp K t • uvec t + r • vvec t with hA
  have hIoc : Icc a b ⊆ Ioc (t - π) t := fun s hs => ⟨by linarith [hs.1], hs.2.trans hb⟩
  have heq : EqOn (tangentParam K t) (fun s => A (lam s)) (Icc a b) := fun s hs =>
    opt_tangentParam_eq K (hIoc hs)
  have hmono : MonotoneOn lam (Icc a b) := (opt_tangentParam_mono hK t).mono hIoc
  have hcont : ContinuousOn lam (Icc a b) := opt_tangentParam_dot_continuousOn hK ha hb
  have hbv : BoundedVariationOn lam (Icc a b) := by
    have := hmono.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rwa [inter_self] at this
  have hAlip : LipschitzWith (‖vvec t‖₊) A :=
    LipschitzWith.of_dist_le_mul fun r r' => by
      rw [hA, dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm]
      simp
  have hAc : Continuous A := hAlip.continuous
  have hAaff : A = AffineMap.lineMap (supp K t • uvec t) (supp K t • uvec t + vvec t) := by
    funext r
    rw [AffineMap.lineMap_apply, hA]
    simp only [vadd_eq_add, vsub_eq_sub, add_sub_cancel_left]
    abel
  refine ⟨⟨(hAc.comp_continuousOn hcont).congr heq, ?_⟩, ?_, ?_⟩
  · show eVariationOn _ _ ≠ ⊤
    rw [eVariationOn.eq_of_eqOn heq]
    exact hAlip.comp_boundedVariationOn hbv
  · have himg : lam '' Icc a b = Icc (lam a) (lam b) := by
      apply Subset.antisymm
      · rintro _ ⟨s, hs, rfl⟩
        exact ⟨hmono ⟨le_rfl, hab⟩ hs hs.1, hmono hs ⟨hab, le_rfl⟩ hs.2⟩
      · exact intermediate_value_Icc hab hcont
    rw [heq.image_eq, heq ⟨le_rfl, hab⟩, heq ⟨hab, le_rfl⟩,
      show (fun s => A (lam s)) '' Icc a b = A '' (lam '' Icc a b) from (image_image _ _ _).symm,
      himg, ← segment_eq_Icc (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab), hAaff, image_segment]
  · rw [opt_curveArea_line hab hcont hbv heq, heq ⟨le_rfl, hab⟩, heq ⟨hab, le_rfl⟩]
    simp only [hA, segArea, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring

/-- **Theorem 8.3.2** (`thm:tangent-line-param-linear`). `𝐥_K^t|_{[a,b]}` is convex-linear in `K`. -/
theorem theorem8_3_2 {t a b : ℝ} (ha : t - π < a) (hab : a ≤ b) (hb : b ≤ t)
    (K₁ K₂ : ConvexBodySet) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : s ∈ Icc a b) :
    tangentParam (convexBodyComb c K₁ K₂).1 t s =
      (1 - c) • tangentParam K₁.1 t s + c • tangentParam K₂.1 t s := by
  have _ := hab
  have hst : s ≤ t := hs.2.trans hb
  rcases lt_or_eq_of_le hst with h | h
  · simp only [tangentParam, h, ↓reduceIte]
    exact (theorem7_1_2_vertices s t h (by linarith [hs.1])).2.2 c hc K₁ K₂
  · rw [h]
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
    exact opt_vminus_linear t c hc K₁ K₂

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
  obtain ⟨E, i1, i2, e, he, hlin⟩ := theorem7_1_1
  refine ⟨E, i1, i2, fun K => e K.1, fun K L h => Subtype.ext (he h), fun c hc v w => ?_⟩
  simp only [kiComb, hc, ↓reduceDIte]
  exact hlin c hc v.1 w.1

/-- The convex domain `𝒦^i` (Theorem 8.1.1 (1)). -/
noncomputable def kiDomain : ConvexDomain KiSet where
  comb := kiComb
  embeds := kiSet_embeds

/-! ### Convex functionals (package I) -/

section ConvexFunAux

variable {U V : Type}

lemma opt_isConvexFun_add {D : ConvexDomain U} {f g : U → ℝ} (hf : D.IsConvexFun f)
    (hg : D.IsConvexFun g) : D.IsConvexFun (fun v => f v + g v) := fun K₁ K₂ c hc => by
  have h1 := hf K₁ K₂ c hc
  have h2 := hg K₁ K₂ c hc
  linarith

lemma opt_isConvexFun_comp {D₁ : ConvexDomain U} {D₂ : ConvexDomain V} {pr : U → V}
    (hpr : D₁.IsConvexLinear D₂ pr) {f : V → ℝ} (hf : D₂.IsConvexFun f) :
    D₁.IsConvexFun (fun v => f (pr v)) := fun K₁ K₂ c hc => by
  simp only [hpr c hc]
  exact hf _ _ c hc

end ConvexFunAux

lemma opt_projKi_linear : kiDomain.IsConvexLinear convexBodyDomain (fun K : KiSet => K.1) := by
  intro c hc K₁ K₂
  show (kiComb c K₁ K₂).1 = convexBodyComb c K₁.1 K₂.1
  simp only [kiComb, hc, ↓reduceDIte]

/-- Mamikon's area with the tangent line parametrization is convex and quadratic. -/
lemma opt_mamikon_tangent {t a b : ℝ} (hab : a < b) (hb : b < a + π) (ha : t - π < a)
    (hbt : b ≤ t) :
    convexBodyDomain.IsQuadratic (fun K => mamikon K.1 a b (tangentParam K.1 t)) ∧
      convexBodyDomain.IsConvexFun (fun K => mamikon K.1 a b (tangentParam K.1 t)) := by
  apply theorem7_4_2 hab hb (fun K => tangentParam K.1 t)
  · intro K
    exact (theorem8_3_1 K.2 ha hab.le hbt).1
  · intro K s hs
    by_cases hst : s < t
    · simp only [tangentParam, hst, ↓reduceIte]
      exact vint_mem_line_left K.1 s t
    · have : s = t := le_antisymm (hs.2.trans hbt) (not_lt.mp hst)
      subst this
      simp only [tangentParam, lt_irrefl, ↓reduceIte]
      exact dot_vminus_uvec K.1 s
  · intro K₁ K₂ c hc s hs
    exact theorem8_3_2 ha hab.le hbt K₁ K₂ hc s hs

/-- Mamikon's area with the outer corner is convex and quadratic. -/
lemma opt_mamikon_outer {a b : ℝ} (hab : a < b) (hb : b < a + π) :
    convexBodyDomain.IsQuadratic (fun K => mamikon K.1 a b (outerCorner K.1)) ∧
      convexBodyDomain.IsConvexFun (fun K => mamikon K.1 a b (outerCorner K.1)) := by
  apply theorem7_4_2 hab hb (fun K => outerCorner K.1)
  · intro K
    exact opt_outerCorner_cbv K.2 a b
  · intro K s _
    show dot (outerCorner K.1 s) (uvec s) = supp K.1 s
    rw [proposition2_2_2_outerCorner]
    simp [dot_add_left, dot_smul_left]
  · intro K₁ K₂ c hc s _
    show outerCorner (convexBodyComb c K₁ K₂).1 s = _
    rw [opt_convexBodyComb_val hc, opt_outerCorner_comb K₁.2 K₂.2 hc]
    rfl

/-- **Lemma 8.3.3** (`lem:mamikon-sofa-convex`). `𝒮_K`, `ℛ_B` and `ℒ_D` are convex quadratic
functionals of `K ∈ 𝒦^i`, `B ∈ 𝒦` and `D ∈ 𝒦`. -/
theorem lemma8_3_3 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.IsQuadratic (fun K => mamikonS φ K.1.1) ∧ kiDomain.IsConvexFun (fun K => mamikonS φ K.1.1) ∧
      convexBodyDomain.IsQuadratic (fun B => mamikonR φ B.1) ∧
      convexBodyDomain.IsConvexFun (fun B => mamikonR φ B.1) ∧
      convexBodyDomain.IsQuadratic (fun D => mamikonL φ D.1) ∧
      convexBodyDomain.IsConvexFun (fun D => mamikonL φ D.1) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  obtain ⟨q1, c1⟩ := opt_mamikon_tangent (t := π / 2) (a := 0) (b := φ) hφ0 (by linarith)
    (by linarith) (by linarith)
  obtain ⟨q2, c2⟩ := opt_mamikon_outer (a := φ) (b := π / 2 - φ) (by linarith) (by linarith)
  obtain ⟨q3, c3⟩ := opt_mamikon_tangent (t := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨q4, c4⟩ := opt_mamikon_tangent (t := π) (a := π / 2) (b := π) (by linarith)
    (by linarith) (by linarith) le_rfl
  obtain ⟨qR, cR⟩ := opt_mamikon_tangent (t := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) (by linarith) le_rfl
  obtain ⟨qL, cL⟩ := opt_mamikon_tangent (t := 3 * π / 2 + (π / 2 - φ)) (a := 3 * π / 2)
    (b := 3 * π / 2 + (π / 2 - φ)) (by linarith) (by linarith) (by linarith) le_rfl
  refine ⟨?_, ?_, qR, cR, qL, cL⟩
  · exact opt_isQuadratic_comp opt_projKi_linear
      (opt_isQuadratic_add (opt_isQuadratic_add (opt_isQuadratic_add q1 q2) q3) q4)
  · exact opt_isConvexFun_comp opt_projKi_linear
      (opt_isConvexFun_add (opt_isConvexFun_add (opt_isConvexFun_add c1 c2) c3) c4)

/-- `𝒫_K = |K| + 𝒥(Z_K^L, 𝐱_K^L) - 𝒥(𝐱_K|_{[φ^R, φ^L]}) + 𝒥(𝐱_K^R, W_K^R)` (Definition 8.3.4,
`def:upper-bound-middle`). -/
noncomputable def upperP (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  area K + segArea (zLeft φ K) (xLeft φ K) - curveArea (innerCorner K) φ (π / 2 - φ) +
    segArea (xRight φ K) (wRight φ K)

/-- The corner `v_B(π + φ, 3π/2)` is `W_K^R` when `l_B(π + φ) = b_K(φ)` and `l_B(3π/2) = l(π/2, 0)`. -/
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

/-- The corner `v_D(3π/2, 3π/2 + φ^L)` is `Z_K^L` under the analogous conditions. -/
lemma opt_vint_left_eq {φ : ℝ} {K D : Set (ℝ × ℝ)}
    (hD3 : supp D (3 * π / 2) = 0)
    (hDb : supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ)) :
    vint D (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) = zLeft φ K := by
  rw [opt_zLeft_eq]
  simp only [vint, hD3, hDb, show 3 * π / 2 + (π / 2 - φ) - 3 * π / 2 = π / 2 - φ by ring,
    sin_pi_div_two_sub, opt_vvec_three_pi_div_two, zero_smul, zero_add, zero_mul, sub_zero]
  ext <;> simp

/-- **Lemma 8.3.4** (`lem:upper-bound-decomposition`). On `𝓛`, `𝒬(K, B, D) = 𝒫_K - ℛ_B - ℒ_D`. -/
theorem lemma8_3_4 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    upperQ φ K B D = upperP φ K - mamikonR φ B - mamikonL φ D := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  obtain ⟨hK, hBcb, hDcb, -, -, -, eB1, eB2, -, eD1, eD2⟩ := h
  have hcap := hK.1
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hBa : supp B (π + φ) = 1 - supp K φ := by linarith
  have hB3 : supp B (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π + π / 2 by ring]; linarith [hcap.2.2.2.1]
  have hD3 : supp D (3 * π / 2) = 0 := by
    simp only [add_zero] at eD1; linarith [hcap.2.2.2.1]
  have hDb : supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
    rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at eD2; linarith
  have hvR := opt_vint_right_eq hφ2 hBa hB3
  have hvL := opt_vint_left_eq hD3 hDb
  -- the tangent line pieces
  have hlR := (theorem8_3_1 hBcb (t := 3 * π / 2) (a := π + φ) (b := 3 * π / 2) (by linarith)
    (by linarith) le_rfl).2.2
  have hlL := (theorem8_3_1 hDcb (t := 3 * π / 2 + (π / 2 - φ)) (a := 3 * π / 2)
    (b := 3 * π / 2 + (π / 2 - φ)) (by linarith) (by linarith) le_rfl).2.2
  have tR1 : tangentParam B (3 * π / 2) (π + φ) = wRight φ K := by
    simp only [tangentParam, show π + φ < 3 * π / 2 by linarith, ↓reduceIte]; exact hvR
  have tR2 : tangentParam B (3 * π / 2) (3 * π / 2) = vminus B (3 * π / 2) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have tL1 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2) = zLeft φ K := by
    simp only [tangentParam, show 3 * π / 2 < 3 * π / 2 + (π / 2 - φ) by linarith, ↓reduceIte]
    exact hvL
  have tL2 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2 + (π / 2 - φ)) =
      vminus D (3 * π / 2 + (π / 2 - φ)) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  rw [tR1, tR2] at hlR
  rw [tL1, tL2] at hlL
  -- points on the `x`-axis
  have hWB : (vminus B (3 * π / 2)).2 = 0 := by
    have := dot_vminus_uvec B (3 * π / 2)
    rw [hB3, opt_uvec_three_pi_div_two] at this
    simp at this; linarith
  have hZD : (vplus D (3 * π / 2)).2 = 0 := by
    have := dot_vplus_uvec D (3 * π / 2)
    rw [hD3, opt_uvec_three_pi_div_two] at this
    simp at this; linarith
  have hW2 : (wRight φ K).2 = 0 := rfl
  have hZ2 : (zLeft φ K).2 = 0 := by rw [opt_zLeft_eq]
  -- collinearity on `b_K^R` and on `d_K^L`
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
  have hYD : yD φ D ∈ line (π / 2 - φ + π / 2) (supp K (π / 2 - φ + π / 2) - 1) := by
    have := dot_vminus_uvec D (3 * π / 2 + (π / 2 - φ))
    rw [show 3 * π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 + π by ring, uvec_add_pi,
      dot_neg_right] at this
    have e : supp D (π / 2 - φ + π / 2 + π) = 1 - supp K (π / 2 - φ + π / 2) := by
      rw [show π / 2 - φ + π / 2 + π = 3 * π / 2 + (π / 2 - φ) by ring,
        show π / 2 - φ + π / 2 = π - φ by ring]
      exact hDb
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
  have c1 := opt_segArea_collinear hxR hXB hWl
  have c2 := opt_segArea_collinear hZl hYD hxL
  have z1 := opt_segArea_xaxis hW2 hWB
  have z2 := opt_segArea_xaxis hZD hZ2
  have z3 := opt_segArea_self (vminus B (3 * π / 2))
  have z4 := opt_segArea_self (vminus D (3 * π / 2 + (π / 2 - φ)))
  simp only [upperQ, upperP, mamikonR, mamikonL, mamikon, hlR, hlL, tR1, tR2, tL1, tL2]
  simp only [xB, yD] at c1 c2 ⊢
  linarith

/-! ### Auxiliary facts for Lemmas 8.3.5–8.3.7 (package I) -/

lemma opt_outer_eq_inner_add (K : Set (ℝ × ℝ)) (t : ℝ) :
    outerCorner K t = innerCorner K t + (uvec t + vvec t) := by
  rw [proposition2_2_2_outerCorner, proposition2_2_2_innerCorner]
  ext <;> simp <;> ring

lemma opt_hasDerivAt_uvec (t : ℝ) : HasDerivAt uvec (vvec t) t :=
  (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)

lemma opt_hasDerivAt_vvec (t : ℝ) : HasDerivAt vvec (-uvec t) t :=
  (Real.hasDerivAt_sin t).neg.prodMk (Real.hasDerivAt_cos t)

lemma opt_continuousOn_cross {f g : ℝ → ℝ × ℝ} {S : Set ℝ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) : ContinuousOn (fun t => cross (f t) (g t)) S := by
  unfold cross
  exact ((continuous_fst.comp_continuousOn hf).mul (continuous_snd.comp_continuousOn hg)).sub
    ((continuous_snd.comp_continuousOn hf).mul (continuous_fst.comp_continuousOn hg))

lemma opt_kiComb_val {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K₁ K₂ : KiSet) :
    (kiComb c K₁ K₂).1.1 = (1 - c) • K₁.1.1 + c • K₂.1.1 := by
  simp [kiComb, hc, convexBodyComb]

/-- The integrand of `𝒥(𝐲_K|_{[a,b]}) - 𝒥(𝐱_K|_{[a,b]})`. -/
noncomputable def opt_outerInnerIntegrand (K : Set (ℝ × ℝ)) (a b t : ℝ) : ℝ :=
  cross (innerCorner K t) (vvec t - uvec t) +
    cross (uvec t + vvec t) (derivWithin (innerCorner K) (Icc a b) t) +
    cross (uvec t + vvec t) (vvec t - uvec t)

lemma opt_outer_sub_inner {K : Set (ℝ × ℝ)} (h2 : InjCond2 K) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ π / 2) :
    curveArea (outerCorner K) a b - curveArea (innerCorner K) a b =
      (1 / 2) * ∫ t in a..b, opt_outerInnerIntegrand K a b t := by
  have hxI : ContDiffOn ℝ 1 (innerCorner K) (Icc a b) := h2.mono (Icc_subset_Icc ha hb)
  have hc : ContDiff ℝ 1 (fun t => uvec t + vvec t) := by unfold uvec vvec; fun_prop
  have hy : outerCorner K = fun t => innerCorner K t + (uvec t + vvec t) :=
    funext (opt_outer_eq_inner_add K)
  have hyI : ContDiffOn ℝ 1 (outerCorner K) (Icc a b) := by
    rw [hy]; exact hxI.add hc.contDiffOn
  have hu : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hdy : ∀ t ∈ Icc a b, derivWithin (outerCorner K) (Icc a b) t =
      derivWithin (innerCorner K) (Icc a b) t + (vvec t - uvec t) := by
    intro t ht
    rw [hy, derivWithin_fun_add (hxI.differentiableOn one_ne_zero t ht)
      (hc.differentiable one_ne_zero t).differentiableWithinAt,
      ((opt_hasDerivAt_uvec t).fun_add (opt_hasDerivAt_vvec t)).hasDerivWithinAt.derivWithin (hu t ht)]
    abel
  have hxc := hxI.continuousOn
  have hxd := hxI.continuousOn_derivWithin hu le_rfl
  have hyc := hyI.continuousOn
  have hyd := hyI.continuousOn_derivWithin hu le_rfl
  have i1 : IntervalIntegrable (fun t => cross (outerCorner K t)
      (derivWithin (outerCorner K) (Icc a b) t)) MeasureTheory.volume a b := by
    exact (opt_continuousOn_cross hyc hyd).intervalIntegrable_of_Icc hab.le
  have i2 : IntervalIntegrable (fun t => cross (innerCorner K t)
      (derivWithin (innerCorner K) (Icc a b) t)) MeasureTheory.volume a b := by
    exact (opt_continuousOn_cross hxc hxd).intervalIntegrable_of_Icc hab.le
  rw [curveArea_eq_integral hab.le hyI, curveArea_eq_integral hab.le hxI, ← mul_sub,
    ← intervalIntegral.integral_sub i1 i2]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab.le] at ht
  simp only [opt_outerInnerIntegrand]
  rw [hdy t ht, opt_outer_eq_inner_add]
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

lemma opt_outerInnerIntegrand_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (i₁ : InjCond2 K₁) (i₂ : InjCond2 K₂) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ π / 2) {t : ℝ} (ht : t ∈ Icc a b) :
    opt_outerInnerIntegrand ((1 - c) • K₁ + c • K₂) a b t =
      (1 - c) * opt_outerInnerIntegrand K₁ a b t + c * opt_outerInnerIntegrand K₂ a b t := by
  have hx1 : DifferentiableWithinAt ℝ (innerCorner K₁) (Icc a b) t :=
    ((i₁.mono (Icc_subset_Icc ha hb)).differentiableOn one_ne_zero) t ht
  have hx2 : DifferentiableWithinAt ℝ (innerCorner K₂) (Icc a b) t :=
    ((i₂.mono (Icc_subset_Icc ha hb)).differentiableOn one_ne_zero) t ht
  simp only [opt_outerInnerIntegrand]
  rw [opt_innerCorner_comb h₁ h₂ hc, derivWithin_add (hx1.const_smul (1 - c)) (hx2.const_smul c),
    derivWithin_const_smul _ hx1, derivWithin_const_smul _ hx2]
  simp only [Pi.add_apply, Pi.smul_apply, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `𝐥_K^{π/2}(φ) = W_K(φ) + ((1 - sin φ)/cos φ, 1)` for a cap. -/
lemma opt_tangent_right_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) {K : Set (ℝ × ℝ)}
    (h1 : supp K (π / 2) = 1) :
    tangentParam K (π / 2) φ = wRight φ K + ((1 - sin φ) / cos φ, 1) := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], hφ.2⟩
  have e := sin_sq_add_cos_sq φ
  simp only [tangentParam, hφ.2, ↓reduceIte, vint, h1, cos_pi_div_two_sub, sin_pi_div_two_sub,
    opt_wRight_eq]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, uvec_fst, vvec_fst, smul_eq_mul]
    field_simp
    linear_combination (supp K φ) * e
  · simp only [Prod.snd_add, Prod.smul_snd, uvec_snd, vvec_snd, smul_eq_mul]
    field_simp
    ring

/-- `𝐥_K^{π/2 + φ^L}(π/2) = Z_K^L + ((sin φ - 1)/cos φ, 1)` for a cap. -/
lemma opt_tangent_left_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) {K : Set (ℝ × ℝ)}
    (h1 : supp K (π / 2) = 1) :
    tangentParam K (π / 2 + (π / 2 - φ)) (π / 2) = zLeft φ K + ((sin φ - 1) / cos φ, 1) := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, pi_pos], hφ.2⟩
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring]
  have hlt : π / 2 < π - φ := by linarith [hφ.2]
  simp only [tangentParam, hlt, ↓reduceIte, vint, h1, opt_zLeft_eq,
    show π - φ - π / 2 = π / 2 - φ by ring, cos_pi_div_two_sub, sin_pi_div_two_sub,
    opt_uvec_pi_div_two, opt_vvec_pi_div_two]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · simp

lemma opt_wRight_comb {φ : ℝ} {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    wRight φ ((1 - c) • K₁ + c • K₂) = (1 - c) • wRight φ K₁ + c • wRight φ K₂ := by
  simp only [opt_wRight_eq, supp_comb h₁ h₂ hc]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  · simp

lemma opt_zLeft_comb {φ : ℝ} {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    zLeft φ ((1 - c) • K₁ + c • K₂) = (1 - c) • zLeft φ K₁ + c • zLeft φ K₂ := by
  simp only [opt_zLeft_eq, supp_comb h₁ h₂ hc]
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  · simp

/-! ### The surface area measure of a cap below the `x`-axis (package I) -/

section SigmaCap

variable {K : Set (ℝ × ℝ)}

lemma opt_sin_neg_of_mem {t : ℝ} (h1 : π < t) (h2 : t < 2 * π) : sin t < 0 := by
  have : 0 < sin (t - π) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [sin_sub_pi] at this
  linarith

/-- In the directions `t ∈ (π, 3π/2)` a cap touches its supporting line only at `(-h_K(π), 0)`. -/
lemma opt_cap_lower_left (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ioo π (3 * π / 2)) :
    supp K t = -supp K π * cos t ∧ vplus K t = (-supp K π, 0) := by
  have hC := opt_cap_C_mem hK
  have hcb := hK.2.1
  have hcos : cos t < 0 :=
    cos_neg_of_pi_div_two_lt_of_lt (by linarith [ht.1, pi_pos]) (by linarith [ht.2])
  have hsin : sin t < 0 := opt_sin_neg_of_mem ht.1 (by linarith [ht.2, pi_pos])
  have hbd : ∀ p ∈ K, dot p (uvec t) ≤ -supp K π * cos t := by
    intro p hp
    have h1 := (opt_cap_fst_le hK hp).1
    have h2 := (opt_cap_mem_strip hK hp).1
    simp only [dot, uvec]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le]
  have hsupp : supp K t = -supp K π * cos t := by
    apply le_antisymm
    · show sSup _ ≤ _
      exact csSup_le (hcb.1.image _) (by rintro _ ⟨p, hp, rfl⟩; exact hbd p hp)
    · have := dot_le_supp hcb.2.1 hC t
      simpa [dot, uvec] using this
  refine ⟨hsupp, ?_⟩
  have hedge : edge K t = {(-supp K π, (0 : ℝ))} := by
    ext p
    simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, hsupp]
    constructor
    · rintro ⟨hp, hpl⟩
      have h1 := (opt_cap_fst_le hK hp).1
      have h2 := (opt_cap_mem_strip hK hp).1
      simp only [dot, uvec] at hpl
      have e1 : (p.1 + supp K π) * cos t = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le,
          mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ p.1 + supp K π) hcos.le]
      have e2 : p.2 * sin t = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le,
          mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ p.1 + supp K π) hcos.le]
      rcases mul_eq_zero.mp e1 with h | h
      · rcases mul_eq_zero.mp e2 with h' | h'
        · ext <;> simp <;> linarith
        · linarith
      · linarith
    · rintro rfl
      exact ⟨hC, by simp [dot, uvec]⟩
  simp only [vplus, hedge, image_singleton, csSup_singleton, hsupp]
  conv_rhs => rw [eq_dot_uvec_smul_add ((-supp K π, (0 : ℝ))) t]
  rw [show dot (-supp K π, (0 : ℝ)) (uvec t) = -supp K π * cos t by simp [dot, uvec]]

/-- In the directions `t ∈ (3π/2, 2π)` a cap touches its supporting line only at `(h_K(0), 0)`. -/
lemma opt_cap_lower_right (hK : IsCap K (π / 2)) {t : ℝ} (ht : t ∈ Ioo (3 * π / 2) (2 * π)) :
    supp K t = supp K 0 * cos t ∧ vplus K t = (supp K 0, 0) := by
  have hA := opt_cap_A_mem hK
  have hcb := hK.2.1
  have hcos : 0 < cos t := by
    rw [← cos_sub_two_pi]
    exact cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩
  have hsin : sin t < 0 := opt_sin_neg_of_mem (by linarith [ht.1, pi_pos]) ht.2
  have hbd : ∀ p ∈ K, dot p (uvec t) ≤ supp K 0 * cos t := by
    intro p hp
    have h1 := (opt_cap_fst_le hK hp).2
    have h2 := (opt_cap_mem_strip hK hp).1
    simp only [dot, uvec]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le]
  have hsupp : supp K t = supp K 0 * cos t := by
    apply le_antisymm
    · show sSup _ ≤ _
      exact csSup_le (hcb.1.image _) (by rintro _ ⟨p, hp, rfl⟩; exact hbd p hp)
    · have := dot_le_supp hcb.2.1 hA t
      simpa [dot, uvec] using this
  refine ⟨hsupp, ?_⟩
  have hedge : edge K t = {(supp K 0, (0 : ℝ))} := by
    ext p
    simp only [edge, suppLine, line, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, hsupp]
    constructor
    · rintro ⟨hp, hpl⟩
      have h1 := (opt_cap_fst_le hK hp).2
      have h2 := (opt_cap_mem_strip hK hp).1
      simp only [dot, uvec] at hpl
      have e1 : (supp K 0 - p.1) * cos t = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le,
          mul_nonneg (by linarith : 0 ≤ supp K 0 - p.1) hcos.le]
      have e2 : p.2 * sin t = 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hsin.le,
          mul_nonneg (by linarith : 0 ≤ supp K 0 - p.1) hcos.le]
      rcases mul_eq_zero.mp e1 with h | h
      · rcases mul_eq_zero.mp e2 with h' | h'
        · ext <;> simp <;> linarith
        · linarith
      · linarith
    · rintro rfl
      exact ⟨hA, by simp [dot, uvec]⟩
  simp only [vplus, hedge, image_singleton, csSup_singleton, hsupp]
  conv_rhs => rw [eq_dot_uvec_smul_add ((supp K 0, (0 : ℝ))) t]
  rw [show dot (supp K 0, (0 : ℝ)) (uvec t) = supp K 0 * cos t by simp [dot, uvec]]

lemma opt_cap_vplus_three_pi_div_two (hK : IsCap K (π / 2)) :
    vplus K (3 * π / 2) = (supp K 0, 0) := by
  have hA := opt_cap_A_mem hK
  have hS : sSup ((fun p => dot p (vvec (3 * π / 2))) '' edge K (3 * π / 2)) = supp K 0 := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨(supp K 0, 0), ⟨hA, ?_⟩, ?_⟩, ?_⟩
    · simp [suppLine, line, opt_uvec_three_pi_div_two, hK.2.2.2.2.2.1]
    · simp [opt_vvec_three_pi_div_two]
    · rintro _ ⟨q, ⟨hq, -⟩, rfl⟩
      simp [opt_vvec_three_pi_div_two]
      exact (opt_cap_fst_le hK hq).2
  rw [vplus, hS, hK.2.2.2.2.2.1, opt_uvec_three_pi_div_two, opt_vvec_three_pi_div_two]
  simp

lemma opt_sigmaStieltjes_apply (hK : IsConvexBody K) (t : ℝ) :
    sigmaStieltjes K t = sigmaFun K t := by
  simp [sigmaStieltjes, hK]

/-- `σ_K((π, 3π/2)) = 0` for a cap. -/
lemma opt_cap_sigma_Ioo_left (hK : IsCap K (π / 2)) : sigma K (Ioo π (3 * π / 2)) = 0 := by
  have hcb := hK.2.1
  have hsupp := continuous_supp hcb.2.1 hcb.1
  have hconst : ∀ t ∈ Ico π (3 * π / 2), sigmaFun K t = sigmaFun K π := by
    intro t ht
    have hv : ∀ s ∈ Ico π (3 * π / 2), vplus K s = (-supp K π, 0) := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact opt_cap_vplus_pi hK
      · exact (opt_cap_lower_left hK ⟨h, hs.2⟩).2
    have hint : ∫ s in π..t, supp K s = -supp K π * sin t := by
      rw [intervalIntegral.integral_congr (g := fun s => -supp K π * cos s)]
      · rw [intervalIntegral.integral_const_mul, integral_cos, sin_pi, sub_zero]
      · intro s hs
        rw [uIcc_of_le ht.1] at hs
        rcases eq_or_lt_of_le hs.1 with h | h
        · rw [← h]; show supp K π = -supp K π * cos π; rw [cos_pi]; ring
        · exact (opt_cap_lower_left hK ⟨h, lt_of_le_of_lt hs.2 ht.2⟩).1
    have hsplit : ∫ s in (0 : ℝ)..t, supp K s =
        (∫ s in (0 : ℝ)..π, supp K s) + ∫ s in π..t, supp K s :=
      (intervalIntegral.integral_add_adjacent_intervals (hsupp.intervalIntegrable 0 π)
        (hsupp.intervalIntegrable π t)).symm
    simp only [sigmaFun]
    rw [hv t ht, hv π ⟨le_rfl, by linarith [pi_pos]⟩, hsplit, hint]
    simp [dot, vvec, sin_pi]
  rw [sigma, StieltjesFunction.measure_Ioo,
    opt_sigmaStieltjes_apply hcb]
  have hlim : Function.leftLim (sigmaStieltjes K) (3 * π / 2) = sigmaFun K π := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : π < 3 * π / 2)] with s hs
    rw [opt_sigmaStieltjes_apply hcb, hconst s ⟨hs.1.le, hs.2⟩]
  rw [hlim, sub_self, ENNReal.ofReal_zero]

/-- `σ_K((3π/2, 2π)) = 0` for a cap. -/
lemma opt_cap_sigma_Ioo_right (hK : IsCap K (π / 2)) :
    sigma K (Ioo (3 * π / 2) (2 * π)) = 0 := by
  have hcb := hK.2.1
  have hsupp := continuous_supp hcb.2.1 hcb.1
  have hconst : ∀ t ∈ Ico (3 * π / 2) (2 * π), sigmaFun K t = sigmaFun K (3 * π / 2) := by
    intro t ht
    have hv : ∀ s ∈ Ico (3 * π / 2) (2 * π), vplus K s = (supp K 0, 0) := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact opt_cap_vplus_three_pi_div_two hK
      · exact (opt_cap_lower_right hK ⟨h, hs.2⟩).2
    have h3 : supp K (3 * π / 2) = supp K 0 * cos (3 * π / 2) := by
      rw [hK.2.2.2.2.2.1, show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; ring
    have hint : ∫ s in (3 * π / 2)..t, supp K s = supp K 0 * (sin t - sin (3 * π / 2)) := by
      rw [intervalIntegral.integral_congr (g := fun s => supp K 0 * cos s)]
      · rw [intervalIntegral.integral_const_mul, integral_cos]
      · intro s hs
        rw [uIcc_of_le ht.1] at hs
        rcases eq_or_lt_of_le hs.1 with h | h
        · rw [← h]; exact h3
        · exact (opt_cap_lower_right hK ⟨h, lt_of_le_of_lt hs.2 ht.2⟩).1
    have hsplit : ∫ s in (0 : ℝ)..t, supp K s =
        (∫ s in (0 : ℝ)..(3 * π / 2), supp K s) + ∫ s in (3 * π / 2)..t, supp K s :=
      (intervalIntegral.integral_add_adjacent_intervals (hsupp.intervalIntegrable 0 (3 * π / 2))
        (hsupp.intervalIntegrable (3 * π / 2) t)).symm
    simp only [sigmaFun]
    rw [hv t ht, hv (3 * π / 2) ⟨le_rfl, by linarith [pi_pos]⟩, hsplit, hint]
    simp [dot, vvec]
    ring
  rw [sigma, StieltjesFunction.measure_Ioo, opt_sigmaStieltjes_apply hcb]
  have hlim : Function.leftLim (sigmaStieltjes K) (2 * π) = sigmaFun K (3 * π / 2) := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : 3 * π / 2 < 2 * π)] with s hs
    rw [opt_sigmaStieltjes_apply hcb, hconst s ⟨hs.1.le, hs.2⟩]
  rw [hlim, sub_self, ENNReal.ofReal_zero]

/-- Under condition (1) of the injectivity condition, `σ_K` has no atom in `[0, π/2) ∪ (π/2, π]`. -/
lemma opt_inj_sigma_singleton (h1 : InjCond1 K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) : sigma K {t} = 0 := by
  obtain ⟨r, s, -, -, -, -, hr, hs⟩ := h1
  rcases ht with ht | ht
  · have := congrArg (fun μ : Measure ℝ => μ {t}) hr
    simp only [Measure.restrict_apply (measurableSet_singleton t),
      singleton_inter_of_mem ht] at this
    rw [this, MeasureTheory.withDensity_apply _ (measurableSet_singleton t)]
    apply MeasureTheory.setLIntegral_measure_zero
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)
  · have := congrArg (fun μ : Measure ℝ => μ {t}) hs
    simp only [Measure.restrict_apply (measurableSet_singleton t),
      singleton_inter_of_mem ht] at this
    rw [this, MeasureTheory.withDensity_apply _ (measurableSet_singleton t)]
    apply MeasureTheory.setLIntegral_measure_zero
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)

end SigmaCap

/-- For `K ∈ 𝒦^i`: `|K| = 𝒥(𝐮_K^{0,φ}) + 𝒥(𝐮_K^{φ,φ^L}) + 𝒥(𝐮_K^{φ^L,π/2}) + 𝒥(𝐮_K^{π/2,π}) + σ_K(π/2)/2`. -/
lemma opt_area_eq_cca {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    area K = convexCurveArea K 0 φ + convexCurveArea K φ (π / 2 - φ) +
      convexCurveArea K (π / 2 - φ) (π / 2) + convexCurveArea K (π / 2) π +
      (1 / 2) * (sigma K).real {π / 2} := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hcap := hK.1
  have hcb := hcap.2.1
  have h1 := hK.2.1.1
  have hf := continuous_supp hcb.2.1 hcb.1
  set σ := sigma K with hσ
  have hint : ∀ a b : ℝ, IntegrableOn (supp K) (Icc a b) σ := fun a b =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hint' : ∀ {S : Set ℝ} (a b : ℝ), S ⊆ Icc a b → IntegrableOn (supp K) S σ :=
    fun a b hS => (hint a b).mono_set hS
  have hii : ∀ a b : ℝ, IntervalIntegrable (supp K) σ a b := fun a b =>
    hf.intervalIntegrable a b
  have hnull : ∀ t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π, σ {t} = 0 := fun t ht =>
    opt_inj_sigma_singleton h1 ht
  have hIoo : ∀ a b : ℝ, a < b → σ {b} = 0 →
      ∫ t in a..b, supp K t ∂σ = ∫ t in Ioo a b, supp K t ∂σ := by
    intro a b hab hb
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo' hb]
  -- the lower half
  have hlow : ∫ t in Ioo π (2 * π), supp K t ∂σ = 0 := by
    have hset : Ioo π (2 * π) = (Ioo π (3 * π / 2) ∪ Ioo (3 * π / 2) (2 * π)) ∪ {3 * π / 2} := by
      ext t
      simp only [mem_Ioo, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy t (3 * π / 2) with h | h | h
        · exact Or.inl (Or.inl ⟨h1, h⟩)
        · exact Or.inr h
        · exact Or.inl (Or.inr ⟨h, h2⟩)
      · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h)
        · exact ⟨h1, by linarith⟩
        · exact ⟨by linarith, h2⟩
        · rw [h]; constructor <;> linarith
    have hA0 : σ (Ioo π (3 * π / 2) ∪ Ioo (3 * π / 2) (2 * π)) = 0 :=
      measure_union_null (opt_cap_sigma_Ioo_left hcap) (opt_cap_sigma_Ioo_right hcap)
    rw [hset, setIntegral_union (by
        rw [Set.disjoint_singleton_right]
        rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact lt_irrefl _ h)
      (measurableSet_singleton _)
      (hint' π (2 * π) (by
        rintro t (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith))
      (hint' π (2 * π) (by intro t ht; rw [mem_singleton_iff.mp ht]; constructor <;> linarith)),
      setIntegral_measure_zero _ hA0, integral_singleton, hcap.2.2.2.2.2.1, smul_zero, add_zero]
  -- the upper half
  have hup : ∫ t in Icc 0 π, supp K t ∂σ =
      (∫ t in Ioo 0 φ, supp K t ∂σ) + (∫ t in Ioo φ (π / 2 - φ), supp K t ∂σ) +
        ((∫ t in Ioo (π / 2 - φ) (π / 2), supp K t ∂σ) + σ.real {π / 2}) +
        ∫ t in Ioo (π / 2) π, supp K t ∂σ := by
    rw [← Ioc_union_left (by linarith : (0 : ℝ) ≤ π),
      setIntegral_union (by simp) (measurableSet_singleton _)
        (hint' 0 π Ioc_subset_Icc_self)
        (hint' 0 π (by intro t ht; rw [mem_singleton_iff.mp ht]; constructor <;> linarith)),
      integral_singleton, measureReal_def, hnull 0 (Or.inl ⟨le_rfl, by linarith⟩),
      ENNReal.toReal_zero, zero_smul, add_zero, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (hii 0 φ) (hii φ π),
      ← intervalIntegral.integral_add_adjacent_intervals (hii φ (π / 2 - φ)) (hii (π / 2 - φ) π),
      ← intervalIntegral.integral_add_adjacent_intervals (hii (π / 2 - φ) (π / 2))
        (hii (π / 2) π),
      hIoo 0 φ hφ0 (hnull φ (Or.inl ⟨hφ0.le, by linarith⟩)),
      hIoo φ (π / 2 - φ) (by linarith) (hnull _ (Or.inl ⟨by linarith, by linarith⟩)),
      hIoo (π / 2) π (by linarith) (hnull π (Or.inr ⟨by linarith, le_rfl⟩)),
      intervalIntegral.integral_of_le (by linarith : π / 2 - φ ≤ π / 2),
      ← Ioo_union_right (by linarith : π / 2 - φ < π / 2),
      setIntegral_union (by simp) (measurableSet_singleton _)
        (hint' (π / 2 - φ) (π / 2) Ioo_subset_Icc_self)
        (hint' (π / 2 - φ) (π / 2) (by
          intro t ht; rw [mem_singleton_iff.mp ht]; constructor <;> linarith)),
      integral_singleton, hcap.2.2.2.1, smul_eq_mul, mul_one]
    ring
  have hIco : Ico 0 (2 * π) = Icc 0 π ∪ Ioo π (2 * π) := by
    ext t
    simp only [mem_Ico, mem_union, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt t π with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  rw [theorem7_1_3 hcb, hIco, setIntegral_union (by
      rw [Set.disjoint_left]; rintro t ⟨-, h1⟩ ⟨h2, -⟩; linarith)
    measurableSet_Ioo (hint 0 π) (hint' 0 (2 * π) (by
      rintro t ⟨h1, h2⟩; constructor <;> linarith)), hlow, add_zero, hup]
  simp only [convexCurveArea]
  ring

/-- **Lemma 8.3.5** (`lem:upper-boundary-tracing`). On `𝒦^i`,
`|K| ≡_K 𝒥(𝐮_K^{0,φ^R}) + 𝒥(𝐮_K^{φ^R,φ^L}) + 𝒥(𝐮_K^{φ^L,π/2}) + 𝒥(𝐮_K^{π/2,π})`. -/
theorem lemma8_3_5 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => area K.1.1)
      (fun K => convexCurveArea K.1.1 0 φ + convexCurveArea K.1.1 φ (π / 2 - φ) +
        convexCurveArea K.1.1 (π / 2 - φ) (π / 2) + convexCurveArea K.1.1 (π / 2) π) := by
  intro c hc K₁ K₂
  have hcomb : IsKi ((1 - c) • K₁.1.1 + c • K₂.1.1) := theorem8_1_1_convex K₁.2 K₂.2 hc
  have d : ∀ {L : Set (ℝ × ℝ)}, IsKi L → area L - (convexCurveArea L 0 φ +
      convexCurveArea L φ (π / 2 - φ) + convexCurveArea L (π / 2 - φ) (π / 2) +
      convexCurveArea L (π / 2) π) = (1 / 2) * (sigma L).real {π / 2} := by
    intro L hL
    rw [opt_area_eq_cca hφ hL]
    ring
  show area (kiComb c K₁ K₂).1.1 - (convexCurveArea (kiComb c K₁ K₂).1.1 0 φ +
      convexCurveArea (kiComb c K₁ K₂).1.1 φ (π / 2 - φ) +
      convexCurveArea (kiComb c K₁ K₂).1.1 (π / 2 - φ) (π / 2) +
      convexCurveArea (kiComb c K₁ K₂).1.1 (π / 2) π) =
    (1 - c) * (area K₁.1.1 - (convexCurveArea K₁.1.1 0 φ + convexCurveArea K₁.1.1 φ (π / 2 - φ) +
      convexCurveArea K₁.1.1 (π / 2 - φ) (π / 2) + convexCurveArea K₁.1.1 (π / 2) π)) +
    c * (area K₂.1.1 - (convexCurveArea K₂.1.1 0 φ + convexCurveArea K₂.1.1 φ (π / 2 - φ) +
      convexCurveArea K₂.1.1 (π / 2 - φ) (π / 2) + convexCurveArea K₂.1.1 (π / 2) π))
  rw [opt_kiComb_val hc, d hcomb, d K₁.2, d K₂.2, opt_sigma_comb K₁.1.2 K₂.1.2 hc]
  have f1 : sigma K₁.1.1 {π / 2} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  have f2 : sigma K₂.1.1 {π / 2} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  simp only [measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f1)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hc.2), ENNReal.toReal_ofReal hc.1]
  ring

/-- **Lemma 8.3.6** (`lem:linvals`). On `𝒦^i`: (1) `𝒥(𝐲_K|_I) ≡_K 𝒥(𝐱_K|_I)`;
(2) `𝒥(𝐥_K^{π/2}(φ^R), 𝐲_K(φ^R)) ≡_K 𝒥(W_K^R, 𝐱_K^R)`;
(3) `𝒥(𝐥_K^{π/2 + φ^L}(π/2), 𝐲_K(φ^L)) ≡_K 𝒥(Z_K^L, 𝐱_K^L)`.
The paper's (3) evaluates `𝐥_K^{π/2 + φ^L}` at `φ^L`, which makes its left side zero; Lemma 8.3.7 uses
the value at `π/2`, which we state. -/
theorem lemma8_3_6 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => curveArea (outerCorner K.1.1) φ (π / 2 - φ))
        (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) ∧
      kiDomain.EqModLinear
        (fun K => segArea (tangentParam K.1.1 (π / 2) φ) (outerCorner K.1.1 φ))
        (fun K => segArea (wRight φ K.1.1) (xRight φ K.1.1)) ∧
      kiDomain.EqModLinear
        (fun K => segArea (tangentParam K.1.1 (π / 2 + (π / 2 - φ)) (π / 2))
          (outerCorner K.1.1 (π / 2 - φ)))
        (fun K => segArea (zLeft φ K.1.1) (xLeft φ K.1.1)) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro c hc K₁ K₂
    have hi₁ := K₁.2.2.1.2.1
    have hi₂ := K₂.2.2.1.2.1
    have hcb₁ := K₁.1.2
    have hcb₂ := K₂.1.2
    have hcomb : IsKi ((1 - c) • K₁.1.1 + c • K₂.1.1) := theorem8_1_1_convex K₁.2 K₂.2 hc
    show curveArea (outerCorner (kiComb c K₁ K₂).1.1) φ (π / 2 - φ) -
        curveArea (innerCorner (kiComb c K₁ K₂).1.1) φ (π / 2 - φ) =
      (1 - c) * (curveArea (outerCorner K₁.1.1) φ (π / 2 - φ) -
        curveArea (innerCorner K₁.1.1) φ (π / 2 - φ)) +
      c * (curveArea (outerCorner K₂.1.1) φ (π / 2 - φ) -
        curveArea (innerCorner K₂.1.1) φ (π / 2 - φ))
    rw [opt_kiComb_val hc, opt_outer_sub_inner hcomb.2.1.2.1 hφ0.le (by linarith) (by linarith),
      opt_outer_sub_inner hi₁ hφ0.le (by linarith) (by linarith),
      opt_outer_sub_inner hi₂ hφ0.le (by linarith) (by linarith)]
    have hint : ∀ {L : Set (ℝ × ℝ)}, IsKi L → IntervalIntegrable
        (fun t => opt_outerInnerIntegrand L φ (π / 2 - φ) t) MeasureTheory.volume φ (π / 2 - φ) := by
      intro L hL
      have hxI : ContDiffOn ℝ 1 (innerCorner L) (Icc φ (π / 2 - φ)) :=
        hL.2.1.2.1.mono (Icc_subset_Icc hφ0.le (by linarith))
      have hxc := hxI.continuousOn
      have hxd := hxI.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl
      have hcc : Continuous fun t => uvec t + vvec t := by unfold uvec vvec; fun_prop
      have hcd : Continuous fun t => vvec t - uvec t := by unfold uvec vvec; fun_prop
      exact (((opt_continuousOn_cross hxc hcd.continuousOn).add
        (opt_continuousOn_cross hcc.continuousOn hxd)).add
        (opt_continuousOn_cross hcc.continuousOn hcd.continuousOn)).intervalIntegrable_of_Icc
        (by linarith)
    rw [intervalIntegral.integral_congr (g := fun t => (1 - c) * opt_outerInnerIntegrand K₁.1.1 φ
      (π / 2 - φ) t + c * opt_outerInnerIntegrand K₂.1.1 φ (π / 2 - φ) t) (fun t ht => by
        rw [uIcc_of_le (by linarith)] at ht
        exact opt_outerInnerIntegrand_comb hcb₁ hcb₂ hi₁ hi₂ hc hφ0.le (by linarith) ht),
      intervalIntegral.integral_add ((hint K₁.2).const_mul _) ((hint K₂.2).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  · intro c hc K₁ K₂
    have hcb₁ := K₁.1.2
    have hcb₂ := K₂.1.2
    have hcomb : IsKi ((1 - c) • K₁.1.1 + c • K₂.1.1) := theorem8_1_1_convex K₁.2 K₂.2 hc
    show segArea (tangentParam (kiComb c K₁ K₂).1.1 (π / 2) φ) (outerCorner (kiComb c K₁ K₂).1.1 φ) -
        segArea (wRight φ (kiComb c K₁ K₂).1.1) (xRight φ (kiComb c K₁ K₂).1.1) =
      (1 - c) * (segArea (tangentParam K₁.1.1 (π / 2) φ) (outerCorner K₁.1.1 φ) -
        segArea (wRight φ K₁.1.1) (xRight φ K₁.1.1)) +
      c * (segArea (tangentParam K₂.1.1 (π / 2) φ) (outerCorner K₂.1.1 φ) -
        segArea (wRight φ K₂.1.1) (xRight φ K₂.1.1))
    rw [opt_kiComb_val hc, opt_tangent_right_eq hφ2 hcomb.1.2.2.2.1,
      opt_tangent_right_eq hφ2 K₁.2.1.2.2.2.1, opt_tangent_right_eq hφ2 K₂.2.1.2.2.2.1,
      opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
      opt_wRight_comb hcb₁ hcb₂ hc, xRight, xRight, xRight, opt_innerCorner_comb hcb₁ hcb₂ hc]
    simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · intro c hc K₁ K₂
    have hcb₁ := K₁.1.2
    have hcb₂ := K₂.1.2
    have hcomb : IsKi ((1 - c) • K₁.1.1 + c • K₂.1.1) := theorem8_1_1_convex K₁.2 K₂.2 hc
    show segArea (tangentParam (kiComb c K₁ K₂).1.1 (π / 2 + (π / 2 - φ)) (π / 2))
          (outerCorner (kiComb c K₁ K₂).1.1 (π / 2 - φ)) -
        segArea (zLeft φ (kiComb c K₁ K₂).1.1) (xLeft φ (kiComb c K₁ K₂).1.1) =
      (1 - c) * (segArea (tangentParam K₁.1.1 (π / 2 + (π / 2 - φ)) (π / 2))
          (outerCorner K₁.1.1 (π / 2 - φ)) - segArea (zLeft φ K₁.1.1) (xLeft φ K₁.1.1)) +
      c * (segArea (tangentParam K₂.1.1 (π / 2 + (π / 2 - φ)) (π / 2))
          (outerCorner K₂.1.1 (π / 2 - φ)) - segArea (zLeft φ K₂.1.1) (xLeft φ K₂.1.1))
    rw [opt_kiComb_val hc, opt_tangent_left_eq hφ2 hcomb.1.2.2.2.1,
      opt_tangent_left_eq hφ2 K₁.2.1.2.2.2.1, opt_tangent_left_eq hφ2 K₂.2.1.2.2.2.1,
      opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
      opt_zLeft_comb hcb₁ hcb₂ hc, xLeft, xLeft, xLeft, opt_innerCorner_comb hcb₁ hcb₂ hc]
    simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The explicit convex-linear part of `𝒮_K + 𝒫_K` (Lemma 8.3.7). -/
noncomputable def opt_explicitPart (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  supp K 0 / 2 + (supp K 0 - (supp K φ - sin φ) / cos φ) / 2 +
    ((sin φ - supp K (π - φ)) / cos φ - (vminus K (π / 2)).1) / 2 +
    ((vplus K (π / 2)).1 + supp K π) / 2 + supp K π / 2

lemma opt_explicitPart_linear (φ : ℝ) :
    kiDomain.IsConvexLinear realDomain (fun K : KiSet => opt_explicitPart φ K.1.1) := by
  intro c hc K₁ K₂
  have hcb₁ := K₁.1.2
  have hcb₂ := K₂.1.2
  have hm := (opt_vminus_linear (π / 2)) c hc K₁.1 K₂.1
  have hp := (opt_vplus_linear (π / 2)) c hc K₁.1 K₂.1
  simp only [convexBodyDomain, vectorDomain] at hm hp
  show opt_explicitPart φ (kiComb c K₁ K₂).1.1 =
    (1 - c) * opt_explicitPart φ K₁.1.1 + c * opt_explicitPart φ K₂.1.1
  have hk : (kiComb c K₁ K₂).1 = convexBodyComb c K₁.1 K₂.1 := by
    simp only [kiComb, hc, ↓reduceDIte]
  rw [hk]
  simp only [opt_explicitPart]
  rw [hm, hp, opt_convexBodyComb_val hc]
  simp only [supp_comb hcb₁ hcb₂ hc]
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  field_simp
  ring

/-- No atom at `t` means `v_K⁺(t) = v_K⁻(t)`. -/
lemma opt_vplus_eq_vminus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ} (ht : sigma K {t} = 0) :
    vplus K t = vminus K t := by
  have := (proposition2_1_2 hK t).2
  rw [this, sigmaAt, ht, ENNReal.toReal_zero, zero_smul, add_zero]

/-- The bookkeeping of Lemma 8.3.7: `𝒮_K + 𝒫_K` decomposes into convex-linear parts. -/
lemma opt_mamikonS_add_upperP {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K : Set (ℝ × ℝ)} (hK : IsKi K) :
    mamikonS φ K - -upperP φ K = opt_explicitPart φ K +
      (segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
        segArea (wRight φ K) (xRight φ K)) +
      (curveArea (outerCorner K) φ (π / 2 - φ) - curveArea (innerCorner K) φ (π / 2 - φ)) -
      (segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2)) (outerCorner K (π / 2 - φ)) -
        segArea (zLeft φ K) (xLeft φ K)) +
      (area K - (convexCurveArea K 0 φ + convexCurveArea K φ (π / 2 - φ) +
        convexCurveArea K (π / 2 - φ) (π / 2) + convexCurveArea K (π / 2) π)) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hcap := hK.1
  have hcb := hcap.2.1
  have h1 := hK.2.1.1
  have h12 : supp K (π / 2) = 1 := hcap.2.2.2.1
  -- no atoms
  have n0 := opt_inj_sigma_singleton h1 (Or.inl ⟨le_rfl, by linarith⟩ : (0 : ℝ) ∈ _)
  have nφ := opt_inj_sigma_singleton h1 (Or.inl ⟨hφ0.le, by linarith⟩ : φ ∈ _)
  have nψ := opt_inj_sigma_singleton h1 (Or.inl ⟨by linarith, by linarith⟩ : π / 2 - φ ∈ _)
  have nπ := opt_inj_sigma_singleton h1 (Or.inr ⟨by linarith, le_rfl⟩ : π ∈ _)
  have v0 : vplus K 0 = (supp K 0, 0) := by
    rw [opt_vplus_eq_vminus hcb n0, opt_cap_vminus_zero hcap]
  have vφ := opt_vplus_eq_vminus hcb nφ
  have vψ := opt_vplus_eq_vminus hcb nψ
  have vπ : vminus K π = (-supp K π, 0) := by
    rw [← opt_vplus_eq_vminus hcb nπ, opt_cap_vplus_pi hcap]
  -- the tangent line pieces
  have c1 := (theorem8_3_1 hcb (t := π / 2) (a := 0) (b := φ) (by linarith) hφ0.le
    (by linarith)).2.2
  have c3 := (theorem8_3_1 hcb (t := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith)).2.2
  have c4 := (theorem8_3_1 hcb (t := π) (a := π / 2) (b := π) (by linarith) (by linarith)
    le_rfl).2.2
  have l10 : tangentParam K (π / 2) 0 = (supp K 0, 1) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte, vint, h12,
      sub_zero, cos_pi_div_two, sin_pi_div_two, opt_uvec_zero, opt_vvec_zero]
    ext <;> simp
  have l1φ := opt_tangent_right_eq hφ2 h12
  have l3ψ : tangentParam K (π / 2 + (π / 2 - φ)) (π / 2 - φ) = outerCorner K (π / 2 - φ) := by
    rw [show π / 2 + (π / 2 - φ) = π / 2 - φ + π / 2 by ring]
    have hlt : π / 2 - φ < π / 2 - φ + π / 2 := by linarith
    simp only [tangentParam, hlt, ↓reduceIte, vint,
      show π / 2 - φ + π / 2 - (π / 2 - φ) = π / 2 by ring, cos_pi_div_two, sin_pi_div_two,
      mul_zero, sub_zero, div_one, proposition2_2_2_outerCorner]
  have l3h := opt_tangent_left_eq hφ2 h12
  have l4h : tangentParam K π (π / 2) = (-supp K π, 1) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte, vint, h12,
      show π - π / 2 = π / 2 by ring, cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero, div_one,
      opt_uvec_pi_div_two, opt_vvec_pi_div_two]
    ext <;> simp
  have l4π : tangentParam K π π = vminus K π := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  -- the vertices at `π/2` lie on `y = 1`
  have vm2 : (vminus K (π / 2)).2 = 1 := by
    have := dot_vminus_uvec K (π / 2)
    rw [h12, opt_uvec_pi_div_two] at this
    simpa using this
  have vp2 : (vplus K (π / 2)).2 = 1 := by
    have := dot_vplus_uvec K (π / 2)
    rw [h12, opt_uvec_pi_div_two] at this
    simpa using this
  -- collinearity on `l_K(φ)`
  have hl1 : tangentParam K (π / 2) φ ∈ line φ (supp K φ) := by
    simp only [tangentParam, hφ2.2, ↓reduceIte]
    exact vint_mem_line_left K φ (π / 2)
  have hA : vplus K φ ∈ line φ (supp K φ) := dot_vplus_uvec K φ
  have hy : outerCorner K φ ∈ line φ (supp K φ) := by
    show dot (outerCorner K φ) (uvec φ) = supp K φ
    rw [proposition2_2_2_outerCorner]
    simp [dot_add_left, dot_smul_left]
  have col := opt_segArea_collinear hl1 hA hy
  have sw := opt_segArea_swap (outerCorner K (π / 2 - φ)) (vplus K (π / 2 - φ))
  have sw2 := opt_segArea_swap (xRight φ K) (wRight φ K)
  have sw3 := opt_segArea_swap (outerCorner K (π / 2 - φ))
    (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2))
  have sw4 := opt_segArea_swap (zLeft φ K) (xLeft φ K)
  simp only [mamikonS, mamikon, upperP, c1, c3, c4, l3ψ, l4π]
  rw [← vφ, ← vψ] at *
  rw [v0, l10, l4h, vπ]
  rw [l1φ] at col ⊢
  rw [l3h] at sw3 ⊢
  simp only [opt_explicitPart]
  have e1 : segArea (supp K 0, 0) (supp K 0, 1) = supp K 0 / 2 := by
    simp only [segArea, cross]; ring
  have e2 : segArea (supp K 0, 1) (wRight φ K + ((1 - sin φ) / cos φ, 1)) =
      (supp K 0 - (supp K φ - sin φ) / cos φ) / 2 := by
    rw [opt_wRight_eq]
    simp only [segArea, cross, Prod.fst_add, Prod.snd_add]
    field_simp
    ring
  have e3 : segArea (zLeft φ K + ((sin φ - 1) / cos φ, 1)) (vminus K (π / 2)) =
      ((sin φ - supp K (π - φ)) / cos φ - (vminus K (π / 2)).1) / 2 := by
    rw [opt_zLeft_eq]
    simp only [segArea, cross, Prod.fst_add, Prod.snd_add, vm2]
    field_simp
    ring
  have e4 : segArea (vplus K (π / 2)) (-supp K π, 1) = ((vplus K (π / 2)).1 + supp K π) / 2 := by
    simp only [segArea, cross, vp2]
    ring
  have e5 : segArea (-supp K π, 1) (-supp K π, 0) = supp K π / 2 := by
    simp only [segArea, cross]; ring
  have e6 := opt_segArea_self (-supp K π, (0 : ℝ))
  rw [e1, e2, e3, e4, e5, e6]
  linarith

/-- **Lemma 8.3.7** (`lem:mamikon-middle-eq`). On `𝒦^i`, `𝒮_K ≡_K -𝒫_K`. -/
theorem lemma8_3_7 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.EqModLinear (fun K => mamikonS φ K.1.1) (fun K => -upperP φ K.1.1) := by
  obtain ⟨l1, l2, l3⟩ := lemma8_3_6 hφ
  have l5 := lemma8_3_5 hφ
  have lE := opt_explicitPart_linear φ
  intro c hc K₁ K₂
  have hcomb : IsKi ((1 - c) • K₁.1.1 + c • K₂.1.1) := theorem8_1_1_convex K₁.2 K₂.2 hc
  have k := fun (K : KiSet) => opt_mamikonS_add_upperP hφ K.2
  have e1 := l1 c hc K₁ K₂
  have e2 := l2 c hc K₁ K₂
  have e3 := l3 c hc K₁ K₂
  have e5 := l5 c hc K₁ K₂
  have eE := lE c hc K₁ K₂
  simp only [realDomain] at e1 e2 e3 e5 eE ⊢
  rw [k, k, k]
  linarith

/-- **Theorem 8.3.8** (`thm:upper-bound-concave`). `𝒬` is concave on `𝓛`. -/
theorem theorem8_3_8 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) : (lDomain φ).IsConcave (upperQL φ) := by
  obtain ⟨-, cS, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hLin := lemma8_3_7 hφ
  intro x y c hc
  set z := (lDomain φ).comb c x y with hz
  have hzv : z.1 = (convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2) := by
    simp only [hz, lDomain, LTriple.comb, hc, ↓reduceDIte]
  -- the cap parts as elements of `𝒦^i`
  set kx : KiSet := ⟨x.1.1, x.2.1⟩
  set ky : KiSet := ⟨y.1.1, y.2.1⟩
  set kz : KiSet := ⟨z.1.1, z.2.1⟩
  have hkz : kz = kiComb c kx ky := by
    apply Subtype.ext
    show z.1.1 = (kiComb c kx ky).1
    simp only [kiComb, hc, ↓reduceDIte]
    rw [hzv]
  have hQ : ∀ w : LTriple φ, upperQL φ w = (mamikonS φ w.1.1.1 - -upperP φ w.1.1.1) -
      mamikonS φ w.1.1.1 - mamikonR φ w.1.2.1.1 - mamikonL φ w.1.2.2.1 := by
    intro w
    simp only [upperQL]
    rw [lemma8_3_4 hφ w.2]
    ring
  have hB : z.1.2.1 = convexBodyComb c x.1.2.1 y.1.2.1 := by rw [hzv]
  have hD : z.1.2.2 = convexBodyComb c x.1.2.2 y.1.2.2 := by rw [hzv]
  have e1 : mamikonS φ z.1.1.1 - -upperP φ z.1.1.1 =
      (1 - c) * (mamikonS φ x.1.1.1 - -upperP φ x.1.1.1) +
        c * (mamikonS φ y.1.1.1 - -upperP φ y.1.1.1) := by
    have := hLin c hc kx ky
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at this
    exact this
  have e2 : mamikonS φ z.1.1.1 ≤ (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1 := by
    have := cS kx ky c hc
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at this
    exact this
  have e3 : mamikonR φ z.1.2.1.1 ≤
      (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1 := by
    rw [hB]; exact cR x.1.2.1 y.1.2.1 c hc
  have e4 : mamikonL φ z.1.2.2.1 ≤
      (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1 := by
    rw [hD]; exact cL x.1.2.2 y.1.2.2 c hc
  rw [hQ, hQ, hQ]
  linarith

end MovingSofa
