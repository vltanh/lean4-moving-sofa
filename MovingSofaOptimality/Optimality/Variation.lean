module

public import MovingSofaOptimality.Optimality.Concavity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

/-!
# Directional derivatives of `𝒬` (§8.5, general part)

Theorems 8.5.1–8.5.6, together with the general Definitions 8.4.5 (`def:opposite-surface-area`) and
8.4.6 (`def:i-cap`) that they use.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology
open scoped Pointwise

namespace MovingSofaOptimality

attribute [local simp] opt_dot_mk

/-! ### Directional derivatives of quadratic functionals (package I) -/

section DirDerivAux

variable {V W : Type}

lemma opt_quadratic_expand {D : ConvexDomain V} {g : V → V → ℝ}
    (hg : D.IsConvexBilinear D realDomain g) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (K Ks : V) :
    g (D.comb c K Ks) (D.comb c K Ks) =
      (1 - c) * ((1 - c) * g K K + c * g K Ks) + c * ((1 - c) * g Ks K + c * g Ks Ks) := by
  obtain ⟨h1, h2⟩ := hg
  have e := h2 (D.comb c K Ks) c hc K Ks
  simp only [realDomain] at e
  rw [e]
  have e1 := h1 K c hc K Ks
  have e2 := h1 Ks c hc K Ks
  simp only [realDomain] at e1 e2
  rw [e1, e2]

lemma opt_quadratic_hasDerivWithinAt {D : ConvexDomain V} {f : V → ℝ} {g : V → V → ℝ}
    (hg : D.IsConvexBilinear D realDomain g) (hfg : ∀ v, f v = g v v) (K Ks : V) :
    HasDerivWithinAt (fun c => f (D.comb c K Ks)) (g K Ks + g Ks K - 2 * g K K) (Icc 0 1) 0 := by
  set P : ℝ → ℝ := fun c => g K K + c * (g K Ks + g Ks K - 2 * g K K) +
    c * c * (g K K - g K Ks - g Ks K + g Ks Ks) with hP
  have hd : HasDerivAt P (g K Ks + g Ks K - 2 * g K K) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (g K Ks + g Ks K - 2 * g K K)).const_add (g K K)
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const
      (g K K - g K Ks - g Ks K + g Ks Ks)
    convert this.add h2 using 1
    · funext c; simp only [hP, Pi.add_apply, Pi.mul_apply, id]
    · simp only [id]; ring
  apply hd.hasDerivWithinAt.congr
  · intro c hc
    rw [hfg, opt_quadratic_expand hg hc]
    simp only [hP]
    ring
  · rw [hfg, opt_quadratic_expand hg ⟨le_rfl, zero_le_one⟩]
    simp only [hP]
    ring

lemma opt_dirDeriv_eq {D : ConvexDomain V} {f : V → ℝ} {K Ks : V} {d : ℝ}
    (h : HasDerivWithinAt (fun c => f (D.comb c K Ks)) d (Icc 0 1) 0) : D.dirDeriv f K Ks = d :=
  h.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩)

lemma opt_hasDerivWithinAt_comp {D₁ : ConvexDomain V} {D₂ : ConvexDomain W} {pr : V → W}
    (hpr : D₁.IsConvexLinear D₂ pr) {f : W → ℝ} {x xs : V} {d : ℝ}
    (h : HasDerivWithinAt (fun c => f (D₂.comb c (pr x) (pr xs))) d (Icc 0 1) 0) :
    HasDerivWithinAt (fun c => f (pr (D₁.comb c x xs))) d (Icc 0 1) 0 :=
  h.congr (fun c hc => by simp only [hpr c hc]) (by simp only [hpr 0 ⟨le_rfl, zero_le_one⟩])

lemma opt_quadratic_differentiableWithinAt {D : ConvexDomain V} {f : V → ℝ} (hq : D.IsQuadratic f)
    (K Ks : V) : HasDerivWithinAt (fun c => f (D.comb c K Ks)) (D.dirDeriv f K Ks) (Icc 0 1) 0 := by
  obtain ⟨g, hg, hfg⟩ := hq
  have h := opt_quadratic_hasDerivWithinAt hg hfg K Ks
  rw [opt_dirDeriv_eq h]
  exact h

end DirDerivAux


/-- `σ̆_C(X) = σ_C(X + π)` (Definition 8.4.5, `def:opposite-surface-area`). -/
noncomputable def sigmaBreve (C : Set (ℝ × ℝ)) : Measure ℝ := (sigma C).map (fun t => t - π)

/-- `h̆_C(t) = h_C(t + π)` (Definition 8.4.5). -/
noncomputable def suppBreve (C : Set (ℝ × ℝ)) (t : ℝ) : ℝ := supp C (t + π)

/-- The density `i_K` on `(0, π]`: `i_K(t) = ⟨𝐱_K'(t), v_t⟩` and `i_K(t + π/2) = ⟨-𝐱_K'(t), u_t⟩` for
`t ∈ (0, π/2]` (Definition 8.4.6, `def:i-cap`). -/
noncomputable def iFun (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  if t ≤ π / 2 then dot (deriv (innerCorner K) t) (vvec t)
  else -dot (deriv (innerCorner K) (t - π / 2)) (uvec (t - π / 2))

/-- The measure `ι_K = i_K dt` on `[0, π]` (Definition 8.4.6). For `K ∈ 𝒦^i` the density is positive
on `(0, π) \ {π/2}`, so `ι_K` is a positive measure. -/
noncomputable def iota (K : Set (ℝ × ℝ)) : Measure ℝ :=
  (volume.restrict (Icc 0 π)).withDensity (fun t => ENNReal.ofReal (iFun K t))

/-! ### The core curve `𝐱_K|_I` (package I) -/

lemma opt_poly_hasDerivWithinAt {F : ℝ → ℝ} {A B C D : ℝ}
    (hF : ∀ c ∈ Icc (0 : ℝ) 1, F c = (1 - c) * ((1 - c) * A + c * B) + c * ((1 - c) * C + c * D)) :
    HasDerivWithinAt F (B + C - 2 * A) (Icc 0 1) 0 := by
  set P : ℝ → ℝ := fun c => A + c * (B + C - 2 * A) + c * c * (A - B - C + D) with hP
  have hd : HasDerivAt P (B + C - 2 * A) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (B + C - 2 * A)).const_add A
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (A - B - C + D)
    convert this.add h2 using 1
    · funext c; simp only [hP, Pi.add_apply, Pi.mul_apply, id]
    · simp only [id]; ring
  apply hd.hasDerivWithinAt.congr
  · intro c hc; rw [hF c hc]; simp only [hP]; ring
  · rw [hF 0 ⟨le_rfl, zero_le_one⟩]; simp only [hP]; ring

lemma opt_hasDerivAt_cross {f g : ℝ → ℝ × ℝ} {f' g' : ℝ × ℝ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => cross (f s) (g s)) (cross f' (g t) + cross (f t) g') t := by
  have hf1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hf2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hg1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hg
  have hg2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hg
  have := (hf1.mul hg2).sub (hf2.mul hg1)
  convert this using 1
  · funext s
    simp only [cross, Pi.sub_apply, Pi.mul_apply, Function.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  · simp only [cross, Function.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    ring

/-- `∫_a^b 𝐱_{K₁} × 𝐱_{K₂}'`. -/
noncomputable def opt_J (K₁ K₂ : Set (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  ∫ t in a..b, cross (innerCorner K₁ t) (deriv (innerCorner K₂) t)

lemma opt_inj_deriv_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo 0 (π / 2)) :
    deriv (innerCorner ((1 - c) • K₁ + c • K₂)) t =
      (1 - c) • deriv (innerCorner K₁) t + c • deriv (innerCorner K₂) t := by
  rw [opt_innerCorner_comb h₁.1.2.1 h₂.1.2.1 hc]
  exact (((opt_inj_hasDerivAt h₁.2.1.2.1 ht).const_smul (1 - c)).add
    ((opt_inj_hasDerivAt h₂.2.1.2.1 ht).const_smul c)).deriv

lemma opt_curveArea_inner_J {K : Set (ℝ × ℝ)} (h2 : InjCond2 K) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hb : b < π / 2) : curveArea (innerCorner K) a b = (1 / 2) * opt_J K K a b := by
  rw [curveArea_eq_integral hab.le (h2.mono (Icc_subset_Icc ha.le hb.le)), opt_J]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab.le] at ht
  simp only
  rw [((opt_inj_hasDerivAt h2 ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Icc hab t ht)]

lemma opt_J_integrable {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hb : b < π / 2) :
    IntervalIntegrable (fun t => cross (innerCorner K₁ t) (deriv (innerCorner K₂) t))
      MeasureTheory.volume a b :=
  (opt_continuousOn_cross (opt_innerCorner_continuous h₁.1.2.1).continuousOn
    (opt_inj_deriv_continuousOn h₂.2.1.2.1 ha hb)).intervalIntegrable_of_Icc hab.le

lemma opt_J_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < π / 2) :
    opt_J ((1 - c) • K₁ + c • K₂) ((1 - c) • K₁ + c • K₂) a b =
      (1 - c) * ((1 - c) * opt_J K₁ K₁ a b + c * opt_J K₁ K₂ a b) +
        c * ((1 - c) * opt_J K₂ K₁ a b + c * opt_J K₂ K₂ a b) := by
  simp only [opt_J]
  rw [intervalIntegral.integral_congr (g := fun t =>
      (1 - c) * ((1 - c) * cross (innerCorner K₁ t) (deriv (innerCorner K₁) t) +
        c * cross (innerCorner K₁ t) (deriv (innerCorner K₂) t)) +
      c * ((1 - c) * cross (innerCorner K₂ t) (deriv (innerCorner K₁) t) +
        c * cross (innerCorner K₂ t) (deriv (innerCorner K₂) t)))]
  · have i11 := opt_J_integrable h₁ h₁ ha hab hb
    have i12 := opt_J_integrable h₁ h₂ ha hab hb
    have i21 := opt_J_integrable h₂ h₁ ha hab hb
    have i22 := opt_J_integrable h₂ h₂ ha hab hb
    rw [intervalIntegral.integral_add (((i11.const_mul _).add (i12.const_mul _)).const_mul _)
      (((i21.const_mul _).add (i22.const_mul _)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (i11.const_mul _) (i12.const_mul _),
      intervalIntegral.integral_add (i21.const_mul _) (i22.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · intro t ht
    rw [uIcc_of_le hab.le] at ht
    have ht' : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only
    rw [opt_inj_deriv_comb h₁ h₂ hc ht', opt_innerCorner_comb h₁.1.2.1 h₂.1.2.1 hc]
    simp only [Pi.add_apply, Pi.smul_apply, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring

lemma opt_J_swap {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hb : b < π / 2) :
    opt_J K₁ K₂ a b - opt_J K₂ K₁ a b =
      cross (innerCorner K₁ b) (innerCorner K₂ b) - cross (innerCorner K₁ a) (innerCorner K₂ a) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => cross (innerCorner K₁ s) (innerCorner K₂ s))
      (cross (deriv (innerCorner K₁) t) (innerCorner K₂ t) +
        cross (innerCorner K₁ t) (deriv (innerCorner K₂) t)) t := by
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have ht' : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact opt_hasDerivAt_cross (opt_inj_hasDerivAt h₁.2.1.2.1 ht') (opt_inj_hasDerivAt h₂.2.1.2.1 ht')
  have i12 := opt_J_integrable h₁ h₂ ha hab hb
  have i21 := opt_J_integrable h₂ h₁ ha hab hb
  have hint : IntervalIntegrable (fun t => cross (deriv (innerCorner K₁) t) (innerCorner K₂ t) +
      cross (innerCorner K₁ t) (deriv (innerCorner K₂) t)) MeasureTheory.volume a b := by
    refine IntervalIntegrable.add ?_ i12
    have := i21.neg
    refine this.congr fun t _ => ?_
    simp only [Pi.neg_apply, cross]
    ring
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, intervalIntegral.integral_add _ i12]
  · simp only [opt_J]
    rw [show (∫ t in a..b, cross (deriv (innerCorner K₁) t) (innerCorner K₂ t)) =
        -∫ t in a..b, cross (innerCorner K₂ t) (deriv (innerCorner K₁) t) by
      rw [← intervalIntegral.integral_neg]
      congr 1; funext t; simp only [cross]; ring]
    ring
  · have := i21.neg
    refine this.congr fun t _ => ?_
    simp only [Pi.neg_apply, cross]
    ring

lemma opt_continuousOn_dot' {f : ℝ → ℝ × ℝ} {S : Set ℝ} (hf : ContinuousOn f S) :
    ContinuousOn (fun t => dot (f t) (vvec t)) S := by
  unfold dot vvec
  exact ((continuous_fst.comp_continuousOn hf).mul (continuous_sin.neg.continuousOn)).add
    ((continuous_snd.comp_continuousOn hf).mul continuous_cos.continuousOn)

lemma opt_continuousOn_dot'' {f : ℝ → ℝ × ℝ} {S : Set ℝ} (hf : ContinuousOn f S) :
    ContinuousOn (fun t => dot (f t) (uvec (t - π / 2))) S := by
  unfold dot uvec
  exact ((continuous_fst.comp_continuousOn hf).mul
    ((continuous_cos.comp (continuous_sub_right _)).continuousOn)).add
    ((continuous_snd.comp_continuousOn hf).mul
      ((continuous_sin.comp (continuous_sub_right _)).continuousOn))

lemma opt_J_iota {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) {K Ks : Set (ℝ × ℝ)} (hK : IsKi K)
    (hKs : IsKi Ks) :
    opt_J Ks K φ (π / 2 - φ) - opt_J K K φ (π / 2 - φ) =
      ∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ), (supp Ks t - supp K t) * iFun K t := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hab : φ < π / 2 - φ := by linarith
  have hb : π / 2 - φ < π / 2 := by linarith
  have hcK := continuous_supp hK.1.2.1.2.1
  have hcKs := continuous_supp hKs.1.2.1.2.1
  have hdc := opt_inj_deriv_continuousOn hK.2.1.2.1 hφ0 hb
  set G : ℝ → ℝ := fun t => (supp Ks t - supp K t) * iFun K t with hG
  have hL : opt_J Ks K φ (π / 2 - φ) - opt_J K K φ (π / 2 - φ) =
      ∫ t in φ..(π / 2 - φ), (G t + G (t + π / 2)) := by
    simp only [opt_J]
    rw [← intervalIntegral.integral_sub (opt_J_integrable hKs hK hφ0 hab hb)
      (opt_J_integrable hK hK hφ0 hab hb)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    simp only [hG, iFun, show t ≤ π / 2 by linarith [ht.2], ↓reduceIte,
      show ¬(t + π / 2 ≤ π / 2) by linarith [ht.1], show t + π / 2 - π / 2 = t by ring]
    rw [proposition2_2_2_innerCorner, proposition2_2_2_innerCorner]
    simp only [cross, dot, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  have hG1 : ContinuousOn G (Icc φ (π / 2 - φ)) := by
    have h0 : ContinuousOn (fun t => (supp Ks t - supp K t) * dot (deriv (innerCorner K) t) (vvec t))
        (Icc φ (π / 2 - φ)) :=
      (hcKs.sub hcK).continuousOn.mul (opt_continuousOn_dot' hdc)
    refine h0.congr fun t ht => ?_
    simp only [hG, iFun, show t ≤ π / 2 by linarith [ht.2], ↓reduceIte]
  have hG2 : ContinuousOn G (Icc (φ + π / 2) (π - φ)) := by
    have hd2 : ContinuousOn (fun t => deriv (innerCorner K) (t - π / 2)) (Icc (φ + π / 2) (π - φ)) :=
      hdc.comp (continuous_sub_right _).continuousOn
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have h0 : ContinuousOn (fun t => (supp Ks t - supp K t) *
        -dot (deriv (innerCorner K) (t - π / 2)) (uvec (t - π / 2))) (Icc (φ + π / 2) (π - φ)) :=
      (hcKs.sub hcK).continuousOn.mul (opt_continuousOn_dot'' hd2).neg
    refine h0.congr fun t ht => ?_
    simp only [hG, iFun, show ¬(t ≤ π / 2) by linarith [ht.1], ↓reduceIte]
  have hG2' : ContinuousOn (fun t => G (t + π / 2)) (Icc φ (π / 2 - φ)) :=
    hG2.comp (continuous_id.add continuous_const).continuousOn
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [hL, setIntegral_union (by
      rw [Set.disjoint_left]; rintro t ⟨-, h1⟩ ⟨h2, -⟩; linarith)
    measurableSet_Icc (hG1.integrableOn_Icc) (hG2.integrableOn_Icc),
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_add (hG1.intervalIntegrable_of_Icc hab.le)
      (hG2'.intervalIntegrable_of_Icc hab.le),
    intervalIntegral.integral_comp_add_right G (π / 2),
    show π / 2 - φ + π / 2 = π - φ by ring]

/-! ### Integration by parts against Stieltjes measures (package I) -/

/-- Integration by parts against a Stieltjes measure. -/
lemma opt_stieltjes_ibp (F : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hfd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (f' t) (Ioi t) t)
    (hf'm : Measurable f') {C : ℝ} (hf'b : ∀ t, |f' t| ≤ C) :
    ∫ t in Ioc a b, f t ∂F.measure = f b * F b - f a * F a - ∫ t in a..b, f' t * F t := by
  set μ := F.measure.restrict (Ioc a b) with hμ
  set ν := (volume : Measure ℝ).restrict (Ioc a b) with hν
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, univ_inter, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hbd : ∀ t, ‖f' t‖ ≤ C := fun t => by rw [Real.norm_eq_abs]; exact hf'b t
  have hf'ν : Integrable f' ν :=
    Integrable.of_bound hf'm.aestronglyMeasurable C (Eventually.of_forall hbd)
  have hf'ii : ∀ x y : ℝ, IntervalIntegrable f' volume x y := by
    intro x y
    refine ⟨?_, ?_⟩ <;>
    exact Integrable.of_bound hf'm.aestronglyMeasurable C (Eventually.of_forall hbd)
  -- `f t = f a + ∫_{(a,t)} f'`
  have hft : ∀ t ∈ Ioc a b, f t = f a + ∫ s, (Iio t).indicator f' s ∂ν := by
    intro t ht
    have h1 := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1.le
      (hfc.mono (Icc_subset_Icc le_rfl ht.2)) (fun x hx => hfd x ⟨hx.1, hx.2.trans_le ht.2⟩)
      (hf'ii a t)
    rw [hν, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      show Iio t ∩ Ioc a b = Ioo a t by
        ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
        constructor
        · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans ht.2⟩,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le, h1]
    ring
  -- Fubini
  have hm : Measurable (Function.uncurry fun t s => (Iio t).indicator f' s) := by
    have : Function.uncurry (fun t s => (Iio t).indicator f' s) =
        {p : ℝ × ℝ | p.2 < p.1}.indicator (fun p => f' p.2) := by
      funext p
      simp only [Function.uncurry, indicator, mem_Iio, mem_ofPred_eq]
    rw [this]
    exact (hf'm.comp measurable_snd).indicator (measurableSet_lt measurable_snd measurable_fst)
  have hint : Integrable (Function.uncurry fun t s => (Iio t).indicator f' s) (μ.prod ν) := by
    refine Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, indicator]
    split_ifs
    · exact hbd _
    · simp only [norm_zero]; exact le_trans (norm_nonneg _) (hbd 0)
  have hswap := integral_integral_swap hint
  have hinner : ∀ s ∈ Ioc a b, ∫ t, (Iio t).indicator f' s ∂μ = f' s * (F b - F s) := by
    intro s hs
    have : (fun t => (Iio t).indicator f' s) = (Ioi s).indicator (fun _ => f' s) := by
      funext t
      simp only [indicator, mem_Iio, mem_Ioi]
    rw [this, integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul,
      measureReal_def, hμ, Measure.restrict_apply measurableSet_Ioi,
      show Ioi s ∩ Ioc a b = Ioc s b by
        ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hs.1.trans h1, h2⟩,
      StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hs.2))]
    ring
  have hFm : Measurable (fun t => F t) := F.mono.measurable
  have hFb : ∀ t ∈ Ioc a b, ‖F t‖ ≤ max |F a| |F b| := by
    intro t ht
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := F.mono ht.1.le
      have := le_max_left |F a| |F b|
      have := neg_abs_le (F a)
      linarith
    · have := F.mono ht.2
      have := le_max_right |F a| |F b|
      have := le_abs_self (F b)
      linarith
  have hf'Fi : Integrable (fun s => f' s * F s) ν := by
    refine hf'ν.mul_bdd (c := max |F a| |F b|) hFm.aestronglyMeasurable ?_
    rw [hν, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hFb
  calc ∫ t in Ioc a b, f t ∂F.measure
      = ∫ t, (f a + ∫ s, (Iio t).indicator f' s ∂ν) ∂μ := setIntegral_congr_fun measurableSet_Ioc hft
    _ = f a * μ.real univ + ∫ t, ∫ s, (Iio t).indicator f' s ∂ν ∂μ := by
        have hI : Integrable (fun t => ∫ s, (Iio t).indicator f' s ∂ν) μ := hint.integral_prod_left
        rw [integral_add (integrable_const _) hI, integral_const, smul_eq_mul, mul_comm]
    _ = f a * (F b - F a) + ∫ s, ∫ t, (Iio t).indicator f' s ∂μ ∂ν := by
        rw [hswap, measureReal_def, hμ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hab))]
    _ = f a * (F b - F a) + ∫ s, (f' s * (F b - F s)) ∂ν := by
        congr 1
        rw [hν]
        exact setIntegral_congr_fun measurableSet_Ioc hinner
    _ = f b * F b - f a * F a - ∫ t in a..b, f' t * F t := by
        have e : (fun s => f' s * (F b - F s)) = fun s => F b * f' s - f' s * F s := by
          funext s; ring
        rw [e, integral_sub (hf'ν.const_mul _) hf'Fi, integral_const_mul,
          intervalIntegral.integral_of_le hab]
        have h1 := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hfc hfd (hf'ii a b)
        rw [intervalIntegral.integral_of_le hab] at h1
        rw [hν, h1]
        ring

/-! ### Integration by parts against the surface area measure (package I) -/

/-- The right derivative `v_K⁺(t) · v_t` of the support function. -/
noncomputable def opt_g (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (vplus K t) (vvec t)

/-- The left derivative `v_K⁻(t) · v_t` of the support function. -/
noncomputable def opt_gm (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := dot (vminus K t) (vvec t)

/-- The primitive `∫_0^t h_K` of the support function. -/
noncomputable def opt_H (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, supp K s

lemma opt_H_hasDerivAt {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    HasDerivAt (opt_H K) (supp K t) t := by
  have hs := continuous_supp hK.2.1
  exact intervalIntegral.integral_hasDerivAt_right (hs.intervalIntegrable 0 t)
    hs.measurable.stronglyMeasurable.stronglyMeasurableAtFilter hs.continuousAt

lemma opt_g_measurable {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Measurable (opt_g K) := by
  have h1 : Measurable (sigmaFun K) := (monotone_sigmaFun hK).measurable
  have h2 : Continuous (opt_H K) :=
    continuous_iff_continuousAt.mpr fun t => (opt_H_hasDerivAt hK t).continuousAt
  have : opt_g K = fun t => sigmaFun K t - opt_H K t := by
    funext t; simp only [opt_g, sigmaFun, opt_H]; ring
  rw [this]
  exact h1.sub h2.measurable

lemma opt_g_bound {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : ∃ C, ∀ t, |opt_g K t| ≤ C := by
  obtain ⟨R, hR⟩ := hK.2.1.isBounded.exists_norm_le
  refine ⟨2 * R, fun t => ?_⟩
  have hp := hR _ (vplus_mem_edge hK t).1
  have h1 : |(vplus K t).1| ≤ R := (norm_fst_le _).trans hp
  have h2 : |(vplus K t).2| ≤ R := (norm_snd_le _).trans hp
  simp only [opt_g, dot, vvec]
  calc |(vplus K t).1 * -sin t + (vplus K t).2 * cos t|
      ≤ |(vplus K t).1 * -sin t| + |(vplus K t).2 * cos t| := abs_add_le _ _
    _ = |(vplus K t).1| * |sin t| + |(vplus K t).2| * |cos t| := by
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ R * 1 + R * 1 := by
        have hR0 : 0 ≤ R := (norm_nonneg _).trans hp
        exact add_le_add (mul_le_mul h1 (abs_sin_le_one t) (abs_nonneg _) hR0)
          (mul_le_mul h2 (abs_cos_le_one t) (abs_nonneg _) hR0)
    _ = 2 * R := by ring

lemma opt_g_intervalIntegrable {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (opt_g K) volume a b := by
  obtain ⟨C, hC⟩ := opt_g_bound hK
  refine ⟨?_, ?_⟩ <;>
  exact Integrable.of_bound (opt_g_measurable hK).aestronglyMeasurable C
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hC t)

/-- `∫_{(a,b]} h_{K₁} dσ_{K₂} = h_{K₁}(b) g_{K₂}(b) - h_{K₁}(a) g_{K₂}(a) - ∫ g₁ g₂ + ∫ h₁ h₂`. -/
lemma opt_intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b :=
  ⟨IntegrableOn.of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hC t),
    IntegrableOn.of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hC t)⟩

/-- `∫_{(a,b]} h_{K₁} dσ_{K₂} = h_{K₁}(b) g_{K₂}(b) - h_{K₁}(a) g_{K₂}(a) - ∫ g₁ g₂ + ∫ h₁ h₂`. -/
lemma opt_supp_ibp {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in Ioc a b, supp K₁ t ∂(sigma K₂) =
      supp K₁ b * opt_g K₂ b - supp K₁ a * opt_g K₂ a - (∫ t in a..b, opt_g K₁ t * opt_g K₂ t) +
        ∫ t in a..b, supp K₁ t * supp K₂ t := by
  have hs₁ := continuous_supp h₁.2.1
  have hs₂ := continuous_supp h₂.2.1
  obtain ⟨C₁, hC₁⟩ := opt_g_bound h₁
  obtain ⟨C₂, hC₂⟩ := opt_g_bound h₂
  have hHc : Continuous (opt_H K₂) :=
    continuous_iff_continuousAt.mpr fun t => (opt_H_hasDerivAt h₂ t).continuousAt
  have hF : ∀ t, sigmaStieltjes K₂ t = opt_g K₂ t + opt_H K₂ t := by
    intro t; rw [opt_sigmaStieltjes_apply h₂]; rfl
  have hibp := opt_stieltjes_ibp (sigmaStieltjes K₂) hab hs₁.continuousOn
    (fun t _ => (hasDerivWithinAt_supp_right h₁ t).mono Ioi_subset_Ici_self)
    (opt_g_measurable h₁) hC₁
  have hH := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := supp K₁) (v := opt_H K₂) (u' := opt_g K₁) (v' := supp K₂) (a := a) (b := b)
    hs₁.continuousOn hHc.continuousOn
    (fun t _ => (hasDerivWithinAt_supp_right h₁ t).mono Ioi_subset_Ici_self)
    (fun t _ => (opt_H_hasDerivAt h₂ t).hasDerivWithinAt)
    (opt_g_intervalIntegrable h₁ a b) (hs₂.intervalIntegrable a b)
  have hgg : IntervalIntegrable (fun t => opt_g K₁ t * opt_g K₂ t) volume a b :=
    opt_intervalIntegrable_of_bound ((opt_g_measurable h₁).mul (opt_g_measurable h₂))
      (C := C₁ * C₂) (fun t => by
        simp only [Pi.mul_apply]
        rw [abs_mul]
        exact mul_le_mul (hC₁ t) (hC₂ t) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ t))) a b
  have hgH : IntervalIntegrable (fun t => opt_g K₁ t * opt_H K₂ t) volume a b :=
    (opt_g_intervalIntegrable h₁ a b).mul_continuousOn hHc.continuousOn
  have hg1 : ∀ t, dot (vplus K₁ t) (vvec t) = opt_g K₁ t := fun t => rfl
  rw [sigma, hibp]
  simp only [hF, mul_add, hg1]
  rw [intervalIntegral.integral_add hgg hgH]
  linarith


lemma opt_sigma_real_singleton {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (b : ℝ) :
    (sigma K).real {b} = opt_g K b - opt_gm K b := by
  have h := (proposition2_1_2 hK b).2
  have e := congrArg (fun p => dot p (vvec b)) h
  simp only [dot_add_left, dot_smul_left, dot_vvec_self, mul_one] at e
  simp only [opt_g, opt_gm, e, measureReal_def, sigmaAt]
  ring

lemma opt_supp_ibp_Ioo {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {a b : ℝ}
    (hab : a < b) :
    ∫ t in Ioo a b, supp K₁ t ∂(sigma K₂) =
      supp K₁ b * opt_gm K₂ b - supp K₁ a * opt_g K₂ a - (∫ t in a..b, opt_g K₁ t * opt_g K₂ t) +
        ∫ t in a..b, supp K₁ t * supp K₂ t := by
  have hs₁ := continuous_supp h₁.2.1
  have hI : IntegrableOn (supp K₁) (Icc a b) (sigma K₂) :=
    hs₁.continuousOn.integrableOn_compact isCompact_Icc
  have h := opt_supp_ibp h₁ h₂ hab.le
  rw [← Ioo_union_right hab, setIntegral_union (by simp) (measurableSet_singleton _)
    (hI.mono_set Ioo_subset_Icc_self)
    (hI.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨hab.le, le_rfl⟩)),
    integral_singleton, opt_sigma_real_singleton h₂, smul_eq_mul] at h
  linarith

lemma opt_cross_frame (h₁ m₁ h₂ m₂ b : ℝ) :
    cross (h₁ • uvec b + m₁ • vvec b) (h₂ • uvec b + m₂ • vvec b) = h₁ * m₂ - m₁ * h₂ := by
  simp only [cross, uvec, vvec, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  linear_combination (h₁ * m₂ - m₁ * h₂) * sin_sq_add_cos_sq b

lemma opt_vminus_frame (K : Set (ℝ × ℝ)) (b : ℝ) :
    vminus K b = supp K b • uvec b + opt_gm K b • vvec b := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vminus K b) b]
  rw [dot_vminus_uvec]; rfl

lemma opt_vplus_frame (K : Set (ℝ × ℝ)) (b : ℝ) :
    vplus K b = supp K b • uvec b + opt_g K b • vvec b := by
  conv_lhs => rw [eq_dot_uvec_smul_add (vplus K b) b]
  rw [dot_vplus_uvec]; rfl

/-- The antisymmetry of `𝓑(K₁, K₂) = ∫_{(a,b)} h_{K₁} dσ_{K₂}` (proof of Theorem 8.5.2). -/
lemma opt_bilin_antisymm {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    {a b : ℝ} (hab : a < b) :
    (∫ t in Ioo a b, supp K₁ t ∂(sigma K₂)) - (∫ t in Ioo a b, supp K₂ t ∂(sigma K₁)) =
      cross (vminus K₁ b) (vminus K₂ b) - cross (vplus K₁ a) (vplus K₂ a) := by
  rw [opt_supp_ibp_Ioo h₁ h₂ hab, opt_supp_ibp_Ioo h₂ h₁ hab, opt_vminus_frame K₁ b,
    opt_vminus_frame K₂ b, opt_vplus_frame K₁ a, opt_vplus_frame K₂ a, opt_cross_frame,
    opt_cross_frame]
  have e1 : ∫ t in a..b, opt_g K₂ t * opt_g K₁ t = ∫ t in a..b, opt_g K₁ t * opt_g K₂ t := by
    congr 1; funext t; ring
  have e2 : ∫ t in a..b, supp K₂ t * supp K₁ t = ∫ t in a..b, supp K₁ t * supp K₂ t := by
    congr 1; funext t; ring
  rw [e1, e2]
  ring



/-- The integral of `h_{K₁}` against `σ_{K₂}` over a set `S` contained in a compact interval. -/
noncomputable def opt_Bs (S : Set ℝ) (K₁ K₂ : Set (ℝ × ℝ)) : ℝ := ∫ t in S, supp K₁ t ∂(sigma K₂)

lemma opt_Bs_comb {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {S : Set ℝ} {a b : ℝ} (hS : S ⊆ Icc a b) :
    opt_Bs S ((1 - c) • K₁ + c • K₂) ((1 - c) • K₁ + c • K₂) =
      (1 - c) * ((1 - c) * opt_Bs S K₁ K₁ + c * opt_Bs S K₂ K₁) +
        c * ((1 - c) * opt_Bs S K₁ K₂ + c * opt_Bs S K₂ K₂) := by
  have hs₁ := continuous_supp h₁.2.1
  have hs₂ := continuous_supp h₂.2.1
  have hI : ∀ (f : ℝ → ℝ), Continuous f → ∀ (μ : Measure ℝ) [IsLocallyFiniteMeasure μ],
      Integrable f (μ.restrict S) := fun f hf μ _ =>
    (hf.continuousOn.integrableOn_compact (μ := μ) isCompact_Icc).mono_set hS
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  have hcomb : Continuous (fun t => (1 - c) * supp K₁ t + c * supp K₂ t) := by fun_prop
  simp only [opt_Bs]
  rw [opt_sigma_comb h₁ h₂ hc, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    integral_add_measure
      ((hI _ (continuous_supp (isConvexBody_comb (c := c) h₁ h₂).2.1) _).smul_measure
        ENNReal.ofReal_ne_top)
      ((hI _ (continuous_supp (isConvexBody_comb (c := c) h₁ h₂).2.1) _).smul_measure
        ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hc1,
    ENNReal.toReal_ofReal hc0]
  simp only [supp_comb h₁ h₂ hc, smul_eq_mul]
  rw [integral_add ((hI _ hs₁ _).const_mul _) ((hI _ hs₂ _).const_mul _),
    integral_add ((hI _ hs₁ _).const_mul _) ((hI _ hs₂ _).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- Integrals against `σ_K` over `(π, 2π)` vanish for a cap and an integrand vanishing at `3π/2`. -/
lemma opt_cap_integral_lower {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {f : ℝ → ℝ}
    (hf : Continuous f) (h3 : f (3 * π / 2) = 0) : ∫ t in Ioo π (2 * π), f t ∂(sigma K) = 0 := by
  have hpi := pi_pos
  have hI : ∀ {S : Set ℝ}, S ⊆ Icc π (2 * π) → IntegrableOn f S (sigma K) := fun hS =>
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hS
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
  have hA0 : sigma K (Ioo π (3 * π / 2) ∪ Ioo (3 * π / 2) (2 * π)) = 0 :=
    measure_union_null (opt_cap_sigma_Ioo_left hK) (opt_cap_sigma_Ioo_right hK)
  rw [hset, setIntegral_union (by
      rw [Set.disjoint_singleton_right]
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact lt_irrefl _ h)
    (measurableSet_singleton _)
    (hI (by rintro t (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith))
    (hI (by intro t ht; rw [mem_singleton_iff.mp ht]; constructor <;> linarith)),
    setIntegral_measure_zero _ hA0, integral_singleton, h3, smul_zero, add_zero]

lemma opt_Ico_eq_Icc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) {f : ℝ → ℝ} (hf : Continuous f)
    (h3 : f (3 * π / 2) = 0) :
    ∫ t in Ico 0 (2 * π), f t ∂(sigma K) = ∫ t in Icc 0 π, f t ∂(sigma K) := by
  have hpi := pi_pos
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
  rw [hIco, setIntegral_union (by
      rw [Set.disjoint_left]; rintro t ⟨-, h1⟩ ⟨h2, -⟩; linarith)
    measurableSet_Ioo (hf.continuousOn.integrableOn_compact isCompact_Icc)
    ((hf.continuousOn.integrableOn_compact (isCompact_Icc (a := π) (b := 2 * π))).mono_set
      Ioo_subset_Icc_self), opt_cap_integral_lower hK hf h3, add_zero]

lemma opt_g_two_pi (K : Set (ℝ × ℝ)) : opt_g K (2 * π) = opt_g K 0 := by
  have h := supp_add_two_pi K 0
  rw [zero_add] at h
  have hu : uvec (2 * π) = uvec 0 := by simpa using uvec_add_two_pi 0
  have hv : vvec (2 * π) = vvec 0 := by simpa using vvec_add_two_pi 0
  have he : edge K (2 * π) = edge K 0 := by
    simp only [edge, suppLine, line, h, hu]
  simp only [opt_g, vplus, h, hu, hv, he]

/-- The mixed area is symmetric on `𝒦^i` (proof of Theorem 8.5.1, Schneider (5.19)). -/
lemma opt_Bs_symm {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsKi K₁) (h₂ : IsKi K₂) :
    opt_Bs (Ico 0 (2 * π)) K₁ K₂ = opt_Bs (Ico 0 (2 * π)) K₂ K₁ := by
  have hpi := pi_pos
  have key : ∀ {L₁ L₂ : Set (ℝ × ℝ)}, IsKi L₁ → IsKi L₂ → opt_Bs (Ico 0 (2 * π)) L₁ L₂ =
      -(∫ t in (0 : ℝ)..(2 * π), opt_g L₁ t * opt_g L₂ t) +
        ∫ t in (0 : ℝ)..(2 * π), supp L₁ t * supp L₂ t := by
    intro L₁ L₂ hL₁ hL₂
    have hcb₁ := hL₁.1.2.1
    have hcb₂ := hL₂.1.2.1
    have n0 : sigma L₂ {0} = 0 :=
      opt_inj_sigma_singleton hL₂.2.1.1 (Or.inl ⟨le_rfl, by linarith⟩)
    have n2 : sigma L₂ {2 * π} = 0 := by
      have := sigma_periodic hcb₂ {0}
      simp only [image_singleton, zero_add] at this
      rw [this, n0]
    have h := opt_supp_ibp hcb₁ hcb₂ (by linarith : (0 : ℝ) ≤ 2 * π)
    simp only [opt_Bs]
    rw [integral_Ico_eq_integral_Ioo' n0, ← integral_Ioc_eq_integral_Ioo' n2, h,
      opt_g_two_pi, show supp L₁ (2 * π) = supp L₁ 0 by
        have := supp_add_two_pi L₁ 0; rwa [zero_add] at this]
    ring
  rw [key h₁ h₂, key h₂ h₁]
  have e1 : ∫ t in (0 : ℝ)..(2 * π), opt_g K₂ t * opt_g K₁ t =
      ∫ t in (0 : ℝ)..(2 * π), opt_g K₁ t * opt_g K₂ t := by
    congr 1; funext t; ring
  have e2 : ∫ t in (0 : ℝ)..(2 * π), supp K₂ t * supp K₁ t =
      ∫ t in (0 : ℝ)..(2 * π), supp K₁ t * supp K₂ t := by
    congr 1; funext t; ring
  rw [e1, e2]

/-- **Theorem 8.5.1** (`thm:variation-convex-body`). The area is quadratic on `𝒦^i`, with
`D|·|(K; K*) = ∫_{[0, π]} (h_{K*} - h_K) dσ_K`. -/
theorem theorem8_5_1 : kiDomain.IsQuadratic (fun K => area K.1.1) ∧
    ∀ K Ks : KiSet, kiDomain.dirDeriv (fun K => area K.1.1) K Ks =
      ∫ t in Icc 0 π, (supp Ks.1.1 t - supp K.1.1 t) ∂(sigma K.1.1) := by
  refine ⟨opt_isQuadratic_comp opt_projKi_linear theorem7_1_3_quadratic, fun K Ks => ?_⟩
  have hd : HasDerivWithinAt (fun c => area (kiDomain.comb c K Ks).1.1)
      (opt_Bs (Ico 0 (2 * π)) Ks.1.1 K.1.1 / 2 + opt_Bs (Ico 0 (2 * π)) K.1.1 Ks.1.1 / 2 -
        2 * (opt_Bs (Ico 0 (2 * π)) K.1.1 K.1.1 / 2)) (Icc 0 1) 0 := by
    apply opt_poly_hasDerivWithinAt (D := opt_Bs (Ico 0 (2 * π)) Ks.1.1 Ks.1.1 / 2)
    intro c hc
    have hcomb := theorem8_1_1_convex K.2 Ks.2 hc
    show area (kiComb c K Ks).1.1 = _
    rw [opt_kiComb_val hc, theorem7_1_3 hcomb.1.2.1]
    have := opt_Bs_comb K.1.2 Ks.1.2 hc (S := Ico 0 (2 * π)) (a := 0) (b := 2 * π)
      Ico_subset_Icc_self
    simp only [opt_Bs] at this
    rw [this]
    simp only [opt_Bs]
    ring
  rw [opt_dirDeriv_eq hd, opt_Bs_symm K.2 Ks.2]
  have hs := continuous_supp K.1.2.2.1
  have hss := continuous_supp Ks.1.2.2.1
  have hcap := K.2.1
  have e1 := opt_Ico_eq_Icc hcap hss Ks.2.1.2.2.2.2.2.1
  have e2 := opt_Ico_eq_Icc hcap hs K.2.1.2.2.2.2.2.1
  rw [integral_sub ((hss.continuousOn.integrableOn_compact isCompact_Icc))
    ((hs.continuousOn.integrableOn_compact isCompact_Icc))]
  simp only [opt_Bs]
  rw [e1, e2]
  ring

/-- **Theorem 8.5.2** (`thm:convex-curve-area-variation`). For `a < b < a + π`, `𝒥(𝐮_K^{a,b})` is
quadratic on `𝒦` with directional derivative
`∫_{(a,b)} (h_{K*} - h_K) dσ_K + [𝒥(v_K⁻(b), v_{K*}⁻(b)) - 𝒥(v_K⁺(a), v_{K*}⁺(a))]`. -/
theorem theorem8_5_2 {a b : ℝ} (hab : a < b) :
    convexBodyDomain.IsQuadratic (fun K => convexCurveArea K.1 a b) ∧
      ∀ K Ks : ConvexBodySet, convexBodyDomain.dirDeriv (fun K => convexCurveArea K.1 a b) K Ks =
        (∫ t in Ioo a b, (supp Ks.1 t - supp K.1 t) ∂(sigma K.1)) +
          (segArea (vminus K.1 b) (vminus Ks.1 b) - segArea (vplus K.1 a) (vplus Ks.1 a)) := by
  refine ⟨theorem7_3_2_quadratic, fun K Ks => ?_⟩
  have hd : HasDerivWithinAt (fun c => convexCurveArea (convexBodyDomain.comb c K Ks).1 a b)
      (opt_Bs (Ioo a b) Ks.1 K.1 / 2 + opt_Bs (Ioo a b) K.1 Ks.1 / 2 -
        2 * (opt_Bs (Ioo a b) K.1 K.1 / 2)) (Icc 0 1) 0 := by
    apply opt_poly_hasDerivWithinAt (D := opt_Bs (Ioo a b) Ks.1 Ks.1 / 2)
    intro c hc
    show convexCurveArea (convexBodyComb c K Ks).1 a b = _
    rw [opt_convexBodyComb_val hc]
    have := opt_Bs_comb K.2 Ks.2 hc (S := Ioo a b) Ioo_subset_Icc_self
    simp only [opt_Bs] at this
    rw [convexCurveArea, this]
    simp only [opt_Bs]
    ring
  rw [opt_dirDeriv_eq hd]
  have hanti := opt_bilin_antisymm K.2 Ks.2 hab
  have hs := continuous_supp K.2.2.1
  have hss := continuous_supp Ks.2.2.1
  rw [integral_sub ((hss.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self) ((hs.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self)]
  simp only [opt_Bs, segArea] at hanti ⊢
  linarith

/-- **Theorem 8.5.3** (`thm:variation-segment`). `𝒥(p, q)` is quadratic on `ℝ² × ℝ²` with directional
derivative `½((p* + q*) × (q - p) - 2(p × q)) + [𝒥(q, q*) - 𝒥(p, p*)]`. -/
theorem theorem8_5_3 :
    (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))).IsQuadratic (fun x => segArea x.1 x.2) ∧
      ∀ x xs : (ℝ × ℝ) × (ℝ × ℝ),
        (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))).dirDeriv (fun x => segArea x.1 x.2) x xs =
          (1 / 2) * (cross (xs.1 + xs.2) (x.2 - x.1) - 2 * cross x.1 x.2) +
            (segArea x.2 xs.2 - segArea x.1 xs.1) := by
  have hg : (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))).IsConvexBilinear
      (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))) realDomain (fun x y => segArea x.1 y.2) := by
    constructor
    · intro x₁ c hc v w
      simp only [vectorDomain, realDomain, segArea, Prod.snd_add, Prod.smul_snd, cross_add_right,
        cross_smul_right]
      ring
    · intro y₂ c hc v w
      simp only [vectorDomain, realDomain, segArea, Prod.fst_add, Prod.smul_fst, cross_add_left,
        cross_smul_left]
      ring
  refine ⟨⟨_, hg, fun x => rfl⟩, fun x xs => ?_⟩
  rw [opt_dirDeriv_eq (opt_quadratic_hasDerivWithinAt hg (fun v => rfl) x xs)]
  simp only [segArea, cross, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-! ### The curve area functional on `C^BV[a, b]` (package I) -/

/-- `df` has finite total variation (it is `0` when `f` is not of bounded variation). -/
lemma opt_lsMeasure_isFinite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) (a b : ℝ) : IsFiniteMeasure (lsMeasure f a b).variation := by
  unfold lsMeasure
  split_ifs
  · infer_instance
  · rw [VectorMeasure.variation_zero]; infer_instance

/-- `d((1 - c) x + c y) = (1 - c) dx + c dy` for curves in `C^BV[a, b]`. -/
lemma opt_lsMeasure_comb {x y : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b) (hx : IsCBV x a b)
    (hy : IsCBV y a b) (hz : IsCBV ((1 - c) • x + c • y) a b) :
    lsMeasure ((1 - c) • x + c • y) a b = (1 - c) • lsMeasure x a b + c • lsMeasure y a b := by
  apply VectorMeasure.ext_of_Icc
  intro p q hpq
  rw [opt_lsMeasure_Icc hab hz.1 hz.2 hpq, add_apply, smul_apply,
    smul_apply, opt_lsMeasure_Icc hab hx.1 hx.2 hpq,
    opt_lsMeasure_Icc hab hy.1 hy.2 hpq]
  simp only [clampFun, Pi.add_apply, Pi.smul_apply, smul_sub]
  abel

/-- `𝓑(x, y)` is affine in `y`. -/
lemma opt_curveBilin_comb_right {x y z : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hxc : ContinuousOn x (Icc a b)) (hy : IsCBV y a b) (hz : IsCBV z a b)
    (hw : IsCBV ((1 - c) • y + c • z) a b) :
    curveBilin x ((1 - c) • y + c • z) a b =
      (1 - c) * curveBilin x y a b + c * curveBilin x z a b := by
  have := opt_lsMeasure_isFinite y a b
  have := opt_lsMeasure_isFinite z a b
  have hiy : ((lsMeasure y a b).restrict (Icc a b)).Integrable x := opt_integrable_restrict_Icc hxc
  have hiz : ((lsMeasure z a b).restrict (Icc a b)).Integrable x := opt_integrable_restrict_Icc hxc
  simp only [curveBilin]
  rw [opt_lsMeasure_comb hab hy hz hw, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
    VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure
      (hiy.smul_vectorMeasure _) (hiz.smul_vectorMeasure _),
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    smul_eq_mul, smul_eq_mul]
  ring

/-- `𝓑(x, y)` is affine in `x`. -/
lemma opt_curveBilin_comb_left {x z y : ℝ → ℝ × ℝ} {a b c : ℝ}
    (hx : ContinuousOn x (Icc a b)) (hz : ContinuousOn z (Icc a b)) :
    curveBilin ((1 - c) • x + c • z) y a b =
      (1 - c) * curveBilin x y a b + c * curveBilin z y a b := by
  have := opt_lsMeasure_isFinite y a b
  have hx' : ((lsMeasure y a b).restrict (Icc a b)).Integrable x := opt_integrable_restrict_Icc hx
  have hz' : ((lsMeasure y a b).restrict (Icc a b)).Integrable z := opt_integrable_restrict_Icc hz
  unfold curveBilin
  have e : (fun t => ((1 - c) • x + c • z) t) = fun t => (1 - c) • x t + c • z t := rfl
  have hx'' : ((lsMeasure y a b).restrict (Icc a b)).Integrable (fun t => (1 - c) • x t) :=
    hx'.smul (1 - c)
  have hz'' : ((lsMeasure y a b).restrict (Icc a b)).Integrable (fun t => c • z t) := hz'.smul c
  rw [e, VectorMeasure.integral_fun_add hx'' hz'',
    VectorMeasure.integral_fun_smul, VectorMeasure.integral_fun_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `q × p = -(p × q)` for the cross product pairing. -/
lemma opt_crossCLM_flip : (crossCLM.flip : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) = -crossCLM := by
  refine ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => ?_
  simp only [ContinuousLinearMap.flip_apply, neg_apply, crossCLM_apply, cross]
  ring

/-- Integration by parts for the curve bilinear form:
`𝓑(x, y) - 𝓑(y, x) = ½ (x(b) × y(b) - x(a) × y(a))`. -/
lemma opt_curveBilin_antisymm {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) (hx : IsCBV x a b)
    (hy : IsCBV y a b) :
    curveBilin x y a b - curveBilin y x a b =
      (1 / 2) * (cross (x b) (y b) - cross (x a) (y a)) := by
  have hfx := opt_clampFun_bv hab hx.2
  have hfy := opt_clampFun_bv hab hy.2
  have hcx := opt_clampFun_continuous hab hx.1
  have hcy := opt_clampFun_continuous hab hy.1
  have key := hfx.setIntegral_Icc_leftLim_vectorMeasure_eq_sub hfy (B := crossCLM) hab
  have e1 : ∫ᵛ t in Icc a b, Function.leftLim (clampFun x a b) t ∂[crossCLM; hfy.vectorMeasure] =
      ∫ᵛ t in Icc a b, x t ∂[crossCLM; lsMeasure y a b] := by
    rw [opt_lsMeasure_eq hab hy.2]
    apply VectorMeasure.setIntegral_congr_fun
    intro t ht
    rw [opt_leftLim_eq hcx, opt_clampFun_eqOn x ht]
  have e2 : ∫ᵛ t in Icc a b, Function.rightLim (clampFun y a b) t
      ∂[crossCLM.flip; hfx.vectorMeasure] = -∫ᵛ t in Icc a b, y t ∂[crossCLM; lsMeasure x a b] := by
    rw [opt_crossCLM_flip, VectorMeasure.integral_neg_cbm, opt_lsMeasure_eq hab hx.2]
    congr 1
    apply VectorMeasure.setIntegral_congr_fun
    intro t ht
    rw [opt_rightLim_eq hcy, opt_clampFun_eqOn y ht]
  rw [e1, e2, opt_rightLim_eq hcx, opt_rightLim_eq hcy, opt_leftLim_eq hcx, opt_leftLim_eq hcy,
    opt_clampFun_eqOn x ⟨hab, le_rfl⟩, opt_clampFun_eqOn y ⟨hab, le_rfl⟩,
    opt_clampFun_eqOn x ⟨le_rfl, hab⟩, opt_clampFun_eqOn y ⟨le_rfl, hab⟩] at key
  unfold curveBilin
  rw [key]
  simp only [crossCLM_apply]
  ring

/-- **Theorem 8.5.4** (`thm:variation-curve`). The curve area functional is quadratic on `C^BV[a, b]`
with directional derivative `∫_a^b (𝐱* - 𝐱) × d𝐱 + [𝒥(𝐱(b), 𝐱*(b)) - 𝒥(𝐱(a), 𝐱*(a))]`. -/
theorem theorem8_5_4 {a b : ℝ} (hab : a ≤ b) :
    (cbvDomain a b).IsQuadratic (fun x => curveArea x.1 a b) ∧
      ∀ x xs : CBV a b, (cbvDomain a b).dirDeriv (fun x => curveArea x.1 a b) x xs =
        (∫ᵛ t in Icc a b, (xs.1 t - x.1 t) ∂[crossCLM; lsMeasure x.1 a b]) +
          (segArea (x.1 b) (xs.1 b) - segArea (x.1 a) (xs.1 a)) := by
  refine ⟨proposition7_2_2 hab, fun x xs => ?_⟩
  have hg : (cbvDomain a b).IsConvexBilinear (cbvDomain a b) realDomain
      (fun x y : CBV a b => curveBilin x.1 y.1 a b) := by
    constructor
    · intro x c hc y z
      exact opt_curveBilin_comb_right hab x.2.1 y.2 z.2 ((cbvDomain a b).comb c y z).2
    · intro y c hc x z
      exact opt_curveBilin_comb_left x.2.1 z.2.1
  rw [opt_dirDeriv_eq (opt_quadratic_hasDerivWithinAt hg (fun v => rfl) x xs)]
  have := opt_lsMeasure_isFinite x.1 a b
  have hi1 : ((lsMeasure x.1 a b).restrict (Icc a b)).Integrable xs.1 :=
    opt_integrable_restrict_Icc xs.2.1
  have hi2 : ((lsMeasure x.1 a b).restrict (Icc a b)).Integrable x.1 :=
    opt_integrable_restrict_Icc x.2.1
  rw [VectorMeasure.integral_fun_sub hi1 hi2]
  have hanti := opt_curveBilin_antisymm hab x.2 xs.2
  simp only [curveBilin, segArea] at hanti ⊢
  linarith

/-- **Theorem 8.5.5** (`thm:variation-inner-corner`). With `I = [φ^R, φ^L]`, `𝒥(𝐱_K|_I)` is quadratic on
`𝒦^i` with directional derivative
`⟨h_{K*} - h_K, ι_K⟩_{I ∪ (I + π/2)} + [𝒥(𝐱_K^L, 𝐱_{K*}^L) - 𝒥(𝐱_K^R, 𝐱_{K*}^R)]`. -/
theorem theorem8_5_5 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    kiDomain.IsQuadratic (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) ∧
      ∀ K Ks : KiSet,
        kiDomain.dirDeriv (fun K => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) K Ks =
          (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
              (supp Ks.1.1 t - supp K.1.1 t) * iFun K.1.1 t) +
            (segArea (xLeft φ K.1.1) (xLeft φ Ks.1.1) - segArea (xRight φ K.1.1) (xRight φ Ks.1.1)) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hab : φ < π / 2 - φ := by linarith
  have hb : π / 2 - φ < π / 2 := by linarith
  refine ⟨opt_isQuadratic_comp
    (opt_isConvexLinear_comp opt_projKi_linear (opt_innerCBV_linear φ (π / 2 - φ)))
    (proposition7_2_2 hab.le), fun K Ks => ?_⟩
  have hd : HasDerivWithinAt
      (fun c => curveArea (innerCorner (kiDomain.comb c K Ks).1.1) φ (π / 2 - φ))
      (opt_J K.1.1 Ks.1.1 φ (π / 2 - φ) / 2 + opt_J Ks.1.1 K.1.1 φ (π / 2 - φ) / 2 -
        2 * (opt_J K.1.1 K.1.1 φ (π / 2 - φ) / 2)) (Icc 0 1) 0 := by
    apply opt_poly_hasDerivWithinAt (D := opt_J Ks.1.1 Ks.1.1 φ (π / 2 - φ) / 2)
    intro c hc
    have hcomb := theorem8_1_1_convex K.2 Ks.2 hc
    show curveArea (innerCorner (kiComb c K Ks).1.1) φ (π / 2 - φ) = _
    rw [opt_kiComb_val hc, opt_curveArea_inner_J hcomb.2.1.2.1 hφ0 hab hb,
      opt_J_comb K.2 Ks.2 hc hφ0 hab hb]
    ring
  rw [opt_dirDeriv_eq hd, ← opt_J_iota ⟨hφ0, hφ4⟩ K.2 Ks.2]
  have hs := opt_J_swap K.2 Ks.2 hφ0 hab hb
  simp only [xLeft, xRight, segArea]
  linarith

/-! ### Assembling the directional derivative of `𝒬` (package I) -/

/-- On the `σ̆`-side: `⟨h̆_{C'} - h̆_C, σ̆_C⟩_{(a, b)} = ⟨h_{C'} - h_C, σ_C⟩_{(a + π, b + π)}`. -/
lemma opt_breve_integral (C C' : Set (ℝ × ℝ)) {a b a' b' : ℝ} (ha : a' = a + π)
    (hb : b' = b + π) :
    ∫ t in Ioo a b, (suppBreve C' t - suppBreve C t) ∂(sigmaBreve C) =
      ∫ t in Ioo a' b', (supp C' t - supp C t) ∂(sigma C) := by
  rw [sigmaBreve, (measurableEmbedding_subRight π).setIntegral_map]
  have e : (fun t : ℝ => t - π) ⁻¹' Ioo a b = Ioo a' b' := by
    ext t
    simp only [mem_preimage, mem_Ioo, ha, hb]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [e]
  simp only [suppBreve, sub_add_cancel]

/-- For `(K, B, D) ∈ 𝓛`: `h_B(3π/2) = h_D(3π/2) = 0`. -/
lemma opt_inL_supp_three_pi_div_two {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    supp B (3 * π / 2) = 0 ∧ supp D (3 * π / 2) = 0 := by
  obtain ⟨hK, -, -, -, -, -, -, e1', -, e2, -⟩ := h
  have hK2 : supp K (π / 2) = 1 := hK.1.2.2.2.1
  rw [add_zero, add_zero, hK2] at e2
  rw [hK2, show π + π / 2 = 3 * π / 2 by ring] at e1'
  constructor <;> linarith

/-- If `h_C(3π/2) = 0`, the vertex `v_C⁺(3π/2)` lies on the `x`-axis. -/
lemma opt_snd_vplus_three_pi_div_two {C : Set (ℝ × ℝ)} (h : supp C (3 * π / 2) = 0) :
    (vplus C (3 * π / 2)).2 = 0 := by
  have e := dot_vplus_uvec C (3 * π / 2)
  rw [opt_uvec_three_pi_div_two, h, opt_dot_mk] at e
  linarith

/-- If `h_C(3π/2) = 0`, the vertex `v_C⁻(3π/2)` lies on the `x`-axis. -/
lemma opt_snd_vminus_three_pi_div_two {C : Set (ℝ × ℝ)} (h : supp C (3 * π / 2) = 0) :
    (vminus C (3 * π / 2)).2 = 0 := by
  have e := dot_vminus_uvec C (3 * π / 2)
  rw [opt_uvec_three_pi_div_two, h, opt_dot_mk] at e
  linarith

/-- The projection `(K, B, D) ↦ K` from `𝓛` to `𝒦^i` is convex-linear. -/
lemma opt_projLKi_linear (φ : ℝ) :
    (lDomain φ).IsConvexLinear kiDomain (fun x : LTriple φ => (⟨x.1.1, x.2.1⟩ : KiSet)) := by
  intro c hc x y
  apply Subtype.ext
  show ((lDomain φ).comb c x y).1.1 = (kiComb c ⟨x.1.1, x.2.1⟩ ⟨y.1.1, y.2.1⟩).1
  simp only [kiComb, hc, ↓reduceDIte]
  exact opt_projK_linear φ c hc x y

/-- Pairing two convex-linear maps into `ℝ²` gives a convex-linear map into `ℝ² × ℝ²`. -/
lemma opt_isConvexLinear_pair {U : Type} {D : ConvexDomain U} {P Q : U → ℝ × ℝ}
    (hP : D.IsConvexLinear (vectorDomain (ℝ × ℝ)) P)
    (hQ : D.IsConvexLinear (vectorDomain (ℝ × ℝ)) Q) :
    D.IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ))) (fun v => (P v, Q v)) := by
  intro c hc v w
  show (P (D.comb c v w), Q (D.comb c v w)) = (1 - c) • (P v, Q v) + c • (P w, Q w)
  rw [hP c hc, hQ c hc]
  rfl

/-- **Theorem 8.5.6** (`thm:variation-a2`). If `(K, B, D) ∈ 𝓛` has `X_B = 𝐱_K^R` and `Y_D = 𝐱_K^L`, the
directional derivative of `𝒬` towards `(K*, B*, D*) ∈ 𝓛` is
`⟨h_{K*} - h_K, σ_K⟩_{[0,π]} - ⟨h_{K*} - h_K, ι_K⟩_{I ∪ (I + π/2)} + ⟨h̆_{B*} - h̆_B, σ̆_B⟩_{(φ^R, π/2)}
+ ⟨h̆_{D*} - h̆_D, σ̆_D⟩_{(π/2, π/2 + φ^L)}`. -/
theorem theorem8_5_6 {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (x xs : LTriple φ)
    (hX : xB φ x.1.2.1.1 = xRight φ x.1.1.1) (hY : yD φ x.1.2.2.1 = xLeft φ x.1.1.1) :
    (lDomain φ).dirDeriv (upperQL φ) x xs =
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) -
        (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (∫ t in Ioo φ (π / 2),
          (suppBreve xs.1.2.1.1 t - suppBreve x.1.2.1.1 t) ∂(sigmaBreve x.1.2.1.1)) +
        (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - φ)),
          (suppBreve xs.1.2.2.1 t - suppBreve x.1.2.2.1 t) ∂(sigmaBreve x.1.2.2.1)) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  -- (1) `|K|`, by Theorem 8.5.1
  have d1 : HasDerivWithinAt (fun c => area ((lDomain φ).comb c x xs).1.1.1)
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) (Icc 0 1) 0 := by
    have h := opt_quadratic_differentiableWithinAt theorem8_5_1.1
      (⟨x.1.1, x.2.1⟩ : KiSet) (⟨xs.1.1, xs.2.1⟩ : KiSet)
    rw [theorem8_5_1.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs) (f := fun K : KiSet => area K.1.1)
      (opt_projLKi_linear φ) h
  -- (2) `𝒥(𝐝_D)`, by Theorem 8.5.2
  have d2 : HasDerivWithinAt
      (fun c => convexCurveArea ((lDomain φ).comb c x xs).1.2.2.1 (3 * π / 2)
        (3 * π / 2 + (π / 2 - φ)))
      ((∫ t in Ioo (3 * π / 2) (3 * π / 2 + (π / 2 - φ)),
          (supp xs.1.2.2.1 t - supp x.1.2.2.1 t) ∂(sigma x.1.2.2.1)) +
        (segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1) -
          segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2)))) (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ)) (by linarith)
    have h := opt_quadratic_differentiableWithinAt hT.1 x.1.2.2 xs.1.2.2
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ)))
      (opt_projD_linear φ) h
  -- (3) `𝒥(Y_D, 𝐱_K^L)`, by Theorem 8.5.3
  have hP3 : (lDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : LTriple φ => (yD φ v.1.2.2.1, xLeft φ v.1.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : LTriple φ => v.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (opt_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun v : LTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (opt_projK_linear φ) (opt_innerCorner_linear _))
  have d3 : HasDerivWithinAt
      (fun c => segArea (yD φ ((lDomain φ).comb c x xs).1.2.2.1)
        (xLeft φ ((lDomain φ).comb c x xs).1.1.1))
      ((1 / 2) * (cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1) (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) -
          2 * cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_differentiableWithinAt theorem8_5_3.1
      (yD φ x.1.2.2.1, xLeft φ x.1.1.1) (yD φ xs.1.2.2.1, xLeft φ xs.1.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP3 h
  -- (4) `𝒥(𝐱_K|_{[φ^R, φ^L]})`, by Theorem 8.5.5
  have d4 : HasDerivWithinAt
      (fun c => curveArea (innerCorner ((lDomain φ).comb c x xs).1.1.1) φ (π / 2 - φ))
      ((∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have hT := theorem8_5_5 ⟨hφ0, hφ4⟩
    have h := opt_quadratic_differentiableWithinAt hT.1
      (⟨x.1.1, x.2.1⟩ : KiSet) (⟨xs.1.1, xs.2.1⟩ : KiSet)
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : KiSet => curveArea (innerCorner K.1.1) φ (π / 2 - φ)) (opt_projLKi_linear φ) h
  -- (5) `𝒥(𝐱_K^R, X_B)`, by Theorem 8.5.3
  have hP5 : (lDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : LTriple φ => (xRight φ v.1.1.1, xB φ v.1.2.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : LTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (opt_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun v : LTriple φ => v.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (opt_projB_linear φ) (opt_vplus_linear _))
  have d5 : HasDerivWithinAt
      (fun c => segArea (xRight φ ((lDomain φ).comb c x xs).1.1.1)
        (xB φ ((lDomain φ).comb c x xs).1.2.1.1))
      ((1 / 2) * (cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1) (xB φ x.1.2.1.1 - xRight φ x.1.1.1) -
          2 * cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) +
        (segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_differentiableWithinAt theorem8_5_3.1
      (xRight φ x.1.1.1, xB φ x.1.2.1.1) (xRight φ xs.1.1.1, xB φ xs.1.2.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP5 h
  -- (6) `𝒥(𝐛_B)`, by Theorem 8.5.2
  have d6 : HasDerivWithinAt
      (fun c => convexCurveArea ((lDomain φ).comb c x xs).1.2.1.1 (π + φ) (3 * π / 2))
      ((∫ t in Ioo (π + φ) (3 * π / 2), (supp xs.1.2.1.1 t - supp x.1.2.1.1 t) ∂(sigma x.1.2.1.1)) +
        (segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) -
          segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1))) (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := π + φ) (b := 3 * π / 2) (by linarith)
    have h := opt_quadratic_differentiableWithinAt hT.1 x.1.2.1 xs.1.2.1
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (π + φ) (3 * π / 2))
      (opt_projB_linear φ) h
  have hd : HasDerivWithinAt (fun c => upperQL φ ((lDomain φ).comb c x xs)) _ (Icc 0 1) 0 :=
    ((((d1.add d2).add d3).sub d4).add d5).add d6
  rw [opt_dirDeriv_eq hd]
  -- the boundary terms telescope
  have z1 : segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2)) = 0 :=
    opt_segArea_xaxis (opt_snd_vplus_three_pi_div_two (opt_inL_supp_three_pi_div_two x.2).2)
      (opt_snd_vplus_three_pi_div_two (opt_inL_supp_three_pi_div_two xs.2).2)
  have z2 : segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) = 0 :=
    opt_segArea_xaxis (opt_snd_vminus_three_pi_div_two (opt_inL_supp_three_pi_div_two x.2).1)
      (opt_snd_vminus_three_pi_div_two (opt_inL_supp_three_pi_div_two xs.2).1)
  have c3 : cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1) (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) = 0 := by
    rw [hY, sub_self]; simp [cross]
  have c3' : cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1) = 0 := by rw [hY, cross_self]
  have c5 : cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1) (xB φ x.1.2.1.1 - xRight φ x.1.1.1) = 0 := by
    rw [hX, sub_self]; simp [cross]
  have c5' : cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1) = 0 := by rw [hX, cross_self]
  have b1 := opt_breve_integral x.1.2.1.1 xs.1.2.1.1 (a := φ) (b := π / 2) (a' := π + φ)
    (b' := 3 * π / 2) (by ring) (by ring)
  have b2 := opt_breve_integral x.1.2.2.1 xs.1.2.2.1 (a := π / 2) (b := π / 2 + (π / 2 - φ))
    (a' := 3 * π / 2) (b' := 3 * π / 2 + (π / 2 - φ)) (by ring) (by ring)
  rw [b1, b2, z1, z2, c3, c3', c5, c5']
  ring

end MovingSofaOptimality
