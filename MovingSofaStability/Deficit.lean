module

public import MovingSofaStability.WideDomain

/-!
# The deficit of 𝒬 at Gerver's triple

The first variation of `𝒬` at Gerver's triple, which makes Gerver's triple the maximum of `𝒬` on
`T̄` (`wideUpperQ_le_gerver`), and the deficit `|G| - 𝒬(ξ)` as a nonnegative dual slack plus the
squared differences of Mamikon displacements, the residual energies
(`wide_deficit_eq_slack_add_integrals`). The last two sections prepare the cap estimate: the
residuals of a difference of support functions, which are these differences of displacements, and
three elementary inequalities.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness GerverParams

namespace MovingSofaStability

/-! ## The core term towards a convex body

Baek's Theorem 8.5.5 when the competitor is only a convex body. Every derivative below belongs to
the reference cap, which is in `Ki`. -/

/-- The integrand of `opt_J K₁ K₂` is integrable when `K₁` is a convex body and `K₂ ∈ Ki`. -/
theorem reference_J_integrable {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsKi K₂) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < π / 2) :
    IntervalIntegrable (fun t => cross (innerCorner K₁ t) (deriv (innerCorner K₂) t))
      volume a b :=
  (continuousOn_cross (opt_innerCorner_continuous h₁).continuousOn
    (opt_inj_deriv_continuousOn h₂.2.1.2.1 ha hb)).intervalIntegrable_of_Icc hab.le

/-- On `I = [φ, π/2 - φ]`, `opt_J Ks K - opt_J K K` is the integral of `h_{Ks} - h_K` against the
density `i_K` on `I ∪ (I + π/2)`. -/
theorem reference_J_iota {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K Ks : Set (ℝ × ℝ)} (hK : IsKi K) (hKs : IsConvexBody Ks) :
    opt_J Ks K φ (π / 2 - φ) - opt_J K K φ (π / 2 - φ) =
      ∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
        (supp Ks t - supp K t) * iFun K t := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hab : φ < π / 2 - φ := by linarith
  have hb : π / 2 - φ < π / 2 := by linarith
  have hcK := continuous_supp hK.1.2.1.2.1
  have hcKs := continuous_supp hKs.2.1
  have hdc := opt_inj_deriv_continuousOn hK.2.1.2.1 hφ0 hb
  set F : ℝ → ℝ := fun t => (supp Ks t - supp K t) * iFun K t with hF
  have hL : opt_J Ks K φ (π / 2 - φ) - opt_J K K φ (π / 2 - φ) =
      ∫ t in φ..(π / 2 - φ), (F t + F (t + π / 2)) := by
    rw [opt_J, opt_J, ← intervalIntegral.integral_sub (reference_J_integrable hKs hK hφ0 hab hb)
      (reference_J_integrable hK.1.2.1 hK hφ0 hab hb)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab.le] at ht
    simp only [hF, iFun, show t ≤ π / 2 by linarith [ht.2], ↓reduceIte,
      show ¬(t + π / 2 ≤ π / 2) by linarith [ht.1], add_sub_cancel_right]
    rw [proposition2_2_2_innerCorner, proposition2_2_2_innerCorner]
    simp only [cross, dot, uvec, vvec, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hF1 : ContinuousOn F (Icc φ (π / 2 - φ)) := by
    have h0 : ContinuousOn
        (fun t => (supp Ks t - supp K t) * dot (deriv (innerCorner K) t) (vvec t))
        (Icc φ (π / 2 - φ)) :=
      (hcKs.sub hcK).continuousOn.mul
        (continuous_dot_pair.comp_continuousOn (hdc.prodMk continuous_vvec.continuousOn))
    refine h0.congr fun t ht => ?_
    simp only [hF, iFun, show t ≤ π / 2 by linarith [ht.2], ↓reduceIte]
  have hF2 : ContinuousOn F (Icc (φ + π / 2) (π - φ)) := by
    have hd2 : ContinuousOn (fun t => deriv (innerCorner K) (t - π / 2))
        (Icc (φ + π / 2) (π - φ)) :=
      hdc.comp (continuous_sub_right _).continuousOn
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have h0 : ContinuousOn (fun t => (supp Ks t - supp K t) *
        -dot (deriv (innerCorner K) (t - π / 2)) (uvec (t - π / 2)))
        (Icc (φ + π / 2) (π - φ)) :=
      (hcKs.sub hcK).continuousOn.mul
        (continuous_dot_pair.comp_continuousOn (hd2.prodMk
          (continuous_uvec.comp (continuous_sub_right _)).continuousOn)).neg
    refine h0.congr fun t ht => ?_
    simp only [hF, iFun, show ¬(t ≤ π / 2) by linarith [ht.1], ↓reduceIte]
  have hF2' : ContinuousOn (fun t => F (t + π / 2)) (Icc φ (π / 2 - φ)) :=
    hF2.comp (continuous_id.add continuous_const).continuousOn
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  rw [hL, setIntegral_union (Set.disjoint_left.2 fun t h1 h2 => by linarith [h1.2, h2.1])
      measurableSet_Icc hF1.integrableOn_Icc hF2.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_add (hF1.intervalIntegrable_of_Icc hab.le)
      (hF2'.intervalIntegrable_of_Icc hab.le),
    intervalIntegral.integral_comp_add_right F (π / 2),
    show π / 2 - φ + π / 2 = π - φ by ring]

/-- The vector-measure integral against the core of `K ∈ Ki` has its classical density. -/
theorem reference_inner_measureIntegral {K Ks : Set (ℝ × ℝ)}
    (hK : IsKi K) (hKs : IsConvexBody Ks) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < π / 2) :
    (∫ᵛ t in Icc a b, (innerCorner Ks t - innerCorner K t)
        ∂[crossCLM; lsMeasure (innerCorner K) a b]) =
      opt_J Ks K a b - opt_J K K a b := by
  have h2 := hK.2.1.2.1
  have hψc : ContinuousOn (deriv (innerCorner K)) (Icc a b) :=
    opt_inj_deriv_continuousOn h2 ha hb
  have hψ : IntegrableOn (deriv (innerCorner K)) (Icc a b) := hψc.integrableOn_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hψc
  have hψM : ∀ t ∈ Icc a b, ‖deriv (innerCorner K) t‖ ≤ M.toNNReal := fun t ht =>
    (hM t ht).trans (Real.le_coe_toNNReal M)
  have hx : ∀ t ∈ Icc a b,
      innerCorner K t = innerCorner K a + ∫ s in a..t, deriv (innerCorner K) s := by
    intro t ht
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
        rw [uIcc_of_le ht.1] at hs
        exact opt_inj_hasDerivAt h2 ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩)
      ((hψc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1)]
    abel
  obtain ⟨hbv, hxc⟩ := cvx_bv_of_primitive hab.le hψ hψM hx
  have hg : IntegrableOn (fun t => innerCorner Ks t - innerCorner K t) (Icc a b) :=
    ((opt_innerCorner_continuous hKs).sub
      (opt_innerCorner_continuous hK.1.2.1)).continuousOn.integrableOn_Icc
  rw [cvx_lsMeasure_eq_withDensityᵥ hab.le hψ hx hbv hxc,
    cvx_withDensityᵥ_restrict hψ measurableSet_Icc,
    Measure.restrict_restrict_of_subset subset_rfl,
    cvx_integral_withDensityᵥ hψ (ae_restrict_of_forall_mem measurableSet_Icc hψM) crossCLM hg,
    integral_Icc_eq_integral_Ioc, opt_J, opt_J,
    ← intervalIntegral.integral_sub (reference_J_integrable hKs hK ha hab hb)
      (reference_J_integrable hK.1.2.1 hK ha hab hb),
    intervalIntegral.integral_of_le hab.le]
  congr 1
  funext t
  simp only [crossCLM_apply, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- A quadratic functional composed with a convex-linear map has its directional derivative as a
one-sided derivative along segments. -/
private theorem quadratic_comp_hasDerivWithinAt {V W : Type} {D₁ : ConvexDomain V}
    {D₂ : ConvexDomain W} {f : W → ℝ} {pr : V → W} (hf : D₂.IsQuadratic f)
    (hpr : D₁.IsConvexLinear D₂ pr) (x xs : V) {d : ℝ}
    (hd : D₂.dirDeriv f (pr x) (pr xs) = d) :
    HasDerivWithinAt (fun c => f (pr (D₁.comb c x xs))) d (Icc 0 1) 0 :=
  opt_hasDerivWithinAt_comp hpr (hd ▸ opt_quadratic_hasDerivWithinAt hf _ _)

/-- The core term `𝒥(𝐱_K|_I)` is quadratic on convex bodies; at `K ∈ Ki` its directional derivative
towards any convex body is the integral of `h_{Ks} - h_K` against `i_K` plus two end segments. -/
theorem reference_core_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    convexBodyDomain.IsQuadratic (fun K => curveArea (innerCorner K.1) φ (π / 2 - φ)) ∧
    ∀ K Ks : ConvexBodySet, IsKi K.1 →
      convexBodyDomain.dirDeriv (fun C => curveArea (innerCorner C.1) φ (π / 2 - φ)) K Ks =
        (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp Ks.1 t - supp K.1 t) * iFun K.1 t) +
        (segArea (xLeft φ K.1) (xLeft φ Ks.1) - segArea (xRight φ K.1) (xRight φ Ks.1)) := by
  have hab : φ < π / 2 - φ := by linarith [hφ.2, pi_pos]
  have hb : π / 2 - φ < π / 2 := by linarith [hφ.1]
  have hlin := opt_innerCBV_linear φ (π / 2 - φ)
  have hT := theorem8_5_4 hab.le
  refine ⟨opt_isQuadratic_comp hlin hT.1, fun K Ks hK => ?_⟩
  have hd : HasDerivWithinAt
      (fun c => curveArea (innerCorner (convexBodyDomain.comb c K Ks).1) φ (π / 2 - φ))
      ((∫ᵛ t in Icc φ (π / 2 - φ), (innerCorner Ks.1 t - innerCorner K.1 t)
          ∂[crossCLM; lsMeasure (innerCorner K.1) φ (π / 2 - φ)]) +
        (segArea (xLeft φ K.1) (xLeft φ Ks.1) - segArea (xRight φ K.1) (xRight φ Ks.1)))
      (Icc 0 1) 0 :=
    quadratic_comp_hasDerivWithinAt hT.1 hlin K Ks (hT.2 _ _)
  rw [opt_dirDeriv_eq hd, reference_inner_measureIntegral hK Ks.2 hφ.1 hab hb,
    reference_J_iota hφ hK Ks.2]

/-! ## The first variation of `𝒬` on the enlarged domain -/

/-- Baek's Theorem 8.5.6 on the enlarged domain: the first variation of `𝒬` at a triple whose cap
is in `Ki` and whose tails meet its core, towards any triple of the enlarged domain. -/
theorem wide_reference_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x xs : WideTriple φ) (hK : IsKi x.1.1.1)
    (hX : xB φ x.1.2.1.1 = xRight φ x.1.1.1)
    (hY : yD φ x.1.2.2.1 = xLeft φ x.1.1.1) :
    (wideDomain φ).dirDeriv (wideUpperQ φ) x xs =
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) -
        (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (∫ t in Ioo φ (π / 2),
          (suppBreve xs.1.2.1.1 t - suppBreve x.1.2.1.1 t) ∂(sigmaBreve x.1.2.1.1)) +
        (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - φ)),
          (suppBreve xs.1.2.2.1 t - suppBreve x.1.2.2.1 t) ∂(sigmaBreve x.1.2.2.1)) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hB := theorem8_5_2 (a := π + φ) (b := 3 * π / 2) (by linarith) (by linarith)
  have hD := theorem8_5_2 (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ)) (by linarith)
    (by linarith)
  have hC := reference_core_firstVariation ⟨hφ0, hφ4⟩
  have hYL : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (yD φ v.1.2.2.1, xLeft φ v.1.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (wide_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (wide_projK_linear φ) (opt_innerCorner_linear _))
  have hXB : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (xRight φ v.1.1.1, xB φ v.1.2.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (wide_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (wide_projB_linear φ) (opt_vplus_linear _))
  -- the six terms of `𝒬`: `|K|`, `𝒥(𝐝_D)`, `𝒥(Y_D, 𝐱_K^L)`, `𝒥(𝐱_K|_I)`, `𝒥(𝐱_K^R, X_B)`, `𝒥(𝐛_B)`
  have hd : HasDerivWithinAt (fun c => wideUpperQ φ ((wideDomain φ).comb c x xs)) _ (Icc 0 1) 0 :=
    (((((quadratic_comp_hasDerivWithinAt theorem7_1_3_quadratic (wide_projK_linear φ) x xs
      (area_firstVariation_caps x.1.1 xs.1.1 x.2.1 xs.2.1)).add
      (quadratic_comp_hasDerivWithinAt hD.1 (wide_projD_linear φ) x xs (hD.2 _ _))).add
      (quadratic_comp_hasDerivWithinAt theorem8_5_3.1 hYL x xs (theorem8_5_3.2 _ _))).sub
      (quadratic_comp_hasDerivWithinAt hC.1 (wide_projK_linear φ) x xs (hC.2 _ _ hK))).add
      (quadratic_comp_hasDerivWithinAt theorem8_5_3.1 hXB x xs (theorem8_5_3.2 _ _))).add
      (quadratic_comp_hasDerivWithinAt hB.1 (wide_projB_linear φ) x xs (hB.2 _ _))
  have z1 : segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two (inWideL_supp x.2).2.1)
      (opt_snd_vplus_three_pi_div_two (inWideL_supp xs.2).2.1)
  have z2 : segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vminus_three_pi_div_two (inWideL_supp x.2).1)
      (opt_snd_vminus_three_pi_div_two (inWideL_supp xs.2).1)
  rw [opt_dirDeriv_eq hd, opt_breve_integral x.1.2.1.1 xs.1.2.1.1 (a := φ) (b := π / 2)
      (a' := π + φ) (b' := 3 * π / 2) (by ring) (by ring),
    opt_breve_integral x.1.2.2.1 xs.1.2.2.1 (a := π / 2) (b := π / 2 + (π / 2 - φ))
      (a' := 3 * π / 2) (b' := 3 * π / 2 + (π / 2 - φ)) (by ring) (by ring)]
  -- the end segments telescope, as the tails meet the core
  simp only [xB, yD] at hX hY ⊢
  rw [z1, z2, hX, hY]
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-! ## Gerver's triple maximizes `𝒬` on the enlarged domain -/

/-- Gerver's triple `(K_G, B_{K_G}, D_{K_G})`, as a triple of the enlarged domain. -/
def wideGerverTriple {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : WideTriple P.φ :=
  toWideTriple (gerverTriple hP hbox)

/-- At Gerver's triple, the directional derivative of `𝒬` towards any triple of the enlarged domain
is nonpositive. -/
theorem gerver_wide_firstVariation_nonpos {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (xs : WideTriple P.φ) :
    (wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) xs ≤ 0 := by
  obtain ⟨h1, -, -, -, h4, -, -, -⟩ := theorem8_4_3_two hP hbox
  rw [wide_reference_firstVariation (gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox) xs (gerverTriple hP hbox).2.1 h4.symm h1.symm]
  have hL : InWideL P.φ xs.1.1.1 xs.1.2.1.1 xs.1.2.2.1 := xs.2
  have h01 := gm_φ_pos hP
  have h12 := gm_φ_lt_θ hP
  have h23 := gm_θ_lt_c hP
  have hpi := pi_pos
  set f : ℝ → ℝ := fun t => supp xs.1.1.1 t - supp P.cap t with hf
  set gB : ℝ → ℝ := fun t => suppBreve xs.1.2.1.1 t -
    suppBreve (rightBody P.φ P.cap) t with hgB
  set gD : ℝ → ℝ := fun t => suppBreve xs.1.2.2.1 t -
    suppBreve (leftBody P.φ P.cap) t with hgD
  have hfc : Continuous f :=
    (continuous_supp xs.1.1.2.2.1).sub (continuous_supp (gm_isConvexBody_cap hP hbox).2.1)
  have hgBc : Continuous gB :=
    ((continuous_supp xs.1.2.1.2.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp (gm_isConvexBody_B hP hbox).2.1).comp
        (continuous_id.add continuous_const))
  have hgDc : Continuous gD :=
    ((continuous_supp xs.1.2.2.2.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp (gm_isConvexBody_D hP hbox).2.1).comp
        (continuous_id.add continuous_const))
  -- Baek's Theorem 8.4.5: on `[0, π]`, `σ_K = ι + β + δ + τ`
  set Sι := Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ)
  set ι := (iota P.cap).restrict Sι
  set β := (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2))
  set δ := (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ))
  set τ := (sigma P.cap).restrict {π / 2}
  have hdec : (sigma P.cap).restrict (Icc 0 π) = ι + β + δ + τ := gm_sigma_decomp hP hbox
  have hint : ∀ g : ℝ → ℝ, Continuous g →
      Integrable g ι ∧ Integrable g β ∧ Integrable g δ ∧ Integrable g τ := by
    intro g hg
    have h : Integrable g (ι + β + δ + τ) := by
      rw [← hdec]
      exact hg.continuousOn.integrableOn_compact isCompact_Icc
    simp only [integrable_add_measure] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  obtain ⟨iι, iβ, iδ, iτ⟩ := hint f hfc
  -- the atom at `π/2` carries nothing, as `h_{Ks}(π/2) = h_K(π/2)`
  have eI1 : (∫ t in Icc 0 π, f t ∂(sigma P.cap)) =
      (∫ t, f t ∂ι) + (∫ t, f t ∂β) + (∫ t, f t ∂δ) := by
    have he : ∫ t, f t ∂τ = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      simp only [hf, mem_singleton_iff.1 ht, hL.1.2.2.2.1, gm_supp_cap_pi_div_two hP hbox,
        sub_self]
    rw [hdec, integral_add_measure ((iι.add_measure iβ).add_measure iδ) iτ,
      integral_add_measure (iι.add_measure iβ) iδ, integral_add_measure iι iβ, he, add_zero]
  -- the part of `σ_K` with density `i_K` cancels the core term
  have eI2 : (∫ t in Sι, f t * iFun P.cap t) = ∫ t, f t ∂ι := by
    have hm : Measurable (fun t => ENNReal.ofReal (iFun P.cap t)) := by
      unfold iFun
      exact (Measurable.ite measurableSet_Iic
        (gm_measurable_dot (measurable_deriv _) (by unfold vvec; fun_prop))
        (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
          (by unfold uvec; fun_prop)).neg).ennreal_ofReal
    rw [show ι = (volume.restrict Sι).withDensity (fun t => ENNReal.ofReal (iFun P.cap t)) from
        gm_iota_restrict (measurableSet_Icc.union measurableSet_Icc) (by
          rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      integral_withDensity_eq_integral_toReal_smul hm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine setIntegral_congr_fun (measurableSet_Icc.union measurableSet_Icc) fun t ht => ?_
    have hpos : 0 ≤ iFun P.cap t := by
      rcases ht with ht | ht
      · have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_left hlo.2.le]
        exact ((theorem6_1_2 hP hbox).2.2 t hlo).2.le
      · have hτ : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_right (not_le.2 (by linarith [ht.1]))]
        linarith [((theorem6_1_2 hP hbox).2.2 _ hτ).1]
    simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  change (∫ t in Icc 0 π, f t ∂(sigma P.cap)) - (∫ t in Sι, f t * iFun P.cap t) +
      (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) +
      (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
        ∂(sigmaBreve (leftBody P.φ P.cap))) ≤ 0
  rw [eI1, eI2, gm_sigmaBreve_B_restrict hP hbox, gm_sigmaBreve_D_restrict hP hbox]
  -- what remains is nonpositive by the wall constraints and Baek's Theorem 8.4.3
  have kB : (∫ t, f t ∂β) + (∫ t, gB t ∂β) ≤ 0 := by
    rw [← integral_add iβ (hint gB hgBc).2.1]
    refine setIntegral_nonpos measurableSet_Ico fun t ht => ?_
    have h1 := hL.2.2.2.2.2.1 t ⟨by linarith [ht.1], ht.2.le⟩
    have h2 := (theorem8_4_3_three hP hbox).2 t ⟨ht.1, ht.2.le⟩
    simp only [hf, hgB, suppBreve]
    rw [add_comm t π]
    linarith
  have kD : (∫ t, f t ∂δ) + (∫ t, gD t ∂δ) ≤ 0 := by
    rw [← integral_add iδ (hint gD hgDc).2.2.1]
    refine setIntegral_nonpos measurableSet_Ioc fun t ht => ?_
    have h1 := hL.2.2.2.2.2.2.2.2.1 (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := (theorem8_4_3_three hP hbox).1 (t - π / 2)
      ⟨show (0 : ℝ) ≤ t - π / 2 by linarith [ht.1], show t - π / 2 ≤ P.θ by linarith [ht.2]⟩
    rw [show π / 2 + (t - π / 2) = t by ring,
      show 3 * π / 2 + (t - π / 2) = t + π by ring] at h1 h2
    simp only [hf, hgD, suppBreve]
    linarith
  linarith

/-- Gerver's triple maximizes `𝒬` on the enlarged domain. -/
theorem wideUpperQ_le_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ wideUpperQ P.φ (wideGerverTriple hP hbox) :=
  (wide_maximum_iff_firstVariation (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox)).2
    (gerver_wide_firstVariation_nonpos hP hbox) x

/-- The value of `𝒬` at Gerver's triple is the area of Gerver's sofa. -/
@[simp] theorem wideGerver_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    wideUpperQ P.φ (wideGerverTriple hP hbox) = area (gerverSofa P) :=
  gerver_upperQL_eq_area hP hbox

/-- The dual slack `-D𝒬(ξ_G; x)`, nonnegative by `gerver_wide_firstVariation_nonpos`. -/
def wideDualSlack {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ :=
  -(wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) x

/-! ## The deficit as dual slack plus residual energies -/

/-- The energy `E_𝒮` of the four Mamikon terms of `𝒮`, for arbitrary convex bodies. -/
def capResidualEnergy (φ : ℝ) (K₀ K₁ : ConvexBodySet) : ℝ :=
  displacementEnergy 0 φ (fun K => tangentParam K.1 (π / 2)) K₀ K₁ +
  displacementEnergy φ (π / 2 - φ) (fun K => outerCorner K.1) K₀ K₁ +
  displacementEnergy (π / 2 - φ) (π / 2)
    (fun K => tangentParam K.1 (π / 2 + (π / 2 - φ))) K₀ K₁ +
  displacementEnergy (π / 2) π (fun K => tangentParam K.1 π) K₀ K₁

/-- The energy `E_ℛ` of the Mamikon term `ℛ`. -/
def rightResidualEnergy (φ : ℝ) (B₀ B₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (π + φ) (3 * π / 2) (fun B => tangentParam B.1 (3 * π / 2)) B₀ B₁

/-- The energy `E_ℒ` of the Mamikon term `ℒ`. -/
def leftResidualEnergy (φ : ℝ) (D₀ D₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
    (fun D => tangentParam D.1 (3 * π / 2 + (π / 2 - φ))) D₀ D₁

/-- The sum of the six energies, `E_𝒮 + E_ℛ + E_ℒ`. -/
def wideResidualEnergy {φ : ℝ} (x y : WideTriple φ) : ℝ :=
  capResidualEnergy φ x.1.1 y.1.1 + rightResidualEnergy φ x.1.2.1 y.1.2.1 +
    leftResidualEnergy φ x.1.2.2 y.1.2.2

/-- The convexity gap of a Mamikon term along a fixed tangent line is its energy. -/
theorem tangent_energy_gap {a b T c : ℝ} (hab : a < b) (hb : b < a + π)
    (ha : T - π < a) (hbt : b ≤ T) (K₀ K₁ : ConvexBodySet)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (tangentParam K₀.1 T) +
      c * mamikon K₁.1 a b (tangentParam K₁.1 T) -
      mamikon (convexBodyComb c K₀ K₁).1 a b
        (tangentParam (convexBodyComb c K₀ K₁).1 T) =
      c * (1 - c) * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  refine mamikon_combo_energy hab hb (fun K => tangentParam K.1 T)
    (fun K => (theorem8_3_1 K.2 ha hab.le hbt).1) (fun K t ht => ?_)
    (fun K L s hs t ht => theorem8_3_2 hab.le hbt K L hs t ht) K₀ K₁ hc
  rcases (ht.2.trans hbt).lt_or_eq with h | rfl
  · simpa only [tangentParam, h, ↓reduceIte] using vint_mem_line_left K.1 t T
  · simp only [tangentParam, lt_irrefl, ↓reduceIte]
    exact dot_vminus_uvec K.1 t

/-- The convexity gap of the Mamikon term along the outer corner is its energy. -/
theorem outer_energy_gap {a b c : ℝ} (hab : a < b) (hb : b < a + π)
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (outerCorner K₀.1) +
      c * mamikon K₁.1 a b (outerCorner K₁.1) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (outerCorner (convexBodyComb c K₀ K₁).1) =
      c * (1 - c) * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ :=
  mamikon_combo_energy hab hb (fun K => outerCorner K.1) (fun K => opt_outerCorner_cbv K.2 a b)
    (fun K t _ => inj_dot_outerCorner_uvec K.1 t)
    (fun K L s hs t _ => by rw [cvx_convexBodyComb_val hs, opt_outerCorner_comb K.2 L.2 hs]; rfl)
    K₀ K₁ hc

/-- The convexity gap of `𝒮`, `(1 - c) 𝒮_{K₀} + c 𝒮_{K₁} - 𝒮_{(1 - c) K₀ + c K₁}`, is
`c (1 - c) E_𝒮(K₀, K₁)`. -/
theorem capResidualEnergy_gap {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikonS φ K₀.1 + c * mamikonS φ K₁.1 -
      mamikonS φ (convexBodyComb c K₀ K₁).1 = c * (1 - c) * capResidualEnergy φ K₀ K₁ := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have h1 := tangent_energy_gap (T := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h2 := outer_energy_gap (a := φ) (b := π / 2 - φ) (by linarith) (by linarith) K₀ K₁ hc
  have h3 := tangent_energy_gap (T := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h4 := tangent_energy_gap (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁ hc
  unfold mamikonS capResidualEnergy
  linarith

/-- On the enlarged domain, the segment energy of `𝒬` is the sum of the six energies. -/
theorem wideEnergy_eq_integrals {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : WideTriple φ) :
    segmentEnergy (wideDomain φ) (wideUpperQ φ) x y = wideResidualEnergy x y := by
  have hpi := pi_pos
  have ⟨hφ0, hφ4⟩ := hφ
  have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := capResidualEnergy_gap hφ x.1.1 y.1.1 hc
  have hR := tangent_energy_gap (T := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.1 y.1.2.1 hc
  have hL := tangent_energy_gap (T := 3 * π / 2 + (π / 2 - φ))
    (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ))
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.2 y.1.2.2 hc
  have hlin := cap_mamikon_upperP_affine hφ x.2.1 y.2.1 hc
  -- the midpoint triple, by components
  have eK : ((wideDomain φ).comb (1 / 2) x y).1.1 = convexBodyComb (1 / 2) x.1.1 y.1.1 :=
    wide_projK_linear φ _ hc x y
  have eB : ((wideDomain φ).comb (1 / 2) x y).1.2.1 = convexBodyComb (1 / 2) x.1.2.1 y.1.2.1 :=
    wide_projB_linear φ _ hc x y
  have eD : ((wideDomain φ).comb (1 / 2) x y).1.2.2 = convexBodyComb (1 / 2) x.1.2.2 y.1.2.2 :=
    wide_projD_linear φ _ hc x y
  unfold segmentEnergy wideResidualEnergy wideUpperQ
  rw [wide_upperQ_decomposition hφ ((wideDomain φ).comb (1 / 2) x y).2,
    wide_upperQ_decomposition hφ x.2, wide_upperQ_decomposition hφ y.2, eK, eB, eD]
  simp only [cvx_convexBodyComb_val hc] at hS hR hL ⊢
  simp only [mamikonR, mamikonL, rightResidualEnergy, leftResidualEnergy]
  linarith

/-- The deficit of `𝒬` on the enlarged domain is the dual slack plus the six residual energies. -/
theorem wide_deficit_eq_slack_add_integrals {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    area (gerverSofa P) - wideUpperQ P.φ x =
      wideDualSlack hP hbox x + wideResidualEnergy (wideGerverTriple hP hbox) x := by
  rw [← wideGerver_value hP hbox, deficit_eq_neg_dirDeriv_add_energy (wideDomain P.φ)
      (wideUpperQ_quadratic (gm_φ_mem_Ioo hP hbox)),
    wideEnergy_eq_integrals (gm_φ_mem_Ioo hP hbox)]
  rfl

/-- The energy `E_𝒮` of the cap is at most the deficit of `𝒬`. -/
theorem wide_capResidualEnergy_le_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 ≤
      area (gerverSofa P) - wideUpperQ P.φ x := by
  rw [wide_deficit_eq_slack_add_integrals hP hbox x, wideResidualEnergy]
  have hs : 0 ≤ wideDualSlack hP hbox x :=
    neg_nonneg.2 (gerver_wide_firstVariation_nonpos hP hbox x)
  have hr : 0 ≤ rightResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1 :=
    displacementEnergy_nonneg _ _ _ _ _
  have hl : 0 ≤ leftResidualEnergy P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2 :=
    displacementEnergy_nonneg _ _ _ _ _
  linarith

/-! ## Residuals and displacements -/

/-- The tangent residual `r_T(t)` of `f`, given its right derivative `df`. -/
def tangentResidual (T : ℝ) (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f T - f t * cos (T - t)) / sin (T - t) - df t

/-- The corner residual `r_c(t)` of `f`, given its right derivative `df`. -/
def cornerResidual (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (t + π / 2) - df t

/-- The pinned difference `f(t) + f(π) cos t`, which vanishes at `π`. -/
def pinnedDifference (f : ℝ → ℝ) (t : ℝ) : ℝ := f t + f π * cos t

/-- The right derivative of `pinnedDifference f`, given the right derivative `df` of `f`. -/
def pinnedDerivative (f df : ℝ → ℝ) (t : ℝ) : ℝ := df t - f π * sin t

/-- A pinned difference vanishes at `π`. -/
@[simp] theorem pinnedDifference_pi (f : ℝ → ℝ) : pinnedDifference f π = 0 := by
  simp [pinnedDifference]

/-- Pinning does not change the value at `π/2`. -/
@[simp] theorem pinnedDifference_top (f : ℝ → ℝ) :
    pinnedDifference f (π / 2) = f (π / 2) := by
  simp [pinnedDifference]

/-- Multiples of `cos`, with right derivatives the same multiples of `-sin`, have zero tangent
residuals. -/
theorem tangentResidual_translation (a T t : ℝ) (hs : sin (T - t) ≠ 0) :
    tangentResidual T (fun u => a * cos u) (fun u => -a * sin u) t = 0 := by
  have hc : cos T = cos t * cos (T - t) - sin t * sin (T - t) := by
    rw [← cos_add, add_sub_cancel]
  simp only [tangentResidual, hc]
  field_simp
  ring

/-- Pinning does not change a tangent residual: residuals are linear in the function, and those of
multiples of `cos` vanish. -/
theorem tangentResidual_pinned (T : ℝ) (f df : ℝ → ℝ) (t : ℝ)
    (hs : sin (T - t) ≠ 0) :
    tangentResidual T (pinnedDifference f) (pinnedDerivative f df) t =
      tangentResidual T f df t := by
  have h := tangentResidual_translation (f π) T t hs
  simp only [tangentResidual, pinnedDifference, pinnedDerivative] at h ⊢
  linear_combination h

/-- Pinning does not change a corner residual. -/
@[simp] theorem cornerResidual_pinned (f df : ℝ → ℝ) (t : ℝ) :
    cornerResidual (pinnedDifference f) (pinnedDerivative f df) t =
      cornerResidual f df t := by
  simp only [cornerResidual, pinnedDifference, pinnedDerivative, cos_add_pi_div_two]
  ring

/-- The difference of two tangent displacements is the tangent residual of the difference of the
support functions. -/
theorem tangent_displacement_sub {K₀ K₁ : Set (ℝ × ℝ)} {T t : ℝ} (ht : t < T) :
    displacement K₁ (tangentParam K₁ T) t - displacement K₀ (tangentParam K₀ T) t =
      tangentResidual T (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [tangent_displacement_formula K₁ ht, tangent_displacement_formula K₀ ht, tangentResidual]
  ring

/-- The difference of two outer-corner displacements is the corner residual of the difference of
the support functions. -/
theorem outer_displacement_sub (K₀ K₁ : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K₁ (outerCorner K₁) t - displacement K₀ (outerCorner K₀) t =
      cornerResidual (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [outer_displacement_formula, outer_displacement_formula, cornerResidual]
  ring

/-- The quotient `q_T(t) = (f(t) - f(T) cos (T - t)) / sin (T - t)`, whose right derivative is
`-r_T(t) / sin (T - t)`. -/
def tangentQuotient (T : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - f T * cos (T - t)) / sin (T - t)

/-- The residual `r_π` of a function vanishing at `π`. -/
theorem tangentResidual_left {f df : ℝ → ℝ} (h : f π = 0) (t : ℝ) :
    tangentResidual π f df t = cos t / sin t * f t - df t := by
  simp only [tangentResidual, h, zero_sub, cos_pi_sub, sin_pi_sub]
  ring

/-! ## Three inequalities for the cap estimate -/

/-- The Cauchy--Schwarz inequality for real functions whose squares and product are integrable. -/
theorem integral_mul_sq_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {f g : X → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  -- `∫ (f - s g)² ≥ 0` for every `s`, so the discriminant is nonpositive
  have h : ∀ s : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (s * s) + (-2 * ∫ x, f x * g x ∂μ) * s +
      ∫ x, f x ^ 2 ∂μ := by
    intro s
    have h0 : 0 ≤ ∫ x, s * s * g x ^ 2 + -2 * s * (f x * g x) + f x ^ 2 ∂μ :=
      integral_nonneg fun x => (sq_nonneg (f x - s * g x)).trans_eq (by ring)
    have hi : Integrable (fun x => s * s * g x ^ 2 + -2 * s * (f x * g x)) μ :=
      (hg.const_mul _).add (hfg.const_mul _)
    rw [integral_add hi hf, integral_add (hg.const_mul _) (hfg.const_mul _), integral_const_mul,
      integral_const_mul] at h0
    linarith
  have hd := discrim_le_zero h
  rw [discrim] at hd
  linarith

/-- The Cauchy--Schwarz inequality for four terms. -/
theorem four_term_sq_le (a b c d x y z w : ℝ) :
    (a * x + b * y + c * z + d * w) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  linarith [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x), sq_nonneg (a * w - d * x),
    sq_nonneg (b * z - c * y), sq_nonneg (b * w - d * y), sq_nonneg (c * w - d * z)]

/-- From a squared bound to a square-root bound. -/
theorem abs_le_mul_sqrt_of_sq_le {d C E : ℝ} (hC : 0 ≤ C)
    (h : d ^ 2 ≤ C ^ 2 * E) : |d| ≤ C * sqrt E := by
  simpa only [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] using Real.abs_le_sqrt h

end MovingSofaStability
