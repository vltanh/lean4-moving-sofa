module

public import MovingSofaStability.WideDomain

/-!
# The deficit of 𝒬 at Gerver's triple

The first variation of `𝒬` at Gerver's triple, which makes Gerver's triple the maximum of `𝒬` on `T̄`
(`wideUpperQ_le_gerver`), and the deficit `|G| - 𝒬(ξ)` as a nonnegative dual slack plus the squared
differences of Mamikon displacements, the residual energies (`wide_deficit_eq_slack_add_integrals`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Core first variation with a nonsmooth competing cap

Only the reference cap is in Ki. The competitor is an arbitrary convex body. The
core's vector measure belongs to the smooth reference; no derivative of the
competing corner path is assumed.
-/

section ReferenceCoreVariation

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality

namespace MovingSofaStability

/-- The first argument need only be a convex body; the second is differentiated. -/
theorem reference_J_integrable {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsKi K₂) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < π / 2) :
    IntervalIntegrable (fun t => cross (innerCorner K₁ t) (deriv (innerCorner K₂) t))
      volume a b :=
  (continuousOn_cross (opt_innerCorner_continuous h₁).continuousOn
    (opt_inj_deriv_continuousOn h₂.2.1.2.1 ha hb)).intervalIntegrable_of_Icc hab.le

/-- The core-measure formula needs regularity only on the reference K. -/
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
    simp only [opt_J]
    rw [← intervalIntegral.integral_sub (reference_J_integrable hKs hK hφ0 hab hb)
      (reference_J_integrable hK.1.2.1 hK hφ0 hab hb)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    simp only [hF, iFun, show t ≤ π / 2 by linarith [ht.2], ↓reduceIte,
      show ¬(t + π / 2 ≤ π / 2) by linarith [ht.1],
      show t + π / 2 - π / 2 = t by ring]
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
  rw [hL, setIntegral_union (by
      rw [Set.disjoint_left]; rintro t ⟨-, h1⟩ ⟨h2, -⟩; linarith)
      measurableSet_Icc hF1.integrableOn_Icc hF2.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_add (hF1.intervalIntegrable_of_Icc hab.le)
      (hF2'.intervalIntegrable_of_Icc hab.le),
    intervalIntegral.integral_comp_add_right F (π / 2),
    show π / 2 - φ + π / 2 = π - φ by ring]

/-- The vector-measure integral against the reference core has its classical density. -/
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

/-- The convex-body core functional is quadratic on the full domain. -/
theorem coreArea_quadratic {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    convexBodyDomain.IsQuadratic
      (fun K => curveArea (innerCorner K.1) φ (π / 2 - φ)) :=
  opt_isQuadratic_comp (opt_innerCBV_linear φ (π / 2 - φ))
    (proposition7_2_2 (by linarith [hφ.2, pi_pos]))

/-- The first variation at a Ki reference, towards an arbitrary convex body. -/
theorem reference_core_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K Ks : ConvexBodySet) (hK : IsKi K.1) :
    convexBodyDomain.dirDeriv
        (fun C => curveArea (innerCorner C.1) φ (π / 2 - φ)) K Ks =
      (∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
        (supp Ks.1 t - supp K.1 t) * iFun K.1 t) +
      (segArea (xLeft φ K.1) (xLeft φ Ks.1) - segArea (xRight φ K.1) (xRight φ Ks.1)) := by
  have hpi := pi_pos
  have hab : φ < π / 2 - φ := by linarith [hφ.2]
  have hb : π / 2 - φ < π / 2 := by linarith [hφ.1]
  have hlin := opt_innerCBV_linear φ (π / 2 - φ)
  have hT := theorem8_5_4 hab.le
  have hd : HasDerivWithinAt
      (fun c => curveArea (innerCorner (convexBodyDomain.comb c K Ks).1) φ (π / 2 - φ))
      ((∫ᵛ t in Icc φ (π / 2 - φ), (innerCorner Ks.1 t - innerCorner K.1 t)
          ∂[crossCLM; lsMeasure (innerCorner K.1) φ (π / 2 - φ)]) +
        (segArea (xLeft φ K.1) (xLeft φ Ks.1) - segArea (xRight φ K.1) (xRight φ Ks.1)))
      (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt hT.1 (opt_innerCBV φ (π / 2 - φ) K)
      (opt_innerCBV φ (π / 2 - φ) Ks)
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := K) (xs := Ks)
      (f := fun x : CBV φ (π / 2 - φ) => curveArea x.1 φ (π / 2 - φ)) hlin h
  rw [opt_dirDeriv_eq hd, reference_inner_measureIntegral hK Ks.2 hφ.1 hab hb,
    reference_J_iota hφ hK Ks.2]

end MovingSofaStability

end ReferenceCoreVariation

/-!
## First variation of Q on the enlarged domain

The reference cap belongs to Ki and its two tails meet its core. The competing
triple is only in the enlarged nonsmooth domain. All derivatives of corner paths
below belong to the reference cap.
-/

section WideFirstVariation

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- The nonsmooth-competitor version of source Theorem 8.5.6. -/
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
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have d1 : HasDerivWithinAt (fun c => area ((wideDomain φ).comb c x xs).1.1.1)
      (∫ t in Icc 0 π, (supp xs.1.1.1 t - supp x.1.1.1 t) ∂(sigma x.1.1.1)) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem7_1_3_quadratic x.1.1 xs.1.1
    rw [area_firstVariation_caps x.1.1 xs.1.1 x.2.1 xs.2.1] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => area K.1) (wide_projK_linear φ) h
  have d2 : HasDerivWithinAt
      (fun c => convexCurveArea ((wideDomain φ).comb c x xs).1.2.2.1 (3 * π / 2)
        (3 * π / 2 + (π / 2 - φ)))
      ((∫ t in Ioo (3 * π / 2) (3 * π / 2 + (π / 2 - φ)),
          (supp xs.1.2.2.1 t - supp x.1.2.2.1 t) ∂(sigma x.1.2.2.1)) +
        (segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1) -
          segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2))))
      (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ))
      (by linarith) (by linarith)
    have h := opt_quadratic_hasDerivWithinAt hT.1 x.1.2.2 xs.1.2.2
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ)))
      (wide_projD_linear φ) h
  have hP3 : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (yD φ v.1.2.2.1, xLeft φ v.1.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (wide_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (wide_projK_linear φ) (opt_innerCorner_linear _))
  have d3 : HasDerivWithinAt
      (fun c => segArea (yD φ ((wideDomain φ).comb c x xs).1.2.2.1)
        (xLeft φ ((wideDomain φ).comb c x xs).1.1.1))
      ((1 / 2) * (cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1)
          (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) -
          2 * cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (yD φ x.1.2.2.1) (yD φ xs.1.2.2.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem8_5_3.1
      (yD φ x.1.2.2.1, xLeft φ x.1.1.1) (yD φ xs.1.2.2.1, xLeft φ xs.1.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP3 h
  have d4 : HasDerivWithinAt
      (fun c => curveArea (innerCorner ((wideDomain φ).comb c x xs).1.1.1) φ (π / 2 - φ))
      ((∫ t in Icc φ (π / 2 - φ) ∪ Icc (φ + π / 2) (π - φ),
          (supp xs.1.1.1 t - supp x.1.1.1 t) * iFun x.1.1.1 t) +
        (segArea (xLeft φ x.1.1.1) (xLeft φ xs.1.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt (coreArea_quadratic hφ) x.1.1 xs.1.1
    rw [reference_core_firstVariation hφ x.1.1 xs.1.1 hK] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => curveArea (innerCorner K.1) φ (π / 2 - φ))
      (wide_projK_linear φ) h
  have hP5 : (wideDomain φ).IsConvexLinear (vectorDomain ((ℝ × ℝ) × (ℝ × ℝ)))
      (fun v : WideTriple φ => (xRight φ v.1.1.1, xB φ v.1.2.1.1)) :=
    opt_isConvexLinear_pair
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (wide_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun v : WideTriple φ => v.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (wide_projB_linear φ) (opt_vplus_linear _))
  have d5 : HasDerivWithinAt
      (fun c => segArea (xRight φ ((wideDomain φ).comb c x xs).1.1.1)
        (xB φ ((wideDomain φ).comb c x xs).1.2.1.1))
      ((1 / 2) * (cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1)
          (xB φ x.1.2.1.1 - xRight φ x.1.1.1) -
          2 * cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) +
        (segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1) -
          segArea (xRight φ x.1.1.1) (xRight φ xs.1.1.1))) (Icc 0 1) 0 := by
    have h := opt_quadratic_hasDerivWithinAt theorem8_5_3.1
      (xRight φ x.1.1.1, xB φ x.1.2.1.1) (xRight φ xs.1.1.1, xB φ xs.1.2.1.1)
    rw [theorem8_5_3.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => segArea p.1 p.2) hP5 h
  have d6 : HasDerivWithinAt
      (fun c => convexCurveArea ((wideDomain φ).comb c x xs).1.2.1.1 (π + φ) (3 * π / 2))
      ((∫ t in Ioo (π + φ) (3 * π / 2),
          (supp xs.1.2.1.1 t - supp x.1.2.1.1 t) ∂(sigma x.1.2.1.1)) +
        (segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) -
          segArea (xB φ x.1.2.1.1) (xB φ xs.1.2.1.1))) (Icc 0 1) 0 := by
    have hT := theorem8_5_2 (a := π + φ) (b := 3 * π / 2) (by linarith) (by linarith)
    have h := opt_quadratic_hasDerivWithinAt hT.1 x.1.2.1 xs.1.2.1
    rw [hT.2] at h
    exact opt_hasDerivWithinAt_comp (x := x) (xs := xs)
      (f := fun K : ConvexBodySet => convexCurveArea K.1 (π + φ) (3 * π / 2))
      (wide_projB_linear φ) h
  have hd : HasDerivWithinAt
      (fun c => wideUpperQ φ ((wideDomain φ).comb c x xs)) _ (Icc 0 1) 0 :=
    ((((d1.add d2).add d3).sub d4).add d5).add d6
  rw [opt_dirDeriv_eq hd]
  have z1 : segArea (vplus x.1.2.2.1 (3 * π / 2)) (vplus xs.1.2.2.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two (inWideL_supp x.2).2.1)
      (opt_snd_vplus_three_pi_div_two (inWideL_supp xs.2).2.1)
  have z2 : segArea (vminus x.1.2.1.1 (3 * π / 2)) (vminus xs.1.2.1.1 (3 * π / 2)) = 0 :=
    segArea_of_snd_eq_zero (opt_snd_vminus_three_pi_div_two (inWideL_supp x.2).1)
      (opt_snd_vminus_three_pi_div_two (inWideL_supp xs.2).1)
  have c3 : cross (yD φ xs.1.2.2.1 + xLeft φ xs.1.1.1)
      (xLeft φ x.1.1.1 - yD φ x.1.2.2.1) = 0 := by
    rw [hY, sub_self]; simp [cross]
  have c3' : cross (yD φ x.1.2.2.1) (xLeft φ x.1.1.1) = 0 := by
    rw [hY, cross_self]
  have c5 : cross (xRight φ xs.1.1.1 + xB φ xs.1.2.1.1)
      (xB φ x.1.2.1.1 - xRight φ x.1.1.1) = 0 := by
    rw [hX, sub_self]; simp [cross]
  have c5' : cross (xRight φ x.1.1.1) (xB φ x.1.2.1.1) = 0 := by
    rw [hX, cross_self]
  have b1 := opt_breve_integral x.1.2.1.1 xs.1.2.1.1 (a := φ) (b := π / 2)
    (a' := π + φ) (b' := 3 * π / 2) (by ring) (by ring)
  have b2 := opt_breve_integral x.1.2.2.1 xs.1.2.2.1
    (a := π / 2) (b := π / 2 + (π / 2 - φ)) (a' := 3 * π / 2)
    (b' := 3 * π / 2 + (π / 2 - φ)) (by ring) (by ring)
  rw [b1, b2, z1, z2, c3, c3', c5, c5']
  ring

end MovingSofaStability

end WideFirstVariation

/-!
## Gerver's certificate on the enlarged nonsmooth domain

Only the fixed reference sofa supplies regularity. The competing triple has
arbitrary convex bodies and a normalized cap, with no injectivity or
curvature-density assumption. Gerver's existing measure identity cancels the
core contribution in the first variation.

This proves the algebraic maximum and exact quadratic deficit. Applying it to
a sofa still requires the geometric canonical-triple and local upper-bound
lemmas: they are not assumed to follow from this algebraic certificate.
-/

section WideGerverCertificate

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

def wideGerverTriple {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : WideTriple P.φ :=
  toWideTriple (gerverTriple hP hbox)

/-- First-variation sign towards every enlarged-domain competitor. -/
theorem gerver_wide_firstVariation_nonpos {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (xs : WideTriple P.φ) :
    (wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) xs ≤ 0 := by
  obtain ⟨h1, -, -, -, h4, -, -, -⟩ := theorem8_4_3_two hP hbox
  rw [wide_reference_firstVariation (gm_φ_mem_Ioo hP hbox)
    (wideGerverTriple hP hbox) xs (gerverTriple hP hbox).2.1 h4.symm h1.symm]
  have hL : InWideL P.φ xs.1.1.1 xs.1.2.1.1 xs.1.2.2.1 := xs.2
  have hKs : IsConvexBody xs.1.1.1 := xs.1.1.2
  have hBs : IsConvexBody xs.1.2.1.1 := xs.1.2.1.2
  have hDs : IsConvexBody xs.1.2.2.1 := xs.1.2.2.2
  have hK := gm_isConvexBody_cap hP hbox
  have hB := gm_isConvexBody_B hP hbox
  have hD := gm_isConvexBody_D hP hbox
  have h01 := gm_φ_pos hP
  have h12 := gm_φ_lt_θ hP
  have h23 := gm_θ_lt_c hP
  have h34 := gm_c_lt_d hP
  have h45 := gm_d_lt hP
  have hpi := pi_pos
  set f : ℝ → ℝ := fun t => supp xs.1.1.1 t - supp P.cap t with hf
  set gB : ℝ → ℝ := fun t => suppBreve xs.1.2.1.1 t -
    suppBreve (rightBody P.φ P.cap) t with hgB
  set gD : ℝ → ℝ := fun t => suppBreve xs.1.2.2.1 t -
    suppBreve (leftBody P.φ P.cap) t with hgD
  have hfc : Continuous f :=
    (continuous_supp hKs.2.1).sub (continuous_supp hK.2.1)
  have hgBc : Continuous gB :=
    ((continuous_supp hBs.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hB.2.1).comp (continuous_id.add continuous_const))
  have hgDc : Continuous gD :=
    ((continuous_supp hDs.2.1).comp (continuous_id.add continuous_const)).sub
      ((continuous_supp hD.2.1).comp (continuous_id.add continuous_const))
  set Sι := Icc P.φ (π / 2 - P.φ) ∪ Icc (P.φ + π / 2) (π - P.φ) with hSι
  set ι := (iota P.cap).restrict Sι
  set β := (sigmaBreve (rightBody P.φ P.cap)).restrict (Ico (π / 2 - P.θ) (π / 2))
  set δ := (sigmaBreve (leftBody P.φ P.cap)).restrict (Ioc (π / 2) (π / 2 + P.θ))
  set τ := (sigma P.cap).restrict {π / 2}
  have hdec : (sigma P.cap).restrict (Icc 0 π) = ι + β + δ + τ := gm_sigma_decomp hP hbox
  have iσ : ∀ g : ℝ → ℝ, Continuous g → Integrable g ((sigma P.cap).restrict (Icc 0 π)) :=
    fun g hg => hg.continuousOn.integrableOn_compact isCompact_Icc
  have leι : ι ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))
  have leβ : β ≤ ι + β + δ + τ :=
    Measure.le_add_right (Measure.le_add_right (Measure.le_add_left le_rfl))
  have leδ : δ ≤ ι + β + δ + τ := Measure.le_add_right (Measure.le_add_left le_rfl)
  have leτ : τ ≤ ι + β + δ + τ := Measure.le_add_left le_rfl
  have iι : Integrable f ι := (iσ f hfc).mono_measure (by rw [hdec]; exact leι)
  have iβ : ∀ g : ℝ → ℝ, Continuous g → Integrable g β :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leβ)
  have iδ : ∀ g : ℝ → ℝ, Continuous g → Integrable g δ :=
    fun g hg => (iσ g hg).mono_measure (by rw [hdec]; exact leδ)
  have iτ : Integrable f τ := (iσ f hfc).mono_measure (by rw [hdec]; exact leτ)
  have eI1 : (∫ t in Icc 0 π, f t ∂(sigma P.cap)) =
      (∫ t, f t ∂ι) + (∫ t, f t ∂β) + (∫ t, f t ∂δ) := by
    rw [hdec, integral_add_measure ((iι.add_measure (iβ f hfc)).add_measure (iδ f hfc)) iτ,
      integral_add_measure (iι.add_measure (iβ f hfc)) (iδ f hfc),
      integral_add_measure iι (iβ f hfc)]
    have he : ∫ t, f t ∂τ = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      rw [mem_singleton_iff] at ht
      simp only [hf, ht, hL.1.2.2.2.1, gm_supp_cap_pi_div_two hP hbox, sub_self]
    rw [he, add_zero]
  have eI2 : (∫ t in Sι, f t * iFun P.cap t) = ∫ t, f t ∂ι := by
    have hS : Sι ⊆ Icc 0 π := by
      rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm : Measurable (fun t => ENNReal.ofReal (iFun P.cap t)) := by
      unfold iFun
      exact (Measurable.ite measurableSet_Iic
        (gm_measurable_dot (measurable_deriv _) (by unfold vvec; fun_prop))
        (gm_measurable_dot ((measurable_deriv _).comp (measurable_id.sub_const _))
          (by unfold uvec; fun_prop)).neg).ennreal_ofReal
    rw [show ι = (volume.restrict Sι).withDensity (fun t => ENNReal.ofReal (iFun P.cap t)) from
        gm_iota_restrict (measurableSet_Icc.union measurableSet_Icc) hS,
      integral_withDensity_eq_integral_toReal_smul hm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply setIntegral_congr_fun (measurableSet_Icc.union measurableSet_Icc)
    intro t ht
    have hpos : 0 ≤ iFun P.cap t := by
      rcases ht with ht | ht
      · have hlo : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_left hlo.2.le]
        exact ((theorem6_1_2 hP hbox).2.2 t hlo).2.le
      · have hτ : t - π / 2 ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [iFun, ite_eq_right (not_le.2 (by linarith [ht.1]))]
        linarith [((theorem6_1_2 hP hbox).2.2 _ hτ).1]
    simp only [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  have eI3 : (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) =
      ∫ t, gB t ∂β := by
    rw [gm_sigmaBreve_B_restrict hP hbox]
  have eI4 : (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
      ∂(sigmaBreve (leftBody P.φ P.cap))) = ∫ t, gD t ∂δ := by
    rw [gm_sigmaBreve_D_restrict hP hbox]
  change (∫ t in Icc 0 π, f t ∂(sigma P.cap)) - (∫ t in Sι, f t * iFun P.cap t) +
      (∫ t in Ioo P.φ (π / 2), gB t ∂(sigmaBreve (rightBody P.φ P.cap))) +
      (∫ t in Ioo (π / 2) (π / 2 + (π / 2 - P.φ)), gD t
        ∂(sigmaBreve (leftBody P.φ P.cap))) ≤ 0
  rw [eI1, eI2, eI3, eI4]
  have kB : (∫ t, f t ∂β) + (∫ t, gB t ∂β) ≤ 0 := by
    rw [← integral_add (iβ f hfc) (iβ gB hgBc)]
    apply setIntegral_nonpos measurableSet_Ico
    intro t ht
    have h1 := hL.2.2.2.2.2.1 t ⟨by linarith [ht.1], ht.2.le⟩
    have h2 := (theorem8_4_3_three hP hbox).2 t ⟨ht.1, ht.2.le⟩
    simp only [hf, hgB, suppBreve]
    rw [add_comm t π]
    linarith
  have kD : (∫ t, f t ∂δ) + (∫ t, gD t ∂δ) ≤ 0 := by
    rw [← integral_add (iδ f hfc) (iδ gD hgDc)]
    apply setIntegral_nonpos measurableSet_Ioc
    intro t ht
    have h1 := hL.2.2.2.2.2.2.2.2.1 (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := (theorem8_4_3_three hP hbox).1 (t - π / 2)
      ⟨show (0 : ℝ) ≤ t - π / 2 by linarith [ht.1],
        show t - π / 2 ≤ P.θ by linarith [ht.2]⟩
    rw [show π / 2 + (t - π / 2) = t by ring,
      show 3 * π / 2 + (t - π / 2) = t + π by ring] at h1 h2
    simp only [hf, hgD, suppBreve]
    linarith
  linarith

/-- Gerver maximizes the ORIGINAL Q on all nonsmooth feasible triples. -/
theorem wideUpperQ_le_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ wideUpperQ P.φ (wideGerverTriple hP hbox) :=
  (wide_maximum_iff_firstVariation (gm_φ_mem_Ioo hP hbox) (wideGerverTriple hP hbox)).2
    (gerver_wide_firstVariation_nonpos hP hbox) x

@[simp] theorem wideGerver_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    wideUpperQ P.φ (wideGerverTriple hP hbox) = area (gerverSofa P) :=
  gerver_upperQL_eq_area hP hbox

/-- Dual slack on the enlarged domain. Its sign is established, not assumed. -/
def wideDualSlack {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : ℝ :=
  -(wideDomain P.φ).dirDeriv (wideUpperQ P.φ) (wideGerverTriple hP hbox) x

theorem wideDualSlack_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) : 0 ≤ wideDualSlack hP hbox x :=
  neg_nonneg.mpr (gerver_wide_firstVariation_nonpos hP hbox x)

/-- The exact deficit is dual slack plus quadratic energy, without a Taylor error. -/
theorem wide_deficit_identity {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    area (gerverSofa P) - wideUpperQ P.φ x = wideDualSlack hP hbox x +
      segmentEnergy (wideDomain P.φ) (wideUpperQ P.φ) (wideGerverTriple hP hbox) x := by
  have h := deficit_eq_neg_dirDeriv_add_energy (wideDomain P.φ)
    (wideUpperQ_quadratic (gm_φ_mem_Ioo hP hbox)) (wideGerverTriple hP hbox) x
  simpa only [wideGerver_value, wideDualSlack] using h


end MovingSofaStability

end WideGerverCertificate

/-!
## Integral estimates for the residual-to-support step

Integrability assumptions are explicit: totalized Bochner integrals must not be
used to conceal a nonintegrable residual. The Cauchy--Schwarz proof below uses
nonnegativity of a square integral and also handles a zero square norm. No new
integration axioms are introduced.
-/

section IntegralEstimates

open Real MeasureTheory Filter
open MovingSofaUniqueness

namespace MovingSofaStability

section Integral

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

/-- Cauchy--Schwarz in a form convenient for the real tangent residuals. -/
theorem integral_mul_sq_le
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let A : ℝ := ∫ x, f x ^ 2 ∂μ
  let B : ℝ := ∫ x, g x ^ 2 ∂μ
  let C : ℝ := ∫ x, f x * g x ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => sq_nonneg (f x)
  change C ^ 2 ≤ A * B
  by_cases hA0 : A = 0
  · have hfzero : ∀ᵐ x ∂μ, f x = 0 := by
      have hz : ∀ᵐ x ∂μ, f x ^ 2 = 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hf).1 hA0
      filter_upwards [hz] with x hx
      have hmul : f x * f x = 0 := by simpa only [pow_two] using hx
      exact (mul_eq_zero.mp hmul).elim id id
    have hC0 : C = 0 := by
      change (∫ x, f x * g x ∂μ) = 0
      calc
        _ = ∫ _ : X, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hfzero] with x hx
          simp only [hx, zero_mul]
        _ = 0 := integral_zero X ℝ
    rw [hA0, hC0]
    norm_num
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hleft : Integrable (fun x => C ^ 2 * f x ^ 2 + A ^ 2 * g x ^ 2) μ :=
      (hf.const_mul _).add (hg.const_mul _)
    have hright : Integrable (fun x => (2 * C * A) * (f x * g x)) μ :=
      hfg.const_mul _
    have hi : (∫ x, (C * f x - A * g x) ^ 2 ∂μ) =
        C ^ 2 * A + A ^ 2 * B - (2 * C * A) * C := by
      calc
        _ = ∫ x, (C ^ 2 * f x ^ 2 + A ^ 2 * g x ^ 2) -
            (2 * C * A) * (f x * g x) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
        _ = _ := by
          rw [integral_sub hleft hright,
            integral_add (hf.const_mul _) (hg.const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
    have hn : 0 ≤ C ^ 2 * A + A ^ 2 * B - (2 * C * A) * C := by
      rw [← hi]
      exact integral_nonneg fun x => sq_nonneg _
    have hp : A * C ^ 2 ≤ A * (A * B) := by nlinarith
    exact (mul_le_mul_iff_right₀ hApos).mp hp


end Integral

/-- The elementary four-term Cauchy--Schwarz identity used when keeping the
four residual intervals separate. -/
theorem four_term_sq_le (a b c d x y z w : ℝ) :
    (a * x + b * y + c * z + d * w) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  have he :
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) -
        (a * x + b * y + c * z + d * w) ^ 2 =
      (a * y - b * x) ^ 2 + (a * z - c * x) ^ 2 + (a * w - d * x) ^ 2 +
      (b * z - c * y) ^ 2 + (b * w - d * y) ^ 2 + (c * w - d * z) ^ 2 := by ring
  apply sub_nonneg.mp
  rw [he]
  positivity

/-- The final scalar passage from a squared norm estimate to square-root stability. -/
theorem abs_le_mul_sqrt_of_sq_le {d C E : ℝ} (hC : 0 ≤ C)
    (h : d ^ 2 ≤ C ^ 2 * E) : |d| ≤ C * sqrt E := by
  have hroot := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hC] at hroot
  exact hroot

end MovingSofaStability

end IntegralEstimates

/-!
## The four cap residuals and their integrating factor

The derivative argument is kept explicit rather than silently using a derivative
of a nonsmooth support function everywhere. The algebraic support-displacement
identities hold without smoothness.

The absolutely continuous reconstruction and the square integrals of the four
Green kernels are proved in later modules (`ODEReconstruction.lean`,
`TrigKernelIntegrals.lean`, `SharpKernelNorms.lean`).
-/

section Residuals

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Residual for the tangent-line term, with an explicit derivative value. -/
def tangentResidual (T : ℝ) (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f T - f t * cos (T - t)) / sin (T - t) - df t

/-- Residual for the outer-corner term. -/
def cornerResidual (f df : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (t + π / 2) - df t

/-- Pin the left support: the translation coefficient is `-f π`. -/
def pinnedDifference (f : ℝ → ℝ) (t : ℝ) : ℝ := f t + f π * cos t

def pinnedDerivative (f df : ℝ → ℝ) (t : ℝ) : ℝ := df t - f π * sin t

@[simp] theorem pinnedDifference_pi (f : ℝ → ℝ) : pinnedDifference f π = 0 := by
  simp [pinnedDifference]

@[simp] theorem pinnedDifference_top (f : ℝ → ℝ) :
    pinnedDifference f (π / 2) = f (π / 2) := by
  simp [pinnedDifference]

theorem tangentResidual_add (T : ℝ) (f df g dg : ℝ → ℝ) (t : ℝ) :
    tangentResidual T (fun u => f u + g u) (fun u => df u + dg u) t =
      tangentResidual T f df t + tangentResidual T g dg t := by
  unfold tangentResidual
  ring

/-- Horizontal translations lie in the kernel of every tangent residual. -/
theorem tangentResidual_translation (a T t : ℝ) (hs : sin (T - t) ≠ 0) :
    tangentResidual T (fun u => a * cos u) (fun u => -a * sin u) t = 0 := by
  have hc : cos T = cos t * cos (T - t) - sin t * sin (T - t) := by
    rw [← cos_add]
    congr 1
    ring
  unfold tangentResidual
  beta_reduce
  rw [hc]
  field_simp
  ring

/-- Pinning removes translation without changing a tangent residual. -/
theorem tangentResidual_pinned (T : ℝ) (f df : ℝ → ℝ) (t : ℝ)
    (hs : sin (T - t) ≠ 0) :
    tangentResidual T (pinnedDifference f) (pinnedDerivative f df) t =
      tangentResidual T f df t := by
  have h := tangentResidual_translation (f π) T t hs
  have he := tangentResidual_add T f df (fun u => f π * cos u)
    (fun u => -f π * sin u) t
  change tangentResidual T (fun u => f u + f π * cos u)
    (fun u => df u - f π * sin u) t = tangentResidual T f df t
  simp only [sub_eq_add_neg, neg_mul] at *
  rw [he, h, add_zero]

@[simp] theorem cornerResidual_pinned (f df : ℝ → ℝ) (t : ℝ) :
    cornerResidual (pinnedDifference f) (pinnedDerivative f df) t =
      cornerResidual f df t := by
  simp only [cornerResidual, pinnedDifference, pinnedDerivative, cos_add_pi_div_two]
  ring

/-- The algebraic residual is the difference of the actual tangent displacements.
No derivative-existence assumption is used here. -/
theorem tangent_displacement_sub {K₀ K₁ : Set (ℝ × ℝ)} {T t : ℝ} (ht : t < T) :
    displacement K₁ (tangentParam K₁ T) t - displacement K₀ (tangentParam K₀ T) t =
      tangentResidual T (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [tangent_displacement_formula K₁ ht, tangent_displacement_formula K₀ ht]
  unfold tangentResidual
  ring

theorem outer_displacement_sub (K₀ K₁ : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K₁ (outerCorner K₁) t - displacement K₀ (outerCorner K₀) t =
      cornerResidual (fun u => supp K₁ u - supp K₀ u)
        (fun u => dot (vplus K₁ u) (vvec u) - dot (vplus K₀ u) (vvec u)) t := by
  rw [outer_displacement_formula, outer_displacement_formula]
  unfold cornerResidual
  ring

/-- Explicit integrating factor. The target support `f T` is held constant. -/
def tangentQuotient (T : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - f T * cos (T - t)) / sin (T - t)

/-- The fourth interval's residual, after pinning the left support. -/
theorem tangentResidual_left {f df : ℝ → ℝ} (h : f π = 0) (t : ℝ) :
    tangentResidual π f df t = cos t / sin t * f t - df t := by
  simp only [tangentResidual, h, zero_sub, cos_pi_sub, sin_pi_sub]
  ring

end MovingSofaStability

end Residuals

/-!
## Six squared displacement differences in the enlarged deficit

This identifies the abstract quadratic energy with actual integrals, not merely
with a midpoint expression. The four cap integrals are bounded by the objective
deficit for EVERY nonsmooth feasible triple.
-/

section WideResidualEnergy

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Sum of the four cap displacement energies, for arbitrary convex bodies. -/
def capResidualEnergy (φ : ℝ) (K₀ K₁ : ConvexBodySet) : ℝ :=
  displacementEnergy 0 φ (fun K => tangentParam K.1 (π / 2)) K₀ K₁ +
  displacementEnergy φ (π / 2 - φ) (fun K => outerCorner K.1) K₀ K₁ +
  displacementEnergy (π / 2 - φ) (π / 2)
    (fun K => tangentParam K.1 (π / 2 + (π / 2 - φ))) K₀ K₁ +
  displacementEnergy (π / 2) π (fun K => tangentParam K.1 π) K₀ K₁

def rightResidualEnergy (φ : ℝ) (B₀ B₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (π + φ) (3 * π / 2) (fun B => tangentParam B.1 (3 * π / 2)) B₀ B₁

def leftResidualEnergy (φ : ℝ) (D₀ D₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
    (fun D => tangentParam D.1 (3 * π / 2 + (π / 2 - φ))) D₀ D₁

theorem rightResidualEnergy_nonneg (φ : ℝ) (B₀ B₁ : ConvexBodySet) :
    0 ≤ rightResidualEnergy φ B₀ B₁ := displacementEnergy_nonneg _ _ _ _ _

theorem leftResidualEnergy_nonneg (φ : ℝ) (D₀ D₁ : ConvexBodySet) :
    0 ≤ leftResidualEnergy φ D₀ D₁ := displacementEnergy_nonneg _ _ _ _ _

/-- Specialize the quantitative Mamikon identity to a fixed tangent line. -/
theorem tangent_energy_gap {a b T c : ℝ} (hab : a < b) (hb : b < a + π)
    (ha : T - π < a) (hbt : b ≤ T) (K₀ K₁ : ConvexBodySet)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (tangentParam K₀.1 T) +
      c * mamikon K₁.1 a b (tangentParam K₁.1 T) -
      mamikon (convexBodyComb c K₀ K₁).1 a b
        (tangentParam (convexBodyComb c K₀ K₁).1 T) =
      c * (1 - c) * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  apply mamikon_combo_energy hab hb (fun K => tangentParam K.1 T)
  · intro K
    exact (theorem8_3_1 K.2 ha hab.le hbt).1
  · intro K t ht
    by_cases h : t < T
    · simp only [tangentParam, h, ↓reduceIte]
      exact vint_mem_line_left K.1 t T
    · have he : t = T := le_antisymm (ht.2.trans hbt) (not_lt.mp h)
      subst t
      simp only [tangentParam, lt_irrefl, ↓reduceIte]
      exact dot_vminus_uvec K.1 T
  · intro K L s hs t ht
    exact theorem8_3_2 hab.le hbt K L hs t ht
  · exact hc

/-- Specialize the identity to the outer-corner family. -/
theorem outer_energy_gap {a b c : ℝ} (hab : a < b) (hb : b < a + π)
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (outerCorner K₀.1) +
      c * mamikon K₁.1 a b (outerCorner K₁.1) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (outerCorner (convexBodyComb c K₀ K₁).1) =
      c * (1 - c) * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ := by
  apply mamikon_combo_energy hab hb (fun K => outerCorner K.1)
  · intro K
    exact opt_outerCorner_cbv K.2 a b
  · intro K t ht
    exact inj_dot_outerCorner_uvec K.1 t
  · intro K L s hs t ht
    rw [cvx_convexBodyComb_val hs, opt_outerCorner_comb K.2 L.2 hs]
    rfl
  · exact hc

/-- The grouped cap gap is the sum of all four displacement energies. -/
theorem capResidualEnergy_gap {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikonS φ K₀.1 + c * mamikonS φ K₁.1 -
      mamikonS φ (convexBodyComb c K₀ K₁).1 = c * (1 - c) * capResidualEnergy φ K₀ K₁ := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have h1 := tangent_energy_gap (T := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h2 := outer_energy_gap (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith) K₀ K₁ hc
  have h3 := tangent_energy_gap (T := π / 2 + (π / 2 - φ))
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h4 := tangent_energy_gap (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁ hc
  unfold mamikonS capResidualEnergy
  linarith

/-- All six integral energies, retaining the two auxiliary-body terms. -/
def wideResidualEnergy {φ : ℝ} (x y : WideTriple φ) : ℝ :=
  capResidualEnergy φ x.1.1 y.1.1 + rightResidualEnergy φ x.1.2.1 y.1.2.1 +
    leftResidualEnergy φ x.1.2.2 y.1.2.2

theorem wideEnergy_eq_integrals {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : WideTriple φ) :
    segmentEnergy (wideDomain φ) (wideUpperQ φ) x y = wideResidualEnergy x y := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := capResidualEnergy_gap hφ x.1.1 y.1.1 hc
  have hR := tangent_energy_gap (T := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.1 y.1.2.1 hc
  have hL := tangent_energy_gap (T := 3 * π / 2 + (π / 2 - φ))
    (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ))
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.2 y.1.2.2 hc
  change (1 - 1 / 2) * mamikonR φ x.1.2.1.1 + (1 / 2) * mamikonR φ y.1.2.1.1 -
    mamikonR φ (convexBodyComb (1 / 2) x.1.2.1 y.1.2.1).1 =
    (1 / 2) * (1 - 1 / 2) * rightResidualEnergy φ x.1.2.1 y.1.2.1 at hR
  change (1 - 1 / 2) * mamikonL φ x.1.2.2.1 + (1 / 2) * mamikonL φ y.1.2.2.1 -
    mamikonL φ (convexBodyComb (1 / 2) x.1.2.2 y.1.2.2).1 =
    (1 / 2) * (1 - 1 / 2) * leftResidualEnergy φ x.1.2.2 y.1.2.2 at hL
  have hlin := cap_mamikon_upperP_affine hφ x.2.1 y.2.1 hc
  have hm := inWideL_comb x.2 y.2 hc
  simp only [cvx_convexBodyComb_val hc] at hS hR hL
  unfold segmentEnergy wideResidualEnergy
  simp only [wideUpperQ, wideDomain, WideTriple.comb, hc, ↓reduceDIte,
    cvx_convexBodyComb_val hc]
  rw [wide_upperQ_decomposition hφ hm,
    wide_upperQ_decomposition hφ x.2, wide_upperQ_decomposition hφ y.2]
  linarith

/-- The exact deficit identity in integral, rather than abstract midpoint, form. -/
theorem wide_deficit_eq_slack_add_integrals {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    area (gerverSofa P) - wideUpperQ P.φ x =
      wideDualSlack hP hbox x + wideResidualEnergy (wideGerverTriple hP hbox) x := by
  rw [wide_deficit_identity hP hbox x,
    wideEnergy_eq_integrals (GerverParams.gm_φ_mem_Ioo hP hbox)]

/-- Cap-only integral energy is bounded by the nonsmooth Q deficit. -/
theorem wide_capResidualEnergy_le_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 ≤
      area (gerverSofa P) - wideUpperQ P.φ x := by
  rw [wide_deficit_eq_slack_add_integrals hP hbox x]
  have hs := wideDualSlack_nonneg hP hbox x
  have hr := rightResidualEnergy_nonneg P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1
  have hl := leftResidualEnergy_nonneg P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2
  unfold wideResidualEnergy
  linarith

end MovingSofaStability

end WideResidualEnergy
