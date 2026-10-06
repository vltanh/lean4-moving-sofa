module

public import MovingSofaStability.MixedArea

/-!
# Core first variation with a nonsmooth competing cap

Only the reference cap is in Ki. The competitor is an arbitrary convex body. The
core's vector measure belongs to the smooth reference; no derivative of the
competing corner path is assumed.
-/

@[expose] public section
noncomputable section

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
