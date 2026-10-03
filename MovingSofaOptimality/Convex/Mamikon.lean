module

public import MovingSofaOptimality.Convex.ConvexCurve
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Mamikon's theorem (§7.4)

Definitions 7.4.1 (`def:mamikon-region`), 7.4.2 (`def:mamikon`), Theorems 7.4.1 (`thm:mamikon`) and
7.4.2 (`thm:mamikon-convex`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

section aux

open Filter Topology Function

section density

open scoped NNReal ENNReal

variable {X E F G : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in
/-- A density bounded by `M` gives a vector measure of total variation at most `‖B‖ M |μ|`. -/
lemma cvx_variation_withDensity_le {μ : VectorMeasure X F} {g : X → E} {M : ℝ≥0}
    (hgM : ∀ᵐ x ∂μ.variation, ‖g x‖ ≤ M) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.withDensity g B).variation ≤ ((‖B‖₊ * M : ℝ≥0) : ℝ≥0∞) • μ.variation := by
  refine (VectorMeasure.variation_WithDensity_le).trans ?_
  rw [Measure.le_iff]
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  have hac := VectorMeasure.absolutelyContinuous_variation_transpose μ B
  have h2 := VectorMeasure.variation_transpose_le μ B s
  rw [Measure.coe_nnreal_smul_apply] at h2
  refine (lintegral_mono_ae (g := fun _ => (M : ℝ≥0∞)) ?_).trans ?_
  · filter_upwards [ae_restrict_of_ae (hac.ae_le hgM)] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hx
  · rw [setLIntegral_const, ENNReal.coe_mul, mul_comm (‖B‖₊ : ℝ≥0∞), mul_assoc]
    gcongr

omit [CompleteSpace F] in
/-- Integrating `φ • g` against `μ` (with pairing `B`) is integrating `φ` against the vector
measure with density `g`. -/
theorem cvx_integral_smul_eq_integral_withDensity {μ : VectorMeasure X F}
    [IsFiniteMeasure μ.variation] {g : X → E} {M : ℝ≥0}
    (hgm : AEStronglyMeasurable g μ.variation) (hgM : ∀ᵐ x ∂μ.variation, ‖g x‖ ≤ M)
    (B : E →L[ℝ] F →L[ℝ] G) {φ : X → ℝ} (hφ : Integrable φ μ.variation) :
    ∫ᵛ x, φ x • g x ∂[B; μ] = ∫ᵛ x, φ x ∂• (μ.withDensity g B) := by
  have hgi : μ.Integrable g := Integrable.of_bound hgm M hgM
  set ν := μ.withDensity g B with hν
  have hvar := cvx_variation_withDensity_le hgM B
  have hint : ∀ {φ : X → ℝ}, Integrable φ μ.variation → ν.Integrable φ := fun hφ =>
    (hφ.smul_measure ENNReal.coe_ne_top).mono_measure hvar
  have hbd : ∀ (φ₁ φ₂ : X → ℝ), ∀ᵐ x ∂μ.variation,
      ‖φ₁ x • g x - φ₂ x • g x‖ ≤ M * ‖φ₁ x - φ₂ x‖ := by
    intro φ₁ φ₂
    filter_upwards [hgM] with x hx
    rw [← sub_smul, norm_smul, mul_comm]
    gcongr
  have hint2 : ∀ {φ : X → ℝ}, Integrable φ μ.variation →
      μ.Integrable (fun x => φ x • g x) := by
    intro φ hφ
    refine Integrable.mono' (hφ.norm.const_mul M) (hφ.aestronglyMeasurable.smul hgm) ?_
    filter_upwards [hbd φ 0] with x hx
    simpa using hx
  have hfinν : IsFiniteMeasure ν.variation := by
    refine ⟨(hvar univ).trans_lt ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  -- induction on `φ ∈ L¹(|μ|)`
  refine hφ.induction (P := fun φ => ∫ᵛ x, φ x • g x ∂[B; μ] = ∫ᵛ x, φ x ∂• ν) ?_ ?_ ?_ ?_
  · -- indicator functions
    intro c s hs _
    have e : (fun x => s.indicator (fun _ => c) x • g x) = s.indicator (fun x => c • g x) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [e, VectorMeasure.integral_indicator hs, VectorMeasure.integral_fun_smul,
      VectorMeasure.integral_indicator_const _ hs, hν, VectorMeasure.withDensity_apply hgi]
    simp
  · -- sums
    intro φ₁ φ₂ _ hφ₁ hφ₂ h₁ h₂
    simp only [Pi.add_apply, add_smul]
    rw [VectorMeasure.integral_fun_add (hint2 hφ₁) (hint2 hφ₂),
      VectorMeasure.integral_fun_add (hint hφ₁) (hint hφ₂), h₁, h₂]
  · -- closedness: both sides are `‖B‖ M`-Lipschitz in `φ ∈ L¹(|μ|)`
    refine cvx_isClosed_eq_of_lipschitz (K := ‖B‖₊ * M)
      (Φ := fun φ => ∫ᵛ x, φ x • g x ∂[B; μ]) (Ψ := fun φ => ∫ᵛ x, φ x ∂• ν) ?_ ?_
    · intro φ₁ φ₂
      refine (VectorMeasure.dist_integral_le_lintegral_edist (hint2 (L1.integrable_coeFn φ₁))
        (hint2 (L1.integrable_coeFn φ₂))).trans ?_
      rw [L1.dist_def, NNReal.coe_mul, coe_nnnorm, mul_assoc]
      gcongr
      have hfin : ∫⁻ a, edist (φ₁ a) (φ₂ a) ∂μ.variation ≠ ∞ := by
        rw [← L1.edist_def]; exact edist_ne_top _ _
      calc (∫⁻ a, edist (φ₁ a • g a) (φ₂ a • g a) ∂μ.variation).toReal
          ≤ (∫⁻ a, M * edist (φ₁ a) (φ₂ a) ∂μ.variation).toReal := by
            refine ENNReal.toReal_mono ?_ (lintegral_mono_ae ?_)
            · rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
              exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
            · filter_upwards [hbd φ₁ φ₂] with x hx
              rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← ENNReal.ofReal_coe_nnreal,
                ← ENNReal.ofReal_mul (by positivity)]
              exact ENNReal.ofReal_le_ofReal hx
        _ = M * (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂μ.variation).toReal := by
            rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.toReal_mul,
              ENNReal.coe_toReal]
    · intro φ₁ φ₂
      refine (VectorMeasure.dist_integral_le_lintegral_edist (hint (L1.integrable_coeFn φ₁))
        (hint (L1.integrable_coeFn φ₂))).trans ?_
      rw [L1.dist_def]
      have hfin : ∫⁻ a, edist (φ₁ a) (φ₂ a) ∂μ.variation ≠ ∞ := by
        rw [← L1.edist_def]; exact edist_ne_top _ _
      have h1 : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] G →L[ℝ] G)‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_lsmul_le
      have h2 : (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂ν.variation).toReal ≤
          ((‖B‖₊ * M : ℝ≥0) : ℝ) * (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂μ.variation).toReal := by
        calc (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂ν.variation).toReal
            ≤ (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂(((‖B‖₊ * M : ℝ≥0) : ℝ≥0∞) • μ.variation)).toReal := by
              refine ENNReal.toReal_mono ?_ (lintegral_mono' hvar le_rfl)
              rw [lintegral_smul_measure]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
          _ = ((‖B‖₊ * M : ℝ≥0) : ℝ) * (∫⁻ a, edist (φ₁ a) (φ₂ a) ∂μ.variation).toReal := by
              rw [lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
      exact (mul_le_of_le_one_left ENNReal.toReal_nonneg h1).trans h2
  · -- a.e. equal functions
    intro φ₁ φ₂ hfg _ h₁
    have hac : ν.variation ≪ μ.variation := Measure.absolutelyContinuous_of_le_smul hvar
    rw [← VectorMeasure.integral_congr_ae (hac.ae_eq hfg), ← h₁]
    apply VectorMeasure.integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

end density

/-! ### Primitives -/

/-- `v_t = v_a - ∫_a^t u_s ds`. -/
lemma cvx_vvec_primitive (a t : ℝ) : vvec t = vvec a + ∫ s in a..t, -uvec s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_vvec s)
    ((continuous_uvec.neg).intervalIntegrable _ _)]
  abel

/-- `v_K⁺` is measurable. -/
lemma cvx_measurable_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Measurable (vplus K) :=
  (cvx_stronglyMeasurable_vplus hK).measurable

/-- The right derivative `v_K⁺(t) · v_t` of the support function. -/
lemma cvx_measurable_suppDeriv {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    Measurable fun s => dot (vplus K s) (vvec s) :=
  continuous_dot_pair.measurable.comp ((cvx_measurable_vplus hK).prodMk continuous_vvec.measurable)

/-- The right derivative `v_K⁺(t) · v_t` of `h_K` is bounded. -/
lemma cvx_suppDeriv_bound {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) :
    ∃ C : NNReal, ∀ s, ‖dot (vplus K s) (vvec s)‖ ≤ C := by
  obtain ⟨R, hR⟩ := cvx_exists_bound hK
  refine ⟨2 * R, fun s => ?_⟩
  rw [Real.norm_eq_abs]
  refine (abs_dot_le _ _).trans ?_
  have := hR _ (vplus_mem_edge hK s).1
  have h2 := norm_vvec_le s
  push_cast
  calc 2 * ‖vplus K s‖ * ‖vvec s‖ ≤ 2 * R * 1 := by gcongr
    _ = 2 * R := by ring

/-- `t ↦ v_K⁺(t) · v_t` is integrable on every set of finite measure. -/
lemma cvx_integrableOn_suppDeriv {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {s : Set ℝ}
    (hs : volume s ≠ ⊤) : IntegrableOn (fun t => dot (vplus K t) (vvec t)) s := by
  obtain ⟨C, hC⟩ := cvx_suppDeriv_bound hK
  exact Measure.integrableOn_of_bounded (M := C) hs
    (cvx_measurable_suppDeriv hK).aestronglyMeasurable (Eventually.of_forall hC)

/-- `h_K` is the primitive of its right derivative `v_K⁺(t) · v_t`. -/
lemma cvx_supp_primitive {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a t : ℝ} (hat : a ≤ t) :
    supp K t = supp K a + ∫ s in a..t, dot (vplus K s) (vvec s) := by
  have hint : IntervalIntegrable (fun s => dot (vplus K s) (vvec s)) volume a t :=
    (cvx_integrableOn_suppDeriv hK
      (by rw [Real.volume_interval]; exact ENNReal.ofReal_ne_top)).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hat
    (continuous_supp hK.2.1).continuousOn
    (fun s _ => (hasDerivWithinAt_supp_right hK s).mono Ioi_subset_Ici_self) hint]
  abel

/-- `v_t` is continuous and of bounded variation on `[a, b]`. -/
lemma cvx_bv_vvec {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn vvec (Icc a b) ∧ ContinuousOn vvec (Icc a b) :=
  cvx_bv_of_primitive (M := 1) hab (continuous_uvec.neg).integrableOn_Icc
    (fun t _ => by simpa using norm_uvec_le t) (fun t _ => cvx_vvec_primitive a t)

/-- `d v_t = -u_t dt`. -/
lemma cvx_lsMeasure_vvec {a b : ℝ} (hab : a ≤ b) :
    lsMeasure vvec a b = (volume.restrict (Icc a b)).withDensityᵥ (fun t => -uvec t) :=
  cvx_lsMeasure_eq_withDensityᵥ hab (continuous_uvec.neg).integrableOn_Icc
    (fun t _ => cvx_vvec_primitive a t) (cvx_bv_vvec hab).1 (cvx_bv_vvec hab).2

/-- `-h_K` has bounded variation on `[a, b]` and `d(-h_K) = -(v_K⁺(t) · v_t) dt`. -/
lemma cvx_lsMeasure_neg_supp {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (fun t => -supp K t) (Icc a b) ∧ lsMeasure (fun t => -supp K t) a b =
      (volume.restrict (Icc a b)).withDensityᵥ (fun t => -dot (vplus K t) (vvec t)) := by
  obtain ⟨C, hC⟩ := cvx_suppDeriv_bound hK
  have hψ : IntegrableOn (fun t => -dot (vplus K t) (vvec t)) (Icc a b) :=
    (cvx_integrableOn_suppDeriv hK (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).neg
  have hx : ∀ t ∈ Icc a b, -supp K t = -supp K a + ∫ s in a..t, -dot (vplus K s) (vvec s) := by
    intro t ht
    rw [cvx_supp_primitive hK ht.1, intervalIntegral.integral_neg]
    ring
  obtain ⟨hbv, hc⟩ := cvx_bv_of_primitive (x := fun t => -supp K t) (M := C) hab hψ
    (fun t _ => by rw [norm_neg]; exact hC t) hx
  exact ⟨hbv, cvx_lsMeasure_eq_withDensityᵥ hab hψ hx hbv hc⟩

/-- The cross product is antisymmetric. -/
lemma cvx_crossCLM_flip : crossCLM.flip = -crossCLM := by
  refine ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => ?_
  rw [ContinuousLinearMap.flip_apply, neg_apply, neg_apply, crossCLM_apply, crossCLM_apply,
    cross_anticomm]

/-- Integration by parts for `𝐳 × v_K⁺` on `(a, b)`. -/
lemma cvx_ibp_cross_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℝ × ℝ} (hzc : ContinuousOn z (Icc a b)) (hzbv : BoundedVariationOn z (Icc a b)) :
    cross (z b) (vminus K b) - cross (z a) (vplus K a) =
      ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM.flip; lsMeasure z a b] +
        ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure (vplus K) a b] := by
  -- integration by parts for the clamped functions, evaluated on `(a, b)`
  have hfz := boundedVariationOn_clampFun hab.le hzbv
  have hvbv := boundedVariationOn_clampFun hab.le (lemma5_2_1 hK a b)
  have hzcl := continuous_clampFun hab.le hzc
  have key := hfz.vectorMeasure_bilinear_comp_eq hvbv (B := crossCLM)
  have hI := congrArg (fun μ : VectorMeasure ℝ ℝ => μ (Ioo a b)) key
  rw [BoundedVariationOn.vectorMeasure_Ioo _ hab, add_apply,
    VectorMeasure.withDensity_apply hvbv.rightLim.integrable,
    VectorMeasure.withDensity_apply hfz.leftLim.integrable,
    BoundedVariationOn.leftLim_bilinear_comp hfz hvbv,
    BoundedVariationOn.rightLim_bilinear_comp hfz hvbv] at hI
  simp only [crossCLM_apply] at hI
  -- the one-sided limits of the clamped functions
  have h1 : Function.leftLim (clampFun z a b) b = z b := by
    rw [hzcl.continuousWithinAt.leftLim_eq, clampFun_of_mem ⟨hab.le, le_rfl⟩]
  have h2 : Function.rightLim (clampFun z a b) a = z a := by
    rw [hzcl.continuousWithinAt.rightLim_eq, clampFun_of_mem ⟨le_rfl, hab.le⟩]
  have h3 : Function.leftLim (clampFun (vplus K) a b) b = vminus K b := by
    apply leftLim_eq_of_tendsto
    apply (tendsto_vplus_left hK b).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (clampFun_of_mem ⟨ht.1.le, ht.2.le⟩).symm
  have h4 : Function.rightLim (clampFun (vplus K) a b) a = vplus K a := by
    apply rightLim_eq_of_tendsto
    apply (tendsto_vplus_right hK a).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (clampFun_of_mem ⟨ht.1.le, ht.2.le⟩).symm
  have h5 : EqOn (Function.rightLim (clampFun (vplus K) a b)) (vplus K) (Ioo a b) := by
    intro t ht
    apply rightLim_eq_of_tendsto
    apply (tendsto_vplus_right hK t).congr'
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact (clampFun_of_mem ⟨(ht.1.trans hs.1).le, hs.2.le⟩).symm
  have h6 : EqOn (Function.leftLim (clampFun z a b)) z (Ioo a b) := by
    intro t ht
    rw [hzcl.continuousWithinAt.leftLim_eq, clampFun_of_mem ⟨ht.1.le, ht.2.le⟩]
  rwa [h1, h2, h3, h4, VectorMeasure.setIntegral_congr_fun h5,
    VectorMeasure.setIntegral_congr_fun h6, ← lsMeasure_eq_vectorMeasure hfz,
    ← lsMeasure_eq_vectorMeasure hvbv] at hI

/-- `(-u_t) × p = -(p · v_t)`. -/
lemma cvx_cross_neg_uvec (p : ℝ × ℝ) (t : ℝ) : cross (-uvec t) p = -dot p (vvec t) := by
  simp only [cross, dot, uvec, vvec, Prod.fst_neg, Prod.snd_neg]; ring

/-- **The key identity** `v_t × d𝐳(t) = α(t) dt` on `(a, b)`, for `𝐳` on the supporting lines. -/
lemma cvx_integral_vvec_cross_dz {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℝ × ℝ} (hzc : Continuous z) (hzbv : BoundedVariationOn z (Icc a b))
    (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) {I : Set ℝ} (hI : MeasurableSet I)
    (hIab : I ⊆ Ioo a b) :
    ∫ᵛ t in I, vvec t ∂[crossCLM; lsMeasure z a b] =
      ∫ t in I, dot (z t - vplus K t) (vvec t) := by
  have hIcc : I ⊆ Icc a b := hIab.trans Ioo_subset_Icc_self
  obtain ⟨hFbv, hFc⟩ := cvx_bv_vvec hab.le
  -- Step 1: integration by parts for `v_t × 𝐳(t)`; since `𝐳(t) ∈ l_K(t)`, `v_t × 𝐳(t) = -h_K(t)`.
  have hF := boundedVariationOn_clampFun hab.le hFbv
  have hG := boundedVariationOn_clampFun hab.le hzbv
  have hFcl := continuous_clampFun hab.le hFc
  have hGcl := continuous_clampFun hab.le hzc.continuousOn
  have key := hF.vectorMeasure_bilinear_comp_eq hG (B := crossCLM)
  obtain ⟨hsbv, hsls⟩ := cvx_lsMeasure_neg_supp hK hab.le
  have hP : (hF.bilinear_comp hG crossCLM).vectorMeasure = lsMeasure (fun t => -supp K t) a b := by
    rw [lsMeasure_eq_vectorMeasure (boundedVariationOn_clampFun hab.le hsbv)]
    apply vectorMeasure_congr
    funext t
    simp only [clampFun, crossCLM_apply]
    rw [cross_anticomm, cross_vvec, hzl _ (clamp_mem hab.le t)]
  rw [hP, hsls] at key
  have h := congrArg (fun μ : VectorMeasure ℝ ℝ => μ I) key
  have hgi : Integrable (fun t => -dot (vplus K t) (vvec t)) (volume.restrict (Icc a b)) :=
    (cvx_integrableOn_suppDeriv hK (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).neg
  rw [withDensityᵥ_apply hgi hI, add_apply, VectorMeasure.withDensity_apply hG.rightLim.integrable,
    VectorMeasure.withDensity_apply hF.leftLim.integrable] at h
  have h5 : EqOn (Function.rightLim (clampFun z a b)) z I := by
    intro t ht
    rw [hGcl.continuousWithinAt.rightLim_eq, clampFun_of_mem (hIcc ht)]
  have h6 : EqOn (Function.leftLim (clampFun vvec a b)) vvec I := by
    intro t ht
    rw [hFcl.continuousWithinAt.leftLim_eq, clampFun_of_mem (hIcc ht)]
  rw [VectorMeasure.setIntegral_congr_fun h5, VectorMeasure.setIntegral_congr_fun h6,
    ← lsMeasure_eq_vectorMeasure hF, ← lsMeasure_eq_vectorMeasure hG,
    cvx_lsMeasure_vvec hab.le] at h
  -- Step 2: compute `∫ 𝐳 × d v_t` with `d v_t = -u_t dt`, and solve for `∫ v_t × d𝐳`.
  have hui : Integrable (fun t => -uvec t) (volume.restrict (Icc a b)) :=
    (continuous_uvec.neg).integrableOn_Icc
  have hL2 : ∫ᵛ t in I, z t ∂[crossCLM.flip;
      (volume.restrict (Icc a b)).withDensityᵥ (fun t => -uvec t)] =
      ∫ t in I, -dot (z t) (vvec t) := by
    rw [cvx_withDensityᵥ_restrict hui hI, cvx_integral_withDensityᵥ hui.restrict (M := 1)
      (Eventually.of_forall fun t => by simpa using norm_uvec_le t) crossCLM.flip
      (hzc.integrableOn_Icc.mono_set hIcc).restrict]
    rw [Measure.restrict_restrict hI, inter_eq_left.2 hIcc]
    congr 1
    funext t
    rw [ContinuousLinearMap.flip_apply, crossCLM_apply, cvx_cross_neg_uvec]
  rw [hL2, Measure.restrict_restrict hI, inter_eq_left.2 hIcc] at h
  have hwi : IntegrableOn (fun t => dot (z t) (vvec t)) I :=
    ((by unfold dot vvec; fun_prop : Continuous fun t => dot (z t) (vvec t)).integrableOn_Icc
      (a := a) (b := b)).mono_set hIcc
  have hgi' : IntegrableOn (fun t => dot (vplus K t) (vvec t)) I := by
    have h1 : IntegrableOn (fun t => -dot (vplus K t) (vvec t)) (Icc a b) := hgi
    have := h1.neg.mono_set hIcc
    simpa using this
  have e : ∫ t in I, dot (z t - vplus K t) (vvec t) =
      (∫ t in I, dot (z t) (vvec t)) - ∫ t in I, dot (vplus K t) (vvec t) := by
    simp_rw [dot_sub_left]
    exact integral_sub hwi hgi'
  rw [e]
  rw [integral_neg, integral_neg] at h
  linarith

/-- A bound for `α(t) = (𝐳(t) - v_K⁺(t)) · v_t` on `[a, b]`. -/
lemma cvx_alpha_bound {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} {z : ℝ → ℝ × ℝ}
    (hzc : ContinuousOn z (Icc a b)) :
    ∃ M : NNReal, ∀ t ∈ Icc a b, ‖dot (z t - vplus K t) (vvec t)‖ ≤ M := by
  obtain ⟨Rz, hRz⟩ := isCompact_Icc.exists_bound_of_continuousOn hzc
  obtain ⟨R, hR⟩ := cvx_exists_bound hK
  refine ⟨(2 * (Rz + R)).toNNReal, fun t ht => ?_⟩
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  rw [Real.norm_eq_abs]
  refine (abs_dot_le _ _).trans ?_
  have h1 := hRz t ht
  have h2 := hR _ (vplus_mem_edge hK t).1
  have h3 := norm_vvec_le t
  have h4 : ‖z t - vplus K t‖ ≤ Rz + R := (norm_sub_le _ _).trans (add_le_add h1 h2)
  have h5 : 0 ≤ 2 * (Rz + R) := by
    have : 0 ≤ ‖z t - vplus K t‖ := norm_nonneg _
    linarith
  calc 2 * ‖z t - vplus K t‖ * ‖vvec t‖ ≤ 2 * (Rz + R) * 1 := by
        gcongr
    _ = 2 * (Rz + R) := by ring

/-- `α(t) = (𝐳(t) - v_K⁺(t)) · v_t` is measurable. -/
lemma cvx_measurable_alpha {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {z : ℝ → ℝ × ℝ}
    (hzc : Continuous z) : Measurable fun t => dot (z t - vplus K t) (vvec t) :=
  continuous_dot_pair.measurable.comp ((hzc.measurable.sub (cvx_measurable_vplus hK)).prodMk
    continuous_vvec.measurable)

/-- `v_t × d𝐳 = α dt` as vector measures on `(a, b)`. -/
lemma cvx_withDensity_vvec_eq {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℝ × ℝ} (hzc : Continuous z) (hzbv : BoundedVariationOn z (Icc a b))
    (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) :
    ((lsMeasure z a b).restrict (Ioo a b)).withDensity vvec crossCLM =
      (volume.restrict (Ioo a b)).withDensityᵥ (fun t => dot (z t - vplus K t) (vvec t)) := by
  obtain ⟨M, hM⟩ := cvx_alpha_bound hK hzc.continuousOn (a := a) (b := b)
  have hαi : Integrable (fun t => dot (z t - vplus K t) (vvec t)) (volume.restrict (Ioo a b)) :=
    Measure.integrableOn_of_bounded (M := M) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (cvx_measurable_alpha hK hzc).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hM t ⟨ht.1.le, ht.2.le⟩)
  have hvi : ((lsMeasure z a b).restrict (Ioo a b)).Integrable vvec :=
    Integrable.of_bound continuous_vvec.aestronglyMeasurable 1
      (Eventually.of_forall norm_vvec_le)
  apply VectorMeasure.ext_of_Icc
  intro c d _
  rw [VectorMeasure.withDensity_apply hvi, withDensityᵥ_apply hαi measurableSet_Icc,
    VectorMeasure.restrict_restrict _ measurableSet_Icc measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Icc]
  exact cvx_integral_vvec_cross_dz hK hab hzc hzbv hzl (measurableSet_Icc.inter measurableSet_Ioo)
    inter_subset_right

/-- **Mamikon's theorem** for a curve `𝐳` continuous on the whole line. -/
theorem cvx_mamikon_core {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) {z : ℝ → ℝ × ℝ} (hzc : Continuous z) (hzbv : BoundedVariationOn z (Icc a b))
    (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) :
    segArea (vplus K a) (z a) + curveArea z a b + segArea (z b) (vminus K b) -
        convexCurveArea K a b =
      (1 / 2) * ∫ t in a..b, dot (z t - vplus K t) (vvec t) ^ 2 := by
  obtain ⟨M, hM⟩ := cvx_alpha_bound hK hzc.continuousOn (a := a) (b := b)
  have hαm := cvx_measurable_alpha hK hzc
  -- Step 1: the curve area functional of `𝐳` as an integral over `(a, b)`
  have h1 : curveArea z a b = (1 / 2) * ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure z a b] := by
    unfold curveArea curveBilin
    congr 1
    apply VectorMeasure.setIntegral_congr_set measurableSet_Icc measurableSet_Ioo
    refine ae_eq_set.2 ⟨?_, by rw [sdiff_eq_empty.2 Ioo_subset_Icc_self]; exact measure_empty⟩
    refine measure_mono_null (t := {a} ∪ {b}) ?_ (measure_union_null
      (cvx_lsMeasure_variation_singleton hab.le hzbv hzc.continuousOn a)
      (cvx_lsMeasure_variation_singleton hab.le hzbv hzc.continuousOn b))
    intro t ht
    simp only [mem_union, mem_singleton_iff]
    rcases ht.1.1.eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases ht.1.2.eq_or_lt with h' | h'
    · exact Or.inr h'
    exact absurd ⟨h, h'⟩ ht.2
  -- Step 2: integration by parts for `𝐳 × v_K⁺`
  have h2 := cvx_ibp_cross_vplus hK hab hzc.continuousOn hzbv
  -- Step 3: `∫ 𝐳 × dv_K⁺ = ∫ h_K dσ_K`
  have h3 : ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure (vplus K) a b] =
      ∫ t in Ioo a b, supp K t ∂(sigma K) := by
    have : IsFiniteMeasure ((sigma K).restrict (Ioo a b)) :=
      isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
    rw [cvx_integral_cross_dvplus' hK hab hb
      (hzc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => hzl t ⟨ht.1.le, ht.2.le⟩
  have hflip : ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM.flip; lsMeasure z a b] =
      -∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure z a b] := by
    rw [cvx_crossCLM_flip, VectorMeasure.integral_neg_cbm]
  -- Step 4: `(𝐳 - v_K⁺) = α v_t`
  obtain ⟨R, hR⟩ := cvx_exists_bound hK
  have hzi : ((lsMeasure z a b).restrict (Ioo a b)).Integrable z :=
    VectorMeasure.IntegrableOn.mono measurableSet_Icc Ioo_subset_Icc_self
      (cvx_integrable_restrict_Icc (lsMeasure z a b) hzc.continuousOn)
  have hvi : ((lsMeasure z a b).restrict (Ioo a b)).Integrable (vplus K) :=
    Integrable.of_bound (cvx_stronglyMeasurable_vplus hK).aestronglyMeasurable R
      (Eventually.of_forall fun t => hR _ (vplus_mem_edge hK t).1)
  have hsub : ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure z a b] -
      ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure z a b] =
      ∫ᵛ t in Ioo a b, dot (z t - vplus K t) (vvec t) • vvec t ∂[crossCLM; lsMeasure z a b] := by
    rw [← VectorMeasure.integral_fun_sub hzi hvi]
    apply VectorMeasure.setIntegral_congr_fun
    intro t ht
    exact sub_eq_smul_vvec (((vplus_mem_edge hK t).2).trans (hzl t ⟨ht.1.le, ht.2.le⟩).symm)
  -- Step 5: `∫ α v_t × d𝐳 = ∫ α² dt`
  have hαi : Integrable (fun t => dot (z t - vplus K t) (vvec t)) (volume.restrict (Ioo a b)) :=
    Measure.integrableOn_of_bounded (M := M) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      hαm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hM t ⟨ht.1.le, ht.2.le⟩)
  have hαi' : Integrable (fun t => dot (z t - vplus K t) (vvec t))
      ((lsMeasure z a b).restrict (Ioo a b)).variation := by
    rw [VectorMeasure.variation_restrict measurableSet_Ioo]
    exact Measure.integrableOn_of_bounded (M := M) (measure_ne_top _ _) hαm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hM t ⟨ht.1.le, ht.2.le⟩)
  have h6 : ∫ᵛ t in Ioo a b, dot (z t - vplus K t) (vvec t) • vvec t ∂[crossCLM; lsMeasure z a b] =
      ∫ t in Ioo a b, dot (z t - vplus K t) (vvec t) ^ 2 := by
    rw [cvx_integral_smul_eq_integral_withDensity (M := 1) continuous_vvec.aestronglyMeasurable
      (Eventually.of_forall fun t => by exact_mod_cast norm_vvec_le t) crossCLM hαi',
      cvx_withDensity_vvec_eq hK hab hzc hzbv hzl,
      cvx_integral_withDensityᵥ hαi (M := M)
        (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => hM t ⟨ht.1.le, ht.2.le⟩)
        (ContinuousLinearMap.lsmul ℝ ℝ) hαi]
    congr 1
    funext t
    simp [sq]
  rw [h1, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, ← h6, ← hsub]
  rw [hflip, h3] at h2
  unfold segArea convexCurveArea
  rw [cross_anticomm (vplus K a) (z a)]
  linarith

/-- Clamping the curve to `[a, b]` does not change its curve area functional on `[a, b]`. -/
lemma cvx_curveArea_clampFun {z : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) :
    curveArea (clampFun z a b) a b = curveArea z a b := by
  have hcl : clampFun (clampFun z a b) a b = clampFun z a b := by
    funext t
    show clampFun z a b (max a (min b t)) = z (max a (min b t))
    exact clampFun_of_mem (clamp_mem hab t)
  have hls : lsMeasure (clampFun z a b) a b = lsMeasure z a b := by
    unfold lsMeasure
    rw [hcl]
  unfold curveArea curveBilin
  rw [hls]
  congr 1
  exact VectorMeasure.setIntegral_congr_fun (fun t ht => clampFun_of_mem ht)

end aux

/-- The Mamikon region swept by the tangent segments from `v_K⁺(t)` to `v_K⁺(t) + α(t) v_t`,
`t ∈ [a, b]` (Definition 7.4.1, `def:mamikon-region`). -/
def mamikonRegion (K : Set (ℝ × ℝ)) (a b : ℝ) (α : ℝ → ℝ) : Set (ℝ × ℝ) :=
  ⋃ t ∈ Icc a b, segment ℝ (vplus K t) (vplus K t + α t • vvec t)

/-- `𝓜_K(a, b; 𝐳) = 𝒥(v_K⁺(a), 𝐳(a)) + 𝒥(𝐳|_{[a,b]}) + 𝒥(𝐳(b), v_K⁻(b)) - 𝒥(𝐮_K^{a,b})`
(Definition 7.4.2, `def:mamikon`). -/
noncomputable def mamikon (K : Set (ℝ × ℝ)) (a b : ℝ) (z : ℝ → ℝ × ℝ) : ℝ :=
  segArea (vplus K a) (z a) + curveArea z a b + segArea (z b) (vminus K b) - convexCurveArea K a b

/-- **Theorem 7.4.1** (`thm:mamikon`, Mamikon's theorem, generalized). For `a < b < a + π` and
`𝐳 ∈ C^BV[a, b]` with `𝐳(t) ∈ l_K(t)`, the function `α(t) = (𝐳(t) - v_K⁺(t)) · v_t` is bounded and
measurable, `𝐳(t) = v_K⁺(t) + α(t) v_t`, and `𝓜_K(a, b; 𝐳) = ½ ∫_a^b α(t)² dt`. -/
theorem theorem7_4_1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) {z : ℝ → ℝ × ℝ} (hz : IsCBV z a b) (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) :
    AEMeasurable (fun t => dot (z t - vplus K t) (vvec t)) (volume.restrict (Icc a b)) ∧
      (∃ C, ∀ t ∈ Icc a b, |dot (z t - vplus K t) (vvec t)| ≤ C) ∧
      (∀ t ∈ Icc a b, z t = vplus K t + dot (z t - vplus K t) (vvec t) • vvec t) ∧
      mamikon K a b z = (1 / 2) * ∫ t in a..b, dot (z t - vplus K t) (vvec t) ^ 2 := by
  -- Replace `𝐳` by its clamp to `[a, b]`, which is continuous on the whole line and agrees with
  -- `𝐳` on `[a, b]`; then apply `cvx_mamikon_core`.
  have hz'c : Continuous (clampFun z a b) := continuous_clampFun hab.le hz.1
  have hz'eq : ∀ t ∈ Icc a b, clampFun z a b t = z t := fun t ht => clampFun_of_mem ht
  have hz'bv : BoundedVariationOn (clampFun z a b) (Icc a b) := by
    unfold BoundedVariationOn
    rw [eVariationOn.eq_of_eqOn (fun t ht => hz'eq t ht)]
    exact hz.2
  have hz'l : ∀ t ∈ Icc a b, clampFun z a b t ∈ suppLine K t := fun t ht => by
    rw [hz'eq t ht]; exact hzl t ht
  have hαeq : ∀ t ∈ Icc a b, dot (clampFun z a b t - vplus K t) (vvec t) =
      dot (z t - vplus K t) (vvec t) := fun t ht => by rw [hz'eq t ht]
  obtain ⟨M, hM⟩ := cvx_alpha_bound hK hz.1 (a := a) (b := b)
  refine ⟨?_, ⟨M, fun t ht => by simpa [Real.norm_eq_abs] using hM t ht⟩, ?_, ?_⟩
  · refine (cvx_measurable_alpha hK hz'c).aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hαeq t ht
  · intro t ht
    have := sub_eq_smul_vvec ((vplus_mem_edge hK t).2.trans (hzl t ht).symm)
    rw [← this]
    abel
  · have hmam : mamikon K a b z = mamikon K a b (clampFun z a b) := by
      unfold mamikon
      rw [hz'eq a ⟨le_rfl, hab.le⟩, hz'eq b ⟨hab.le, le_rfl⟩, cvx_curveArea_clampFun hab.le]
    have hint : ∫ t in a..b, dot (z t - vplus K t) (vvec t) ^ 2 =
        ∫ t in a..b, dot (clampFun z a b t - vplus K t) (vvec t) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab.le] at ht
      simp only [hαeq t ht]
    rw [hmam, hint]
    exact cvx_mamikon_core hK hab hb hz'c hz'bv hz'l

/-- **Theorem 7.4.2** (`thm:mamikon-convex`). If `𝐳_K ∈ C^BV[a, b]` lies on the supporting lines
`l_K(t)` and depends convex-linearly on `K`, then `𝓜_K(a, b; 𝐳_K)` is a convex quadratic functional
of `K`. -/
theorem theorem7_4_2 {a b : ℝ} (hab : a < b) (hb : b < a + π) (z : ConvexBodySet → ℝ → ℝ × ℝ)
    (hz : ∀ K, IsCBV (z K) a b) (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
    (hlin : ∀ K₁ K₂, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb c K₁ K₂) t = (1 - c) • z K₁ t + c • z K₂ t) :
    convexBodyDomain.IsQuadratic (fun K => mamikon K.1 a b (z K)) ∧
      convexBodyDomain.IsConvexFun (fun K => mamikon K.1 a b (z K)) := by
  -- `α_K(t) = (𝐳_K(t) - v_K⁺(t)) · v_t`; by Theorem 7.4.1, `𝓜_K = ½ ∫_a^b α_K²`.
  set α : ConvexBodySet → ℝ → ℝ := fun K t => dot (z K t - vplus K.1 t) (vvec t) with hαdef
  have hM := fun K : ConvexBodySet => theorem7_4_1 K.2 hab hb (hz K) (hzl K)
  have hmam : ∀ K : ConvexBodySet, mamikon K.1 a b (z K) = (1 / 2) * ∫ t in a..b, α K t * α K t :=
    fun K => by rw [(hM K).2.2.2]; simp only [hαdef, sq]
  -- `α_K(t)` is convex-linear in `K`
  have hαlin : ∀ K₁ K₂ : ConvexBodySet, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      α (convexBodyComb c K₁ K₂) t = (1 - c) * α K₁ t + c * α K₂ t := by
    intro K₁ K₂ c hc t ht
    simp only [hαdef]
    rw [hlin K₁ K₂ c hc t ht, cvx_vplus_comb hc K₁ K₂ t]
    simp only [dot_sub_left, dot_add_left, dot_smul_left]
    ring
  -- `α_{K₁} α_{K₂}` is bounded and measurable, hence integrable
  have hint : ∀ K₁ K₂ : ConvexBodySet,
      IntervalIntegrable (fun t => α K₁ t * α K₂ t) volume a b := by
    intro K₁ K₂
    obtain ⟨C₁, hC₁⟩ := (hM K₁).2.1
    obtain ⟨C₂, hC₂⟩ := (hM K₂).2.1
    have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ a ⟨le_rfl, hab.le⟩)
    have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have : IntegrableOn (fun t => α K₁ t * α K₂ t) (Icc a b) := by
      refine Integrable.of_bound ((hM K₁).1.mul (hM K₂).1).aestronglyMeasurable (C₁ * C₂) ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC₁ t ht) (hC₂ t ht) (abs_nonneg _) hC₁0
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (this.mono_set Ioc_subset_Icc_self)
  -- the symmetric form `g(K₁, K₂) = ½ ∫ α_{K₁} α_{K₂}` is convex-linear in each argument
  set g : ConvexBodySet → ConvexBodySet → ℝ :=
    fun K₁ K₂ => (1 / 2) * ∫ t in a..b, α K₁ t * α K₂ t with hgdef
  have hsymm : ∀ K₁ K₂, g K₁ K₂ = g K₂ K₁ := fun K₁ K₂ => by
    simp only [hgdef, mul_comm (α K₁ _)]
  have hg : ∀ K, convexBodyDomain.IsConvexLinear realDomain (g K) := by
    intro K c hc v w
    simp only [realDomain, hgdef]
    rw [show convexBodyDomain.comb c v w = convexBodyComb c v w from rfl,
      intervalIntegral.integral_congr (g := fun t => (1 - c) * (α K t * α v t) +
        c * (α K t * α w t)) fun t ht => by
          rw [uIcc_of_le hab.le] at ht
          simp only [hαlin v w c hc t ht]
          ring,
      intervalIntegral.integral_add ((hint K v).const_mul _) ((hint K w).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  refine ⟨⟨g, ⟨hg, fun K₂ c hc v w => ?_⟩, hmam⟩, ?_⟩
  · simp only
    rw [hsymm _ K₂, hg K₂ c hc v w, hsymm K₂, hsymm K₂]
  -- convexity: `α_{c_λ}² ≤ (1 - λ) α_{K₁}² + λ α_{K₂}²` pointwise
  · intro K₁ K₂ c hc
    show mamikon (convexBodyComb c K₁ K₂).1 a b (z (convexBodyComb c K₁ K₂)) ≤
      (1 - c) * mamikon K₁.1 a b (z K₁) + c * mamikon K₂.1 a b (z K₂)
    rw [hmam, hmam, hmam]
    have hle : ∫ t in a..b, α (convexBodyComb c K₁ K₂) t * α (convexBodyComb c K₁ K₂) t ≤
        ∫ t in a..b, ((1 - c) * (α K₁ t * α K₁ t) + c * (α K₂ t * α K₂ t)) := by
      apply intervalIntegral.integral_mono_on hab.le (hint _ _)
        (((hint K₁ K₁).const_mul _).add ((hint K₂ K₂).const_mul _))
      intro t ht
      rw [hαlin K₁ K₂ c hc t ht]
      have h1 : 0 ≤ c * (1 - c) := mul_nonneg hc.1 (by linarith [hc.2])
      nlinarith [mul_nonneg h1 (sq_nonneg (α K₁ t - α K₂ t))]
    rw [intervalIntegral.integral_add ((hint K₁ K₁).const_mul _) ((hint K₂ K₂).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
    nlinarith

end MovingSofaOptimality
