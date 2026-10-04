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

/-- Integration by parts for `𝐳 × v_K⁺` on `(a, b)`: by Lemma 5.1.3 for the cross product (`𝐳` is
continuous), `d(𝐳 × v_K⁺) = d𝐳 × v_K⁺ + 𝐳 × dv_K⁺`, and `d(𝐳 × v_K⁺)((a, b))` is
`𝐳(b) × v_K⁻(b) - 𝐳(a) × v_K⁺(a)`, as `v_K⁺` is right-continuous with left limits `v_K⁻`
(Theorem 2.1.3). -/
lemma cvx_ibp_cross_vplus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℝ × ℝ} (hzc : ContinuousOn z (Icc a b)) (hzbv : BoundedVariationOn z (Icc a b)) :
    cross (z b) (vminus K b) - cross (z a) (vplus K a) =
      ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM.flip; lsMeasure z a b] +
        ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure (vplus K) a b] := by
  have hvbv := lemma5_2_1 hK a b
  have hzr := cvx_rightCont_of_continuousOn hzc
  have hvr : ∀ t ∈ Ico a b, ContinuousWithinAt (vplus K) (Ici t) t := fun t _ =>
    continuousWithinAt_Ioi_iff_Ici.1 (tendsto_vplus_right hK t)
  rw [← lemma5_1_3_cross hab.le hzbv hvbv hzr hvr (Or.inl hzc) Ioo_subset_Icc_self]
  -- the mass of `(a, b)` under `d(𝐳 × v_K⁺)`
  have hφ : BoundedVariationOn (fun t => cross (z t) (vplus K t)) (Icc a b) :=
    hzbv.bilinear_comp hvbv crossCLM
  have hΦ := boundedVariationOn_clampFun hab.le hφ
  have hφr : ∀ t ∈ Ico a b, ContinuousWithinAt (fun t => cross (z t) (vplus K t)) (Ici t) t :=
    fun t ht => ((hzr t ht).fst.mul (hvr t ht).snd).sub ((hzr t ht).snd.mul (hvr t ht).fst)
  have hzb : Tendsto z (𝓝[<] b) (𝓝 (z b)) :=
    (hzc b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi a, isOpen_Ioi, hab, fun _ hs => ⟨hs.1.le, hs.2.le⟩⟩)
  have hlim : Tendsto (fun t => cross (z t) (vplus K t)) (𝓝[<] b)
      (𝓝 (cross (z b) (vminus K b))) :=
    ((hzb.fst_nhds.mul (tendsto_vplus_left hK b).snd_nhds).sub
      (hzb.snd_nhds.mul (tendsto_vplus_left hK b).fst_nhds))
  have hl : Function.leftLim (clampFun (fun t => cross (z t) (vplus K t)) a b) b =
      cross (z b) (vminus K b) := by
    apply leftLim_eq_of_tendsto
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (clampFun_of_mem (f := fun t => cross (z t) (vplus K t)) ⟨ht.1.le, ht.2.le⟩).symm
  rw [lsMeasure_eq_vectorMeasure hΦ, hΦ.vectorMeasure_Ioo hab, hl, rightLim_clampFun hab.le hφr,
    clampFun_of_mem ⟨le_rfl, hab.le⟩]

/-- `d(x - y) = dx - dy` for curves of bounded variation on `[a, b]` (Proposition 5.1.1, for
curves): `d(𝐳 - 𝐯) = d𝐳 - d𝐯` in the proof of Theorem 7.4.1. -/
private lemma cvx_lsMeasure_sub {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : BoundedVariationOn x (Icc a b)) (hy : BoundedVariationOn y (Icc a b)) :
    lsMeasure (fun t => x t - y t) a b = lsMeasure x a b - lsMeasure y a b := by
  have hX := boundedVariationOn_clampFun hab hx
  have hY := boundedVariationOn_clampFun hab hy
  have hXY : BoundedVariationOn (clampFun (fun t => x t - y t) a b) univ := by
    convert boundedVariationOn_add hX (cvx_bv_const_smul hY (-1)) using 1
    funext t
    simp only [clampFun, Pi.smul_apply, neg_smul, one_smul, sub_eq_add_neg]
  rw [lsMeasure_eq_vectorMeasure hXY, lsMeasure_eq_vectorMeasure hX, lsMeasure_eq_vectorMeasure hY]
  refine VectorMeasure.ext_of_Icc _ _ fun c d hcd => ?_
  rw [sub_apply, hXY.vectorMeasure_Icc hcd, hX.vectorMeasure_Icc hcd, hY.vectorMeasure_Icc hcd,
    rightLim_eq_of_tendsto (f := clampFun (fun t => x t - y t) a b)
      ((hX.tendsto_rightLim d).sub (hY.tendsto_rightLim d)),
    leftLim_eq_of_tendsto (f := clampFun (fun t => x t - y t) a b)
      ((hX.tendsto_leftLim c).sub (hY.tendsto_leftLim c))]
  abel

/-- `φ V × (V dμ) = 0` for a real measure `μ` of finite variation: the vector measure `V dμ` is
parallel to `V`. This is the vanishing of the term `α v_t × v_t dα` in the last chain of equalities
in the proof of Theorem 7.4.1, checked coordinate by coordinate (`p × q = p₁ q₂ - p₂ q₁`). -/
private lemma cvx_integral_cross_withDensity_self {μ : VectorMeasure ℝ ℝ}
    [IsFiniteMeasure μ.variation] {V : ℝ → ℝ × ℝ} (hV : Continuous V) (hV1 : ∀ t, ‖V t‖ ≤ 1)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ t, ‖φ t‖ ≤ C) :
    ∫ᵛ t, φ t • V t ∂[crossCLM; μ.withDensity V (ContinuousLinearMap.lsmul ℝ ℝ).flip] = 0 := by
  have hV1' : ∀ᵐ t ∂μ.variation, ‖V t‖ ≤ (1 : NNReal) :=
    Eventually.of_forall fun t => by exact_mod_cast hV1 t
  have hvar := cvx_variation_withDensity_le hV1'
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip : (ℝ × ℝ) →L[ℝ] ℝ →L[ℝ] (ℝ × ℝ))
  -- bounded measurable functions are integrable against `μ` and against `V dμ`
  have hμ : ∀ {g : ℝ → ℝ}, Measurable g → (∀ t, ‖g t‖ ≤ C) → Integrable g μ.variation :=
    fun hg hgC => Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC)
  have hμ₂ : ∀ {g : ℝ → ℝ × ℝ}, Measurable g → (∀ t, ‖g t‖ ≤ C) → Integrable g μ.variation :=
    fun hg hgC => Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC)
  have hν : ∀ {g : ℝ → ℝ}, Measurable g → (∀ t, ‖g t‖ ≤ C) →
      Integrable g (μ.withDensity V (ContinuousLinearMap.lsmul ℝ ℝ).flip).variation :=
    fun hg hgC => ((hμ hg hgC).smul_measure ENNReal.coe_ne_top).mono_measure hvar
  have hν₂ : ∀ {g : ℝ → ℝ × ℝ}, Measurable g → (∀ t, ‖g t‖ ≤ C) →
      Integrable g (μ.withDensity V (ContinuousLinearMap.lsmul ℝ ℝ).flip).variation :=
    fun hg hgC => ((hμ₂ hg hgC).smul_measure ENNReal.coe_ne_top).mono_measure hvar
  have hsm : ∀ {g : ℝ → ℝ}, (∀ t, ‖g t‖ ≤ C) → ∀ t, ‖g t • V t‖ ≤ C := fun hgC t =>
    (norm_smul _ _).trans_le ((mul_le_of_le_one_right (norm_nonneg _) (hV1 t)).trans (hgC t))
  -- a coordinate `L` of `∫ g d(V dμ)` is `∫ g L(V) dμ`
  have hcoord : ∀ (L : (ℝ × ℝ) →L[ℝ] ℝ) {g : ℝ → ℝ}, Measurable g → (∀ t, ‖g t‖ ≤ C) →
      ∫ᵛ t, g t ∂[(ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ L) ∘L
        ContinuousLinearMap.lsmul ℝ ℝ; μ.withDensity V (ContinuousLinearMap.lsmul ℝ ℝ).flip] =
        ∫ᵛ t, g t * L (V t) ∂•μ := by
    intro L g hg hgC
    have hgV : Integrable (fun t => g t • V t) μ.variation := hμ₂ (hg.smul hV.measurable) (hsm hgC)
    have hL : (ContinuousLinearMap.compL ℝ ℝ (ℝ × ℝ) ℝ L) ∘L
        ((ContinuousLinearMap.lsmul ℝ ℝ).flip : (ℝ × ℝ) →L[ℝ] ℝ →L[ℝ] (ℝ × ℝ)) =
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) ∘L L :=
      ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun r => by simp [mul_comm]
    rw [← VectorMeasure.continuousLinearMap_apply_integral (hν hg hgC),
      ← cvx_integral_smul_eq_integral_withDensity hV.aestronglyMeasurable hV1' _ (hμ hg hgC),
      VectorMeasure.continuousLinearMap_apply_integral hgV, hL,
      ← VectorMeasure.integral_continuousLinearMap_comp hgV]
    simp only [map_smul, smul_eq_mul]
  -- `p × q = p₁ q₂ - p₂ q₁`
  have hc : crossCLM = ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ
      (ContinuousLinearMap.snd ℝ ℝ ℝ)) ∘L ContinuousLinearMap.lsmul ℝ ℝ) ∘L
        ContinuousLinearMap.fst ℝ ℝ ℝ - ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) ∘L ContinuousLinearMap.lsmul ℝ ℝ) ∘L
        ContinuousLinearMap.snd ℝ ℝ ℝ :=
    ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => by simp [cross]
  have hφV : Integrable (fun t => φ t • V t)
      (μ.withDensity V (ContinuousLinearMap.lsmul ℝ ℝ).flip).variation :=
    hν₂ (hφ.smul hV.measurable) (hsm hφC)
  rw [hc, VectorMeasure.integral_sub_cbm hφV,
    ← VectorMeasure.integral_continuousLinearMap_comp hφV,
    ← VectorMeasure.integral_continuousLinearMap_comp hφV]
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hcoord _ (g := fun t => (φ t • V t).1) (hφ.smul hV.measurable).fst
      fun t => (norm_fst_le _).trans (hsm hφC t),
    hcoord _ (g := fun t => (φ t • V t).2) (hφ.smul hV.measurable).snd
      fun t => (norm_snd_le _).trans (hsm hφC t), sub_eq_zero]
  congr 1
  funext t
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

/-- The last chain of equalities in the proof of Theorem 7.4.1: for `α` right-continuous and of
bounded variation on `[a, b]`, `α v_t × d(α v_t) = α v_t × (v_t dα + α dv_t) = α² dt` on `(a, b)`.
The product rule `d(α v_t) = v_t dα + α dv_t` is Lemma 5.1.3 for the pairing `(α, v) ↦ α v`, in
Mathlib's form for a general pairing (`BoundedVariationOn.vectorMeasure_bilinear_comp_eq'`; `v_t` is
continuous). Then `α v_t × v_t dα = 0` (`cvx_integral_cross_withDensity_self`), and
`α v_t × α dv_t = α² (v_t × (-u_t)) dt = α² dt` as `dv_t = -u_t dt`. -/
private lemma cvx_integral_cross_d_smul_vvec {α : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hα : BoundedVariationOn α (Icc a b)) (hαr : ∀ t ∈ Ico a b, ContinuousWithinAt α (Ici t) t)
    (hαm : Measurable α) {M : NNReal} (hαM : ∀ t ∈ Icc a b, ‖α t‖ ≤ M) :
    ∫ᵛ t in Ioo a b, α t • vvec t ∂[crossCLM; lsMeasure (fun t => α t • vvec t) a b] =
      ∫ t in Ioo a b, α t ^ 2 := by
  obtain ⟨hvbv, hvc⟩ := cvx_bv_vvec hab.le
  have hF : BoundedVariationOn (clampFun α a b) univ := boundedVariationOn_clampFun hab.le hα
  have hV : BoundedVariationOn (clampFun vvec a b) univ := boundedVariationOn_clampFun hab.le hvbv
  have hVc : Continuous (clampFun vvec a b) := continuous_clampFun hab.le hvc
  have hV1 : ∀ t, ‖clampFun vvec a b t‖ ≤ 1 := fun t => norm_vvec_le _
  have hFm : Measurable (clampFun α a b) :=
    hαm.comp (by fun_prop : Continuous fun t : ℝ => max a (min b t)).measurable
  have hFM : ∀ t, ‖clampFun α a b t‖ ≤ M := fun t => hαM _ (clamp_mem hab.le t)
  have hFu : ∀ t, ‖clampFun α a b t • -uvec t‖ ≤ M := fun t => by
    rw [norm_smul, norm_neg]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_uvec_le t)).trans (hFM t)
  have hFV : ∀ t, ‖clampFun α a b t • clampFun vvec a b t‖ ≤ M := fun t => by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hV1 t)).trans (hFM t)
  have hFVm : Measurable fun t => clampFun α a b t • clampFun vvec a b t :=
    hFm.smul hVc.measurable
  have hIcc : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hu : Integrable (fun t => -uvec t) (volume.restrict (Icc a b)) :=
    (continuous_uvec.neg).integrableOn_Icc
  have hFi : Integrable (clampFun α a b) (volume.restrict (Icc a b)) :=
    Measure.integrableOn_of_bounded (M := M) hIcc hFm.aestronglyMeasurable
      (Eventually.of_forall hFM)
  have hFui : Integrable (fun t => clampFun α a b t • -uvec t) (volume.restrict (Icc a b)) :=
    Measure.integrableOn_of_bounded (M := M) hIcc
      (hFm.smul continuous_uvec.neg.measurable).aestronglyMeasurable (Eventually.of_forall hFu)
  have hFVi : Integrable (fun t => clampFun α a b t • clampFun vvec a b t)
      (volume.restrict (Icc a b)) :=
    Measure.integrableOn_of_bounded (M := M) hIcc hFVm.aestronglyMeasurable
      (Eventually.of_forall hFV)
  -- Step 1: the product rule `d(α v_t) = v_t dα + α dv_t` (Lemma 5.1.3), with `dv_t = -u_t dt`
  have hPR : lsMeasure (fun t => α t • vvec t) a b =
      (lsMeasure α a b).withDensity (clampFun vvec a b) (ContinuousLinearMap.lsmul ℝ ℝ).flip +
        (volume.restrict (Icc a b)).withDensityᵥ (fun t => clampFun α a b t • -uvec t) := by
    have hFV' : BoundedVariationOn (clampFun (fun t => α t • vvec t) a b) univ := hF.smul hV
    have hl : Function.leftLim (clampFun vvec a b) = clampFun vvec a b :=
      funext (leftLim_clampFun hab.le hvc)
    have hr : Function.rightLim (clampFun α a b) = clampFun α a b :=
      funext (rightLim_clampFun hab.le hαr)
    rw [lsMeasure_eq_vectorMeasure hFV', show hFV'.vectorMeasure =
        (hF.bilinear_comp hV (ContinuousLinearMap.lsmul ℝ ℝ)).vectorMeasure from rfl,
      hF.vectorMeasure_bilinear_comp_eq' hV, hl, hr, ← lsMeasure_eq_vectorMeasure hF,
      ← lsMeasure_eq_vectorMeasure hV]
    congr 1
    refine VectorMeasure.ext fun s hs => ?_
    rw [VectorMeasure.withDensity_apply (Integrable.of_bound hFm.aestronglyMeasurable M
        (Eventually.of_forall hFM)), cvx_lsMeasure_vvec hab.le, cvx_withDensityᵥ_restrict hu hs,
      cvx_integral_withDensityᵥ hu.restrict (M := 1)
        (Eventually.of_forall fun t => by simpa using norm_uvec_le t) _ hFi.restrict,
      withDensityᵥ_apply hFui hs]
    rfl
  -- Step 2: `α v_t × v_t dα = 0`
  have hVi : (lsMeasure α a b).Integrable (clampFun vvec a b) :=
    Integrable.of_bound hVc.aestronglyMeasurable 1 (Eventually.of_forall hV1)
  have hQ₁ : ∫ᵛ t, clampFun α a b t • clampFun vvec a b t ∂[crossCLM;
      ((lsMeasure α a b).withDensity (clampFun vvec a b)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip).restrict (Ioo a b)] = 0 := by
    have : IsFiniteMeasure ((lsMeasure α a b).restrict (Ioo a b)).variation := by
      rw [VectorMeasure.variation_restrict measurableSet_Ioo]; infer_instance
    rw [VectorMeasure.restrict_withDensity hVi]
    exact cvx_integral_cross_withDensity_self hVc hV1 hFm hFM
  -- Step 3: `α v_t × α dv_t = α² (v_t × (-u_t)) dt = α² dt`
  have hQ₂ : ∫ᵛ t, clampFun α a b t • clampFun vvec a b t ∂[crossCLM;
      ((volume.restrict (Icc a b)).withDensityᵥ
        (fun t => clampFun α a b t • -uvec t)).restrict (Ioo a b)] = ∫ t in Ioo a b, α t ^ 2 := by
    have hle : volume.restrict (Ioo a b) ≤ volume.restrict (Icc a b) :=
      Measure.restrict_mono Ioo_subset_Icc_self le_rfl
    rw [cvx_withDensityᵥ_restrict hFui measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Icc_self,
      cvx_integral_withDensityᵥ (hFui.mono_measure hle)
        (M := M) (Eventually.of_forall hFu) crossCLM (hFVi.mono_measure hle)]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have h1 : cross (vvec t) (-uvec t) = 1 := by
      simp only [cross, vvec, uvec, Prod.fst_neg, Prod.snd_neg]
      linear_combination sin_sq_add_cos_sq t
    simp only [crossCLM_apply, clampFun_of_mem (Ioo_subset_Icc_self ht), cross_smul_left,
      cross_smul_right, h1]
    ring
  have hcongr : ∫ᵛ t in Ioo a b, α t • vvec t ∂[crossCLM; lsMeasure (fun t => α t • vvec t) a b] =
      ∫ᵛ t in Ioo a b, clampFun α a b t • clampFun vvec a b t ∂[crossCLM;
        lsMeasure (fun t => α t • vvec t) a b] :=
    VectorMeasure.setIntegral_congr_fun fun t ht => by
      simp only [clampFun_of_mem (Ioo_subset_Icc_self ht)]
  have h₁ : (((lsMeasure α a b).withDensity (clampFun vvec a b)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip).restrict (Ioo a b)).Integrable
        (fun t => clampFun α a b t • clampFun vvec a b t) :=
    VectorMeasure.Integrable.restrict (((Integrable.of_bound hFVm.aestronglyMeasurable M
      (Eventually.of_forall hFV) : (lsMeasure α a b).Integrable _).smul_measure
        ENNReal.coe_ne_top).mono_measure (cvx_variation_withDensity_le (M := 1)
          (Eventually.of_forall fun t => by exact_mod_cast hV1 t) _))
  have h₂ : (((volume.restrict (Icc a b)).withDensityᵥ
      (fun t => clampFun α a b t • -uvec t)).restrict (Ioo a b)).Integrable
        (fun t => clampFun α a b t • clampFun vvec a b t) :=
    VectorMeasure.Integrable.restrict ((hFVi.smul_measure ENNReal.coe_ne_top).mono_measure
      (cvx_variation_withDensityᵥ_le hFui (Eventually.of_forall hFu)))
  rw [hcongr, hPR, VectorMeasure.restrict_add, VectorMeasure.integral_add_vectorMeasure h₁ h₂, hQ₁,
    hQ₂, zero_add]

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

/-- **Mamikon's theorem** for a curve `𝐳` continuous on the whole line. As in the paper, with
`𝐯 = v_K⁺`: `𝐳 × d𝐳 - 𝐯 × d𝐯 + d(𝐳 × 𝐯) = (𝐳 - 𝐯) × d(𝐳 + 𝐯) = (𝐳 - 𝐯) × d(𝐳 - 𝐯)
= α v_t × d(α v_t) = α² dt` on `(a, b)`. -/
theorem cvx_mamikon_core {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b)
    (hb : b < a + π) {z : ℝ → ℝ × ℝ} (hzc : Continuous z) (hzbv : BoundedVariationOn z (Icc a b))
    (hzl : ∀ t ∈ Icc a b, z t ∈ suppLine K t) :
    segArea (vplus K a) (z a) + curveArea z a b + segArea (z b) (vminus K b) -
        convexCurveArea K a b =
      (1 / 2) * ∫ t in a..b, dot (z t - vplus K t) (vvec t) ^ 2 := by
  obtain ⟨M, hM⟩ := cvx_alpha_bound hK hzc.continuousOn (a := a) (b := b)
  obtain ⟨R, hR⟩ := cvx_exists_bound hK
  have hvbv := lemma5_2_1 hK a b
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
  -- Step 2: `d(𝐳 × 𝐯) = d𝐳 × 𝐯 + 𝐳 × d𝐯` on `(a, b)` (Lemma 5.1.3, `𝐳` continuous)
  have h2 := cvx_ibp_cross_vplus hK hab hzc.continuousOn hzbv
  -- Step 3: `(𝐳 - 𝐯) × d𝐯 = 0`, as `d𝐯 = v_t σ_K` (Theorem 5.2.2) and `𝐳 - 𝐯` is parallel to `v_t`
  have hzi' : ((lsMeasure (vplus K) a b).restrict (Ioo a b)).Integrable z :=
    VectorMeasure.IntegrableOn.mono measurableSet_Icc Ioo_subset_Icc_self
      (cvx_integrable_restrict_Icc (lsMeasure (vplus K) a b) hzc.continuousOn)
  have hvi' : ((lsMeasure (vplus K) a b).restrict (Ioo a b)).Integrable (vplus K) :=
    Integrable.of_bound (cvx_stronglyMeasurable_vplus hK).aestronglyMeasurable R
      (Eventually.of_forall fun t => hR _ (vplus_mem_edge hK t).1)
  have h0 : ∫ᵛ t in Ioo a b, (z t - vplus K t) ∂[crossCLM; lsMeasure (vplus K) a b] = 0 := by
    have : IsFiniteMeasure ((sigma K).restrict (Ioo a b)) :=
      isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
    have hzσ : Integrable z ((sigma K).restrict (Ioo a b)) :=
      hzc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hvσ : Integrable (vplus K) ((sigma K).restrict (Ioo a b)) :=
      Integrable.of_bound (cvx_stronglyMeasurable_vplus hK).aestronglyMeasurable R
        (Eventually.of_forall fun t => hR _ (vplus_mem_edge hK t).1)
    rw [cvx_integral_cross_dvplus' hK hab hb (g := fun t => z t - vplus K t) (hzσ.sub hvσ)]
    refine (setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Ioo fun t ht => ?_).trans
      (integral_zero _ _)
    rw [dot_sub_left, dot_vplus_uvec, show dot (z t) (uvec t) = supp K t from
      hzl t ⟨ht.1.le, ht.2.le⟩, sub_self]
  -- so `∫ 𝐳 × d𝐯 = ∫ 𝐯 × d𝐯 = 2 𝒥(𝐮_K^{a,b}) = ∫ h_K dσ_K` (Lemma 7.3.3)
  have h3 : ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure (vplus K) a b] =
      ∫ t in Ioo a b, supp K t ∂(sigma K) := by
    have hsplit : ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure (vplus K) a b] -
        ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure (vplus K) a b] =
        ∫ᵛ t in Ioo a b, (z t - vplus K t) ∂[crossCLM; lsMeasure (vplus K) a b] := by
      rw [← VectorMeasure.integral_fun_sub hzi' hvi']
    have e := lemma7_3_3_self hK hab hb
    unfold convexCurveArea at e
    linarith
  have hflip : ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM.flip; lsMeasure z a b] =
      -∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure z a b] := by
    rw [cvx_crossCLM_flip, VectorMeasure.integral_neg_cbm]
  -- Step 4: by bilinearity, `𝐳 × d𝐳 + d𝐳 × 𝐯 = (𝐳 - 𝐯) × d𝐳`, which is `(𝐳 - 𝐯) × d(𝐳 - 𝐯)` by
  -- Step 3, as `d(𝐳 - 𝐯) = d𝐳 - d𝐯`
  have hzi : ((lsMeasure z a b).restrict (Ioo a b)).Integrable z :=
    VectorMeasure.IntegrableOn.mono measurableSet_Icc Ioo_subset_Icc_self
      (cvx_integrable_restrict_Icc (lsMeasure z a b) hzc.continuousOn)
  have hvi : ((lsMeasure z a b).restrict (Ioo a b)).Integrable (vplus K) :=
    Integrable.of_bound (cvx_stronglyMeasurable_vplus hK).aestronglyMeasurable R
      (Eventually.of_forall fun t => hR _ (vplus_mem_edge hK t).1)
  have hsub : ∫ᵛ t in Ioo a b, z t ∂[crossCLM; lsMeasure z a b] -
      ∫ᵛ t in Ioo a b, vplus K t ∂[crossCLM; lsMeasure z a b] =
      ∫ᵛ t in Ioo a b, (z t - vplus K t) ∂[crossCLM;
        lsMeasure (fun t => z t - vplus K t) a b] := by
    rw [← VectorMeasure.integral_fun_sub hzi hvi, cvx_lsMeasure_sub hab.le hzbv hvbv,
      VectorMeasure.restrict_sub, VectorMeasure.integral_sub_vectorMeasure
        (f := fun t => z t - vplus K t) (hzi.sub hvi) (hzi'.sub hvi'), h0, sub_zero]
  -- Step 5: `𝐳 - 𝐯 = α v_t` on `[a, b]`; `α` is right-continuous and of bounded variation, as
  -- `𝐳` is and `𝐯` is by Lemma 5.2.1; and `α v_t × d(α v_t) = α² dt`
  have hw : ∀ t ∈ Icc a b, z t - vplus K t = dot (z t - vplus K t) (vvec t) • vvec t :=
    fun t ht => sub_eq_smul_vvec (((vplus_mem_edge hK t).2).trans (hzl t ht).symm)
  have hd : ∫ᵛ t in Ioo a b, (z t - vplus K t) ∂[crossCLM;
      lsMeasure (fun t => z t - vplus K t) a b] =
      ∫ᵛ t in Ioo a b, dot (z t - vplus K t) (vvec t) • vvec t ∂[crossCLM;
        lsMeasure (fun t => dot (z t - vplus K t) (vvec t) • vvec t) a b] := by
    have e : lsMeasure (fun t => z t - vplus K t) a b =
        lsMeasure (fun t => dot (z t - vplus K t) (vvec t) • vvec t) a b := by
      unfold lsMeasure
      rw [clampFun_congr hab.le fun t ht => hw t ht]
    rw [e]
    exact VectorMeasure.setIntegral_congr_fun fun t ht => hw t ⟨ht.1.le, ht.2.le⟩
  have hwbv : BoundedVariationOn (fun t => z t - vplus K t) (Icc a b) := by
    convert boundedVariationOn_add hzbv (cvx_bv_const_smul hvbv (-1)) using 1
    funext t
    simp only [Pi.smul_apply, neg_smul, one_smul, sub_eq_add_neg]
  have hubv : BoundedVariationOn uvec (Icc a b) :=
    boundedVariationOn_of_lipschitz (lipschitzWith_of_nnnorm_deriv_le (C := 1)
      (fun t => (hasDerivAt_uvec t).differentiableAt) fun t => by
        rw [(hasDerivAt_uvec t).deriv]; exact_mod_cast norm_vvec_le t) a b
  have hαbv : BoundedVariationOn (fun t => dot (z t - vplus K t) (vvec t)) (Icc a b) := by
    convert cvx_bv_const_smul (hwbv.bilinear_comp hubv crossCLM) (-1) using 1
    funext t
    simp only [Pi.smul_apply, crossCLM_apply, cross_uvec, smul_eq_mul]
    ring
  have hαr : ∀ t ∈ Ico a b,
      ContinuousWithinAt (fun t => dot (z t - vplus K t) (vvec t)) (Ici t) t :=
    fun t _ => continuous_dot_pair.continuousAt.comp_continuousWithinAt
      ((hzc.continuousWithinAt.sub (continuousWithinAt_Ioi_iff_Ici.1
        (tendsto_vplus_right hK t))).prodMk continuous_vvec.continuousWithinAt)
  have h6 := cvx_integral_cross_d_smul_vvec hab hαbv hαr (cvx_measurable_alpha hK hzc) hM
  rw [h1, intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, ← h6, ← hd, ← hsub]
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
    -- `𝐳_K(t)` and `v_K⁺(t)` are convex-linear in `K` (Theorem 7.1.2 (2))
    have hv : vplus (convexBodyComb c K₁ K₂).1 t = (1 - c) • vplus K₁.1 t + c • vplus K₂.1 t :=
      (theorem7_1_2_vertices t t).1 c hc K₁ K₂
    rw [hlin K₁ K₂ c hc t ht, hv]
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
