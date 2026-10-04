module

public import MovingSofaOptimality.Convex.ConvexDomain

/-!
# The curve area functional (§7.2)

Definitions 7.2.4 (`def:plane-cross-product`), 7.2.5 (`def:bounded-variation-space`), 7.2.6
(`def:curve-area-functional`), 7.2.8 (`def:curve-area-line-segment`); Propositions 7.2.2,
7.2.4–7.2.6.

**Not formalized from this section.** The Jordan curve theorem (Theorem 7.2.1, cited), Green's
theorem for rectifiable Jordan curves (Theorem 7.2.3, cited from Apostol), the notions of Jordan
arcs and curves and their orientation (Definitions 7.2.1–7.2.3, 7.2.7, 7.2.9) and Proposition
7.2.7 (the orientation of a Jordan curve with a boundary segment). The paper uses them to compute
the areas of specific regions (Lemmas 8.2.2–8.2.3, Theorem 8.4.6); the formalization computes
those areas directly (Fubini and changes of variables). The curve area functional is defined for
every continuous curve of bounded variation, as in Definition 7.2.6, and concatenation is
splitting the parameter interval.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-! ### Auxiliary results on Lebesgue–Stieltjes measures and vector-measure integrals -/

section aux

open scoped NNReal ENNReal

/-- A constant multiple of a function of bounded variation has bounded variation. -/
lemma cvx_bv_const_smul {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (c : ℝ) :
    BoundedVariationOn (c • f) s :=
  (lipschitzWith_smul c).lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) hf

variable {E : Type*} [NormedAddCommGroup E]

variable [CompleteSpace E]

/-- The Lebesgue–Stieltjes measure has finite total variation. -/
instance cvx_isFiniteMeasure_variation_lsMeasure (f : ℝ → E) (a b : ℝ) :
    IsFiniteMeasure (lsMeasure f a b).variation := by
  unfold lsMeasure
  split_ifs
  · infer_instance
  · rw [VectorMeasure.variation_zero]; infer_instance

/-- The Lebesgue–Stieltjes measure of a continuous function of bounded variation on a closed
interval. -/
lemma cvx_lsMeasure_Icc {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) {c d : ℝ} (hcd : c ≤ d) :
    lsMeasure f a b (Icc c d) = clampFun f a b d - clampFun f a b c := by
  have hc := continuous_clampFun hab hfc
  rw [lsMeasure_eq_vectorMeasure (boundedVariationOn_clampFun hab hf),
    BoundedVariationOn.vectorMeasure_Icc _ hcd, hc.continuousWithinAt.rightLim_eq,
    hc.continuousWithinAt.leftLim_eq]

/-- A continuous curve of bounded variation gives no mass to points. -/
lemma cvx_lsMeasure_variation_singleton {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfc : ContinuousOn f (Icc a b)) (t : ℝ) :
    (lsMeasure f a b).variation {t} = 0 := by
  have hc := continuous_clampFun hab hfc
  rw [lsMeasure_eq_vectorMeasure (boundedVariationOn_clampFun hab hf),
    BoundedVariationOn.variation_vectorMeasure_singleton, hc.continuousWithinAt.rightLim_eq,
    hc.continuousWithinAt.leftLim_eq, sub_self, enorm_zero]

/-- The Lebesgue–Stieltjes measure on `[a, b]` restricted to a subinterval `[a', b']` is the
Lebesgue–Stieltjes measure on `[a', b']`. -/
lemma cvx_lsMeasure_restrict_Icc {f : ℝ → E} {a b a' b' : ℝ} (ha : a ≤ a') (hab' : a' ≤ b')
    (hb : b' ≤ b) (hf : BoundedVariationOn f (Icc a b)) (hfc : ContinuousOn f (Icc a b)) :
    (lsMeasure f a b).restrict (Icc a' b') = (lsMeasure f a' b').restrict (Icc a' b') := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  apply VectorMeasure.ext_of_Icc
  intro p q _
  rw [VectorMeasure.restrict_apply _ measurableSet_Icc measurableSet_Icc,
    VectorMeasure.restrict_apply _ measurableSet_Icc measurableSet_Icc, Icc_inter_Icc]
  rcases le_or_gt (max p a') (min q b') with h | h
  · have h1 : max p a' ∈ Icc a' b' := ⟨le_max_right _ _, h.trans (min_le_right _ _)⟩
    have h2 : min q b' ∈ Icc a' b' := ⟨(le_max_right _ _).trans h, min_le_right _ _⟩
    rw [cvx_lsMeasure_Icc (ha.trans (hab'.trans hb)) hf hfc h,
      cvx_lsMeasure_Icc hab' (hf.mono hsub) (hfc.mono hsub) h,
      clampFun_of_mem h1, clampFun_of_mem h2, clampFun_of_mem (hsub h1),
      clampFun_of_mem (hsub h2)]
  · rw [Icc_eq_empty (not_le.2 h)]; simp

omit [CompleteSpace E] in
/-- A function continuous on `[a, b]` is integrable against a finite vector measure restricted to
`[a, b]`. -/
lemma cvx_integrable_restrict_Icc {F' : Type*} [NormedAddCommGroup F'] (ν : VectorMeasure ℝ E)
    [IsFiniteMeasure ν.variation] {x : ℝ → F'} {a b : ℝ} (hx : ContinuousOn x (Icc a b)) :
    (ν.restrict (Icc a b)).Integrable x := by
  show Integrable x (ν.restrict (Icc a b)).variation
  rw [VectorMeasure.variation_restrict measurableSet_Icc]
  exact hx.integrableOn_Icc

omit [CompleteSpace E] in
/-- A primitive of a bounded integrable function is Lipschitz. -/
lemma cvx_lipschitzOnWith_of_primitive [NormedSpace ℝ E] {x ψ : ℝ → E} {a b : ℝ} {M : ℝ≥0}
    (hψ : IntegrableOn ψ (Icc a b)) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, ψ s) : LipschitzOnWith M x (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hi : ∀ u ∈ Icc a b, IntervalIntegrable ψ volume a u := fun u hu =>
    (hψ.mono_set (by rw [uIcc_of_le hu.1]; exact Icc_subset_Icc le_rfl hu.2)).intervalIntegrable
  rw [dist_eq_norm, hx s hs, hx t ht, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hi s hs) (hi t ht)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => hψM u ?_)).trans ?_
  · rcases le_total t s with h | h
    · rw [uIoc_of_le h] at hu; exact ⟨ht.1.trans hu.1.le, hu.2.trans hs.2⟩
    · rw [uIoc_of_ge h] at hu; exact ⟨hs.1.trans hu.1.le, hu.2.trans ht.2⟩
  · rw [Real.dist_eq]

omit [CompleteSpace E] in
/-- A primitive of a bounded integrable function is continuous and of bounded variation. -/
lemma cvx_bv_of_primitive [NormedSpace ℝ E] {x ψ : ℝ → E} {a b : ℝ} {M : ℝ≥0} (hab : a ≤ b)
    (hψ : IntegrableOn ψ (Icc a b)) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, ψ s) :
    BoundedVariationOn x (Icc a b) ∧ ContinuousOn x (Icc a b) := by
  have hlip := cvx_lipschitzOnWith_of_primitive hψ hψM hx
  refine ⟨?_, hlip.continuousOn⟩
  simpa using hlip.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

omit [NormedAddCommGroup E] [CompleteSpace E] in
/-- For `p ≤ q`, the interval between the clamped endpoints `max a (min b ·)` is `[p, q] ∩ [a, b]`
up to a null set. -/
private lemma cvx_Icc_clamp_ae_eq {a b p q : ℝ} (hab : a ≤ b) (hpq : p ≤ q) :
    Icc (max a (min b p)) (max a (min b q)) =ᵐ[volume] Icc (max p a) (min q b) := by
  rcases le_or_gt (max p a) (min q b) with h | h
  · have e1 : max a (min b p) = max p a := by
      simp only [max_def, min_def] at *; split_ifs at * <;> linarith
    have e2 : max a (min b q) = min q b := by
      simp only [max_def, min_def] at *; split_ifs at * <;> linarith
    rw [e1, e2]
  · have e : max a (min b p) = max a (min b q) := by
      simp only [max_def, min_def] at *; split_ifs at * <;> linarith
    rw [e, Icc_self, Icc_eq_empty h.not_ge]
    exact ae_eq_empty.2 (measure_singleton _)

/-- The Lebesgue–Stieltjes measure of a primitive `x(t) = x(a) + ∫_a^t ψ` is `ψ dt`. -/
lemma cvx_lsMeasure_eq_withDensityᵥ [NormedSpace ℝ E] {x ψ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hψ : IntegrableOn ψ (Icc a b)) (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, ψ s)
    (hbv : BoundedVariationOn x (Icc a b)) (hxc : ContinuousOn x (Icc a b)) :
    lsMeasure x a b = (volume.restrict (Icc a b)).withDensityᵥ ψ := by
  have hi : ∀ u ∈ Icc a b, IntervalIntegrable ψ volume a u := fun u hu =>
    (hψ.mono_set (by rw [uIcc_of_le hu.1]; exact Icc_subset_Icc le_rfl hu.2)).intervalIntegrable
  apply VectorMeasure.ext_of_Icc
  intro p q hpq
  rw [cvx_lsMeasure_Icc hab hbv hxc hpq, withDensityᵥ_apply hψ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, Icc_inter_Icc]
  have key : clampFun x a b q - clampFun x a b p =
      ∫ t in (max a (min b p))..(max a (min b q)), ψ t := by
    simp only [clampFun]
    rw [hx _ (clamp_mem hab q), hx _ (clamp_mem hab p), add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hi _ (clamp_mem hab q))
        (hi _ (clamp_mem hab p))]
  rw [key, intervalIntegral.integral_of_le (max_le_max le_rfl (min_le_min le_rfl hpq)),
    ← integral_Icc_eq_integral_Ioc, setIntegral_congr_set (cvx_Icc_clamp_ae_eq hab hpq)]

omit [CompleteSpace E] in
/-- The restriction of a vector measure with density is the vector measure with density with
respect to the restricted measure. -/
lemma cvx_withDensityᵥ_restrict [NormedSpace ℝ E] {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → E} (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensityᵥ f).restrict s = (μ.restrict s).withDensityᵥ f := by
  ext t ht
  rw [VectorMeasure.restrict_apply _ hs ht, withDensityᵥ_apply hf (ht.inter hs),
    withDensityᵥ_apply hf.restrict ht, Measure.restrict_restrict ht]

end aux

section density

open scoped NNReal ENNReal

/-- The set of `L¹` functions on which two Lipschitz functionals agree is closed. -/
lemma cvx_isClosed_eq_of_lipschitz {X E G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup G] {μ : Measure X} {Φ Ψ : (X → E) → G} {K : ℝ≥0}
    (hΦ : ∀ g₁ g₂ : X →₁[μ] E, dist (Φ g₁) (Φ g₂) ≤ K * dist g₁ g₂)
    (hΨ : ∀ g₁ g₂ : X →₁[μ] E, dist (Ψ g₁) (Ψ g₂) ≤ K * dist g₁ g₂) :
    IsClosed {g : X →₁[μ] E | Φ g = Ψ g} :=
  isClosed_eq (LipschitzWith.of_dist_le_mul hΦ).continuous
    (LipschitzWith.of_dist_le_mul hΨ).continuous

variable {X E F G : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] in
/-- A density bounded by `M` gives a vector measure of total variation at most `M μ`. -/
lemma cvx_variation_withDensityᵥ_le {μ : Measure X} {f : X → F} (hf : Integrable f μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) : (μ.withDensityᵥ f).variation ≤ (M : ℝ≥0∞) • μ := by
  rw [Measure.variation_withDensityᵥ hf, Measure.le_iff]
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hM] with x hx
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hx

/-- Integration against a vector measure with density with respect to a positive measure:
`∫ g d[B; f μ] = ∫ B(g, f) dμ` for a bounded density `f`. The proof checks indicator functions and
extends by linearity and continuity in `L¹(μ)`. -/
theorem cvx_integral_withDensityᵥ {μ : Measure X} {f : X → F} (hf : Integrable f μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) (B : E →L[ℝ] F →L[ℝ] G) {g : X → E} (hg : Integrable g μ) :
    ∫ᵛ x, g x ∂[B; μ.withDensityᵥ f] = ∫ x, B (g x) (f x) ∂μ := by
  set ν := μ.withDensityᵥ f with hν
  have hvar : ν.variation ≤ (M : ℝ≥0∞) • μ := cvx_variation_withDensityᵥ_le hf hM
  have hac : ν.variation ≪ μ := Measure.absolutelyContinuous_of_le_smul hvar
  have hint : ∀ {g : X → E}, Integrable g μ → ν.Integrable g := fun hg =>
    (hg.smul_measure ENNReal.coe_ne_top).mono_measure hvar
  have hbd : ∀ (g₁ g₂ : X → E), ∀ᵐ x ∂μ,
      ‖B (g₁ x) (f x) - B (g₂ x) (f x)‖ ≤ ‖B‖ * M * ‖g₁ x - g₂ x‖ := by
    intro g₁ g₂
    filter_upwards [hM] with x hx
    rw [← sub_apply, ← map_sub]
    calc ‖B (g₁ x - g₂ x) (f x)‖ ≤ ‖B‖ * ‖g₁ x - g₂ x‖ * ‖f x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖g₁ x - g₂ x‖ * M := by gcongr
      _ = ‖B‖ * M * ‖g₁ x - g₂ x‖ := by ring
  have hint2 : ∀ {g : X → E}, Integrable g μ → Integrable (fun x => B (g x) (f x)) μ := by
    intro g hg
    refine Integrable.mono' (hg.norm.const_mul (‖B‖ * M)) ?_ ?_
    · exact B.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable hf.aestronglyMeasurable
    · filter_upwards [hbd g 0] with x hx
      simpa using hx
  -- induction on `g ∈ L¹(μ)`
  refine hg.induction (P := fun g => ∫ᵛ x, g x ∂[B; ν] = ∫ x, B (g x) (f x) ∂μ) ?_ ?_ ?_ ?_
  · -- indicator functions of sets of finite measure
    intro c s hs hμs
    have : IsFiniteMeasure (ν.variation.restrict s) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (hvar s).trans_lt (by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hμs)⟩
    rw [VectorMeasure.integral_indicator_const _ hs]
    have e : (fun x => B (s.indicator (fun _ => c) x) (f x)) =
        s.indicator (fun x => B c (f x)) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [e, integral_indicator hs, ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
      hν, withDensityᵥ_apply hf hs]
  · -- sums
    intro g₁ g₂ _ hg₁ hg₂ h₁ h₂
    simp only [Pi.add_apply, map_add, add_apply]
    rw [VectorMeasure.integral_fun_add (hint hg₁) (hint hg₂), integral_add (hint2 hg₁) (hint2 hg₂),
      h₁, h₂]
  · -- closedness: both sides are `‖B‖ M`-Lipschitz in `g ∈ L¹(μ)`
    refine cvx_isClosed_eq_of_lipschitz (K := ‖B‖₊ * M)
      (Φ := fun g => ∫ᵛ x, g x ∂[B; ν]) (Ψ := fun g => ∫ x, B (g x) (f x) ∂μ) ?_ ?_
    · intro g₁ g₂
      refine (VectorMeasure.dist_integral_le_lintegral_edist (hint (L1.integrable_coeFn g₁))
        (hint (L1.integrable_coeFn g₂))).trans ?_
      rw [L1.dist_def, NNReal.coe_mul, coe_nnnorm, mul_assoc]
      gcongr
      have hfin : ∫⁻ a, edist (g₁ a) (g₂ a) ∂μ ≠ ∞ := by
        rw [← L1.edist_def]; exact edist_ne_top _ _
      calc (∫⁻ a, edist (g₁ a) (g₂ a) ∂ν.variation).toReal
          ≤ (∫⁻ a, edist (g₁ a) (g₂ a) ∂((M : ℝ≥0∞) • μ)).toReal :=
            ENNReal.toReal_mono (by
              rw [lintegral_smul_measure]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)
              (lintegral_mono' hvar le_rfl)
        _ = M * (∫⁻ a, edist (g₁ a) (g₂ a) ∂μ).toReal := by
            rw [lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    · intro g₁ g₂
      rw [dist_eq_norm, ← integral_sub (hint2 (L1.integrable_coeFn g₁))
        (hint2 (L1.integrable_coeFn g₂)), L1.dist_eq_integral_dist, NNReal.coe_mul, coe_nnnorm,
        ← integral_const_mul]
      have hi : Integrable (fun x => dist (g₁ x) (g₂ x)) μ := by
        simp_rw [dist_eq_norm]
        exact ((L1.integrable_coeFn g₁).sub (L1.integrable_coeFn g₂)).norm
      refine norm_integral_le_of_norm_le (hi.const_mul _) ?_
      · filter_upwards [hbd g₁ g₂] with x hx
        rw [dist_eq_norm]; exact hx
  · -- a.e. equal functions
    intro g₁ g₂ hfg _ h₁
    rw [← VectorMeasure.integral_congr_ae (hac.ae_eq hfg), h₁]
    exact integral_congr_ae (hfg.mono fun x hx => by simp only [hx])

end density

/-- The cross product as a continuous bilinear map, the pairing in `∫ p × dμ`. -/
noncomputable def crossCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => LinearMap.toContinuousLinearMap
        { toFun := fun q => cross p q
          map_add' := fun q r => by simp only [cross, Prod.fst_add, Prod.snd_add]; ring
          map_smul' := fun a q => by
            simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      map_add' := fun p r => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          add_apply, Prod.fst_add, Prod.snd_add]; ring
      map_smul' := fun a p => ContinuousLinearMap.ext fun q => by
        simp only [cross, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          RingHom.id_apply]; ring }

@[simp] lemma crossCLM_apply (p q : ℝ × ℝ) : crossCLM p q = cross p q := rfl

/-- The cross product is antisymmetric. -/
lemma cvx_crossCLM_flip : crossCLM.flip = -crossCLM := by
  refine ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => ?_
  rw [ContinuousLinearMap.flip_apply, neg_apply, neg_apply, crossCLM_apply, crossCLM_apply,
    cross_anticomm]

/-! ### Lemmas 5.1.2 and 5.1.3 for the cross product

The paper applies the scalar Lemmas 5.1.2 and 5.1.3 to cross products of plane curves, coordinate
by coordinate. The integrals against `dx` paired by the cross product split into integrals against
the Lebesgue–Stieltjes measures of the coordinates of `x`. -/

section crossForms

/-- Composing the integrand with a continuous linear map `L` is composing the pairing with `L`
(to take coordinates of the integrands in the cross forms of Lemmas 5.1.2 and 5.1.3). -/
private lemma cvx_integral_comp_left {X E E' F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : VectorMeasure X F}
    (B : E →L[ℝ] F →L[ℝ] ℝ) (L : E' →L[ℝ] E) {f : X → E'} (hf : μ.Integrable f) :
    ∫ᵛ x, L (f x) ∂[B; μ] = ∫ᵛ x, f x ∂[B.comp L; μ] := by
  refine hf.induction (P := fun f => ∫ᵛ x, L (f x) ∂[B; μ] = ∫ᵛ x, f x ∂[B.comp L; μ])
    ?_ ?_ ?_ ?_
  · intro c s hs hμs
    have : IsFiniteMeasure (μ.variation.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
    have e : (fun x => L (s.indicator (fun _ => c) x)) = s.indicator fun _ => L c := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [e, VectorMeasure.integral_indicator_const _ hs, VectorMeasure.integral_indicator_const _ hs]
    rfl
  · intro f g _ hf hg h₁ h₂
    simp only [Pi.add_apply, map_add]
    rw [VectorMeasure.integral_fun_add (L.integrable_comp hf) (L.integrable_comp hg),
      VectorMeasure.integral_fun_add hf hg, h₁, h₂]
  · refine isClosed_eq (((VectorMeasure.continuous_integral (μ := μ) (B := B)).comp
      (L.compLpL 1 μ.variation).continuous).congr fun f => ?_) VectorMeasure.continuous_integral
    exact VectorMeasure.integral_congr_ae (L.coeFn_compLpL f)
  · intro f g hfg _ h
    have hL : (fun x => L (f x)) =ᵐ[μ.variation] fun x => L (g x) := hfg.fun_comp L
    rw [← VectorMeasure.integral_congr_ae hL, h, VectorMeasure.integral_congr_ae hfg]

/-- Two pairing integrals agree when the pairings composed with the vector measures agree (to
take coordinates of the measures in the cross forms of Lemmas 5.1.2 and 5.1.3). -/
private lemma cvx_integral_congr_transpose {X E F F' : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {μ : VectorMeasure X F} {ν : VectorMeasure X F'}
    {B : E →L[ℝ] F →L[ℝ] ℝ} {C : E →L[ℝ] F' →L[ℝ] ℝ}
    (h : ∀ s, MeasurableSet s → ∀ e, B e (μ s) = C e (ν s)) {f : X → E}
    (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, f x ∂[C; ν] := by
  have hT : μ.transpose B = ν.transpose C :=
    VectorMeasure.ext fun s hs => ContinuousLinearMap.ext fun e => by
      simp only [transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply, h s hs e]
  rw [VectorMeasure.integral_eq_setToFun_transpose hμ,
    VectorMeasure.integral_eq_setToFun_transpose hν]
  simp only [hT]

/-- The integral of `y` against `μ = (μ₁, μ₂)` paired by the cross product, in coordinates:
`∫_X y × dμ = ∫_X y₁ dμ₂ - ∫_X y₂ dμ₁` (the coordinate-by-coordinate reading of the cross forms
of Lemmas 5.1.2 and 5.1.3). -/
private lemma cvx_setIntegral_cross_coord {μ : VectorMeasure ℝ (ℝ × ℝ)} {μ₁ μ₂ : VectorMeasure ℝ ℝ}
    (hμ : ∀ s, μ s = (μ₁ s, μ₂ s)) {y : ℝ → ℝ × ℝ} (hy : μ.Integrable y)
    (hy₁ : μ₁.Integrable y) (hy₂ : μ₂.Integrable y) (X : Set ℝ) :
    ∫ᵛ t in X, y t ∂[crossCLM; μ] = ∫ᵛ t in X, (y t).1 ∂• μ₂ - ∫ᵛ t in X, (y t).2 ∂• μ₁ := by
  by_cases hX : MeasurableSet X
  swap
  · simp [VectorMeasure.setIntegral_eq_zero_of_not_measurableSet hX]
  -- `p × q = P(p₁, q) - Q(p₂, q)` with `P(r, q) = r q₂` and `Q(r, q) = r q₁`
  set P : ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) with hP
  set Q : ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) with hQ
  have hc : crossCLM = P.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      Q.comp (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    refine ContinuousLinearMap.ext fun p => ContinuousLinearMap.ext fun q => ?_
    simp [hP, hQ, cross]
  have hyX := hy.restrict (s := X)
  rw [hc, VectorMeasure.integral_sub_cbm hyX,
    ← cvx_integral_comp_left P (ContinuousLinearMap.fst ℝ ℝ ℝ) hyX,
    ← cvx_integral_comp_left Q (ContinuousLinearMap.snd ℝ ℝ ℝ) hyX]
  congr 1
  · refine cvx_integral_congr_transpose (fun s hs e => ?_) hyX.fst hy₂.restrict.fst
    simp [hP, VectorMeasure.restrict_apply _ hX hs, hμ]
  · refine cvx_integral_congr_transpose (fun s hs e => ?_) hyX.snd hy₁.restrict.snd
    simp [hQ, VectorMeasure.restrict_apply _ hX hs, hμ]

/-- A function continuous on `[a, b]` is right-continuous on `[a, b)` (the right-continuity
hypothesis of Lemmas 5.1.2 and 5.1.3 for a continuous curve). -/
lemma cvx_rightCont_of_continuousOn {α : Type*} [TopologicalSpace α] {f : ℝ → α} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : ∀ t ∈ Ico a b, ContinuousWithinAt f (Ici t) t :=
  fun t ht => (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, ht.2, fun _ hs => ⟨ht.1.trans hs.2, hs.1.le⟩⟩)

/-- One-sided limits of a function of bounded variation commute with continuous linear maps (the
coordinates of the left limit in Lemma 5.1.2 for the cross product). -/
private lemma cvx_lim_comp {x : ℝ → ℝ × ℝ} (hx : BoundedVariationOn x univ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ) :
    Function.rightLim (fun s => L (x s)) t = L (Function.rightLim x t) ∧
      Function.leftLim (fun s => L (x s)) t = L (Function.leftLim x t) :=
  ⟨rightLim_eq_of_tendsto ((L.continuous.tendsto _).comp (hx.tendsto_rightLim t)),
    leftLim_eq_of_tendsto ((L.continuous.tendsto _).comp (hx.tendsto_leftLim t))⟩

/-- A coordinate of a curve of bounded variation has bounded variation (to apply Lemmas 5.1.2 and
5.1.3 to the coordinates). -/
private lemma cvx_bv_coord {x : ℝ → ℝ × ℝ} {s : Set ℝ} (hx : BoundedVariationOn x s)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) : BoundedVariationOn (fun t => L (x t)) s :=
  L.lipschitzWith.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) hx

/-- The coordinates of `dx` are the Lebesgue–Stieltjes measures `dx₁, dx₂` of the coordinates of
`x` (to apply Lemmas 5.1.2 and 5.1.3 coordinate by coordinate). -/
private lemma cvx_lsMeasure_coord {x : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : BoundedVariationOn x (Icc a b)) (s : Set ℝ) :
    lsMeasure x a b s =
      (lsMeasure (fun t => (x t).1) a b s, lsMeasure (fun t => (x t).2) a b s) := by
  have hX := boundedVariationOn_clampFun hab hx
  have key : ∀ L : (ℝ × ℝ) →L[ℝ] ℝ,
      lsMeasure (fun t => L (x t)) a b s = L (lsMeasure x a b s) := by
    intro L
    have hL := boundedVariationOn_clampFun hab (cvx_bv_coord hx L)
    have h : hL.vectorMeasure = hX.vectorMeasure.mapRange (L : (ℝ × ℝ) →+ ℝ) L.continuous := by
      apply VectorMeasure.ext_of_Icc
      intro c d hcd
      rw [VectorMeasure.mapRange_apply, hL.vectorMeasure_Icc hcd, hX.vectorMeasure_Icc hcd,
        AddMonoidHom.coe_ofClass, map_sub]
      exact congrArg₂ (· - ·) (cvx_lim_comp hX L d).1 (cvx_lim_comp hX L c).2
    rw [lsMeasure_eq_vectorMeasure hL, lsMeasure_eq_vectorMeasure hX, h,
      VectorMeasure.mapRange_apply, AddMonoidHom.coe_ofClass]
  exact Prod.ext (key (ContinuousLinearMap.fst ℝ ℝ ℝ)).symm
    (key (ContinuousLinearMap.snd ℝ ℝ ℝ)).symm

/-- `∫_X y × dx = ∫_X y₁ dx₂ - ∫_X y₂ dx₁` for `X ⊆ [a, b]` and `x, y` of bounded variation on
`[a, b]`: the cross-product integrals of Lemmas 5.1.2 and 5.1.3 in coordinates. -/
private lemma cvx_setIntegral_cross {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : BoundedVariationOn x (Icc a b)) (hy : BoundedVariationOn y (Icc a b)) {X : Set ℝ}
    (hX : X ⊆ Icc a b) :
    ∫ᵛ t in X, y t ∂[crossCLM; lsMeasure x a b] =
      ∫ᵛ t in X, (y t).1 ∂• lsMeasure (fun t => (x t).2) a b -
        ∫ᵛ t in X, (y t).2 ∂• lsMeasure (fun t => (x t).1) a b := by
  -- replace `y` by its clamp to `[a, b]`, which has bounded variation on `ℝ`
  have hY := boundedVariationOn_clampFun hab hy
  have hXY : EqOn (clampFun y a b) y X := fun t ht => clampFun_of_mem (hX ht)
  rw [← VectorMeasure.setIntegral_congr_fun hXY,
    ← VectorMeasure.setIntegral_congr_fun (f := fun t => (clampFun y a b t).1)
      fun t ht => congrArg Prod.fst (hXY ht),
    ← VectorMeasure.setIntegral_congr_fun (f := fun t => (clampFun y a b t).2)
      fun t ht => congrArg Prod.snd (hXY ht)]
  exact cvx_setIntegral_cross_coord (cvx_lsMeasure_coord hab hx) hY.integrable hY.integrable
    hY.integrable X

/-- **Lemma 5.1.2** (`lem:integration-by-parts`) for the cross product, coordinate by coordinate:
for right-continuous `x, y` of bounded variation on `[a, b]`,
`∫_{(a,b]} dx × y + ∫_{(a,b]} x(t-) × dy = x(b) × y(b) - x(a) × y(a)`. -/
theorem lemma5_1_2_cross {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : BoundedVariationOn x (Icc a b)) (hy : BoundedVariationOn y (Icc a b))
    (hxr : ∀ t ∈ Ico a b, ContinuousWithinAt x (Ici t) t)
    (hyr : ∀ t ∈ Ico a b, ContinuousWithinAt y (Ici t) t) :
    (∫ᵛ t in Ioc a b, y t ∂[crossCLM.flip; lsMeasure x a b]) +
      (∫ᵛ t in Ioc a b, Function.leftLim (clampFun x a b) t ∂[crossCLM; lsMeasure y a b]) =
      cross (x b) (y b) - cross (x a) (y a) := by
  have hX := boundedVariationOn_clampFun hab hx
  -- Lemma 5.1.2 for `x₁, y₂` and for `x₂, y₁`
  have h₁ := lemma5_1_2 hab (cvx_bv_coord hx (ContinuousLinearMap.fst ℝ ℝ ℝ))
    (cvx_bv_coord hy (ContinuousLinearMap.snd ℝ ℝ ℝ)) (fun t ht => (hxr t ht).fst)
    (fun t ht => (hyr t ht).snd)
  have h₂ := lemma5_1_2 hab (cvx_bv_coord hx (ContinuousLinearMap.snd ℝ ℝ ℝ))
    (cvx_bv_coord hy (ContinuousLinearMap.fst ℝ ℝ ℝ)) (fun t ht => (hxr t ht).snd)
    (fun t ht => (hyr t ht).fst)
  -- the coordinates of the left limit of `x` are the left limits of its coordinates
  have hl : ∀ L : (ℝ × ℝ) →L[ℝ] ℝ, (fun t => L (Function.leftLim (clampFun x a b) t)) =
      Function.leftLim (clampFun (fun t => L (x t)) a b) :=
    fun L => funext fun t => ((cvx_lim_comp hX L t).2).symm
  rw [cvx_crossCLM_flip, VectorMeasure.integral_neg_cbm,
    cvx_setIntegral_cross hab hx hy Ioc_subset_Icc_self,
    cvx_setIntegral_cross hab hy (hX.leftLim.mono (subset_univ _)) Ioc_subset_Icc_self]
  have e₁ := hl (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have e₂ := hl (ContinuousLinearMap.snd ℝ ℝ ℝ)
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at e₁ e₂ h₁ h₂
  rw [e₁, e₂]
  simp only [cross]
  linarith

/-- **Lemma 5.1.3** (`lem:lebesgue-stieltjes-product`) for the cross product, coordinate by
coordinate: if one of the right-continuous curves `x, y` of bounded variation is continuous, then
`d(x × y) = dx × y + x × dy` on `[a, b]`; stated on every Borel subset of `[a, b]`. -/
theorem lemma5_1_3_cross {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : BoundedVariationOn x (Icc a b)) (hy : BoundedVariationOn y (Icc a b))
    (hxr : ∀ t ∈ Ico a b, ContinuousWithinAt x (Ici t) t)
    (hyr : ∀ t ∈ Ico a b, ContinuousWithinAt y (Ici t) t)
    (hcont : ContinuousOn x (Icc a b) ∨ ContinuousOn y (Icc a b))
    {X : Set ℝ} (hXab : X ⊆ Icc a b) :
    lsMeasure (fun t => cross (x t) (y t)) a b X =
      (∫ᵛ t in X, y t ∂[crossCLM.flip; lsMeasure x a b]) +
        (∫ᵛ t in X, x t ∂[crossCLM; lsMeasure y a b]) := by
  have hx₁ := cvx_bv_coord hx (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hx₂ := cvx_bv_coord hx (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hy₁ := cvx_bv_coord hy (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hy₂ := cvx_bv_coord hy (ContinuousLinearMap.snd ℝ ℝ ℝ)
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at hx₁ hx₂ hy₁ hy₂
  -- Lemma 5.1.3 for `x₁ y₂` and for `x₂ y₁`
  have h₁ := lemma5_1_3 hab hx₁ hy₂ (fun t ht => (hxr t ht).fst) (fun t ht => (hyr t ht).snd)
    (hcont.imp (fun h => h.fst) fun h => h.snd) hXab
  have h₂ := lemma5_1_3 hab hx₂ hy₁ (fun t ht => (hxr t ht).snd) (fun t ht => (hyr t ht).fst)
    (hcont.imp (fun h => h.snd) fun h => h.fst) hXab
  -- `x × y = x₁ y₂ - x₂ y₁` and Proposition 5.1.1
  have e : (fun t => cross (x t) (y t)) =
      fun t => 1 * ((x t).1 * (y t).2) + (-1) * ((x t).2 * (y t).1) := by
    funext t; simp only [cross]; ring
  have hp₁ : BoundedVariationOn (fun t => (x t).1 * (y t).2) (Icc a b) := hx₁.mul hy₂
  have hp₂ : BoundedVariationOn (fun t => (x t).2 * (y t).1) (Icc a b) := hx₂.mul hy₁
  rw [e, proposition5_1_1 hab hp₁ hp₂, add_apply, smul_apply, smul_apply,
    h₁, h₂, cvx_crossCLM_flip, VectorMeasure.integral_neg_cbm, cvx_setIntegral_cross hab hx hy hXab,
    cvx_setIntegral_cross hab hy hx hXab]
  simp only [smul_eq_mul]
  ring

end crossForms

/-- The space `C^BV[a, b]` of continuous maps of bounded variation `[a, b] → ℝ²`
(Definition 7.2.5, `def:bounded-variation-space`). -/
def IsCBV (x : ℝ → ℝ × ℝ) (a b : ℝ) : Prop :=
  ContinuousOn x (Icc a b) ∧ BoundedVariationOn x (Icc a b)

/-- The bilinear form `𝓑(x₁, x₂) = ½ ∫_a^b x₁(t) × dx₂(t)`. -/
noncomputable def curveBilin (x₁ x₂ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ᵛ t in Icc a b, x₁ t ∂[crossCLM; lsMeasure x₂ a b]

/-- The curve area functional `𝒥(x) = ½ ∫_a^b x(t) × dx(t)` (Definition 7.2.6,
`def:curve-area-functional`). -/
noncomputable def curveArea (x : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ := curveBilin x x a b

/-- `C^BV[a, b]` as a type. -/
abbrev CBV (a b : ℝ) : Type := {x : ℝ → ℝ × ℝ // IsCBV x a b}

/-- `C^BV[a, b]` is closed under linear combinations. -/
theorem isCBV_comb {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hx : IsCBV x a b) (hy : IsCBV y a b) (c : ℝ) :
    IsCBV ((1 - c) • x + c • y) a b :=
  ⟨(hx.1.const_smul (1 - c)).add (hy.1.const_smul c),
    boundedVariationOn_add (cvx_bv_const_smul hx.2 _) (cvx_bv_const_smul hy.2 _)⟩

/-- `C^BV` is stable under concatenation. -/
lemma isCBV_append {Z : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : IsCBV Z a b) (h₂ : IsCBV Z b c) : IsCBV Z a c := by
  refine ⟨?_, ?_⟩
  · rw [← Icc_union_Icc_eq_Icc hab hbc]
    exact h₁.1.union_of_isClosed h₂.1 isClosed_Icc isClosed_Icc
  · have := eVariationOn.Icc_add_Icc Z (s := univ) hab hbc (mem_univ b)
    simp only [univ_inter] at this
    unfold BoundedVariationOn
    rw [← this]
    exact ENNReal.add_ne_top.2 ⟨h₁.2, h₂.2⟩

/-- `C^BV` is stable under restriction. -/
lemma isCBV_mono {Z : ℝ → ℝ × ℝ} {a b a' b' : ℝ} (h : IsCBV Z a b) (ha : a ≤ a')
    (hb : b' ≤ b) : IsCBV Z a' b' :=
  ⟨h.1.mono (Icc_subset_Icc ha hb), h.2.mono (Icc_subset_Icc ha hb)⟩

/-- The Lebesgue–Stieltjes measure is linear in the curve. -/
lemma cvx_lsMeasure_comb {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) (hx : IsCBV x a b)
    (hy : IsCBV y a b) (c : ℝ) :
    lsMeasure ((1 - c) • x + c • y) a b = (1 - c) • lsMeasure x a b + c • lsMeasure y a b := by
  have hz := isCBV_comb hx hy c
  apply VectorMeasure.ext_of_Icc
  intro p q hpq
  rw [cvx_lsMeasure_Icc hab hz.2 hz.1 hpq, add_apply, smul_apply,
    smul_apply, cvx_lsMeasure_Icc hab hx.2 hx.1 hpq,
    cvx_lsMeasure_Icc hab hy.2 hy.1 hpq]
  simp only [clampFun, Pi.add_apply, Pi.smul_apply, smul_sub]
  abel

/-- `C^BV[a, b]` as a convex domain (a real vector space). -/
noncomputable def cbvDomain (a b : ℝ) : ConvexDomain (CBV a b) where
  comb c x y := ⟨(1 - c) • x.1 + c • y.1, isCBV_comb x.2 y.2 c⟩
  embeds := ⟨ℝ → ℝ × ℝ, inferInstance, inferInstance, Subtype.val, Subtype.val_injective,
    fun _ _ _ _ => rfl⟩

/-- `𝓑(x₁, x₂)` is linear in `x₁`. -/
lemma cvx_curveBilin_comb_left {x z : ℝ → ℝ × ℝ} (y : ℝ → ℝ × ℝ) {a b : ℝ}
    (hx : ContinuousOn x (Icc a b)) (hz : ContinuousOn z (Icc a b)) (c : ℝ) :
    curveBilin ((1 - c) • x + c • z) y a b =
      (1 - c) * curveBilin x y a b + c * curveBilin z y a b := by
  have hx' := cvx_integrable_restrict_Icc (lsMeasure y a b) hx
  have hz' := cvx_integrable_restrict_Icc (lsMeasure y a b) hz
  unfold curveBilin
  have e : (fun t => ((1 - c) • x + c • z) t) = fun t => (1 - c) • x t + c • z t := rfl
  have hx'' : ((lsMeasure y a b).restrict (Icc a b)).Integrable (fun t => (1 - c) • x t) :=
    hx'.smul (1 - c)
  have hz'' : ((lsMeasure y a b).restrict (Icc a b)).Integrable (fun t => c • z t) := hz'.smul c
  rw [e, VectorMeasure.integral_fun_add hx'' hz'', VectorMeasure.integral_fun_smul,
    VectorMeasure.integral_fun_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `𝓑(x₁, x₂)` is linear in `x₂`. -/
lemma cvx_curveBilin_comb_right {x y z : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hxc : ContinuousOn x (Icc a b)) (hy : IsCBV y a b) (hz : IsCBV z a b) :
    curveBilin x ((1 - c) • y + c • z) a b =
      (1 - c) * curveBilin x y a b + c * curveBilin x z a b := by
  simp only [curveBilin]
  rw [cvx_lsMeasure_comb hab hy hz c, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
    VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure
      ((cvx_integrable_restrict_Icc _ hxc).smul_vectorMeasure _)
      ((cvx_integrable_restrict_Icc _ hxc).smul_vectorMeasure _),
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **Proposition 7.2.2** (`pro:curve-area-functional-quadratic`). `𝒥` is quadratic on
`C^BV[a, b]`. -/
theorem proposition7_2_2 {a b : ℝ} (hab : a ≤ b) :
    (cbvDomain a b).IsQuadratic (fun x => curveArea x.1 a b) := by
  exact ⟨fun x y => curveBilin x.1 y.1 a b,
    ⟨fun x c _ y z => cvx_curveBilin_comb_right hab x.2.1 y.2 z.2,
      fun y c _ x z => cvx_curveBilin_comb_left y.1 x.2.1 z.2.1 c⟩, fun x => rfl⟩

/-- The curve area functional of a primitive of a bounded integrable function. -/
theorem cvx_curveArea_of_primitive {x ψ : ℝ → ℝ × ℝ} {a b : ℝ} {M : NNReal} (hab : a ≤ b)
    (hψ : IntegrableOn ψ (Icc a b)) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, ψ s) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, cross (x t) (ψ t) := by
  obtain ⟨hbv, hxc⟩ := cvx_bv_of_primitive hab hψ hψM hx
  unfold curveArea curveBilin
  rw [cvx_lsMeasure_eq_withDensityᵥ hab hψ hx hbv hxc,
    cvx_withDensityᵥ_restrict hψ measurableSet_Icc,
    Measure.restrict_restrict_of_subset subset_rfl,
    cvx_integral_withDensityᵥ hψ (ae_restrict_of_forall_mem measurableSet_Icc hψM) crossCLM
      hxc.integrableOn_Icc, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  simp only [crossCLM_apply]

/-- A continuously differentiable function is the primitive of its derivative. -/
lemma cvx_eq_primitive_of_contDiffOn {x : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ContDiffOn ℝ 1 x (Icc a b)) :
    ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, derivWithin x (Icc a b) s := by
  intro t ht
  rcases hab.eq_or_lt with rfl | hab'
  · have : t = a := le_antisymm ht.2 ht.1
    subst this; simp
  have hcont : ContinuousOn (derivWithin x (Icc a b)) (Icc a b) :=
    hx.continuousOn_derivWithin (uniqueDiffOn_Icc hab') le_rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hx.continuousOn.mono
    (Icc_subset_Icc le_rfl ht.2))]
  · abel
  · intro s hs
    have hsab : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hd : DifferentiableAt ℝ x s :=
      ((hx.differentiableOn one_ne_zero) s (Ioo_subset_Icc_self hsab)).differentiableAt
        (Icc_mem_nhds hsab.1 hsab.2)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hsab.1 hsab.2)]
    exact hd.hasDerivAt
  · exact (hcont.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- For a continuously differentiable curve, `𝒥(x) = ½ ∫_a^b x(t) × x'(t) dt`. -/
theorem curveArea_eq_integral {x : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b)
    (hx : ContDiffOn ℝ 1 x (Icc a b)) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, cross (x t) (derivWithin x (Icc a b) t) := by
  rcases hab.eq_or_lt with rfl | hab'
  · obtain ⟨M, hM⟩ : ∃ M : NNReal, ∀ t ∈ Icc a a, ‖derivWithin x (Icc a a) t‖ ≤ M :=
      ⟨‖derivWithin x (Icc a a) a‖₊, fun t ht => by
        rw [show t = a from le_antisymm ht.2 ht.1]; exact le_rfl⟩
    exact cvx_curveArea_of_primitive le_rfl (by simp) hM (cvx_eq_primitive_of_contDiffOn le_rfl hx)
  have hcont : ContinuousOn (derivWithin x (Icc a b)) (Icc a b) :=
    hx.continuousOn_derivWithin (uniqueDiffOn_Icc hab') le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact cvx_curveArea_of_primitive (M := M.toNNReal) hab hcont.integrableOn_Icc
    (fun t ht => (hM t ht).trans (Real.le_coe_toNNReal M)) (cvx_eq_primitive_of_contDiffOn hab hx)

/-- The curve area functional of a segment, `𝒥(p, q) = (p × q)/2` (Definition 7.2.8,
`def:curve-area-line-segment`). -/
noncomputable def segArea (p q : ℝ × ℝ) : ℝ := cross p q / 2

/-- **Proposition 7.2.4** (`pro:curve-area-line-segment`). The curve area functional of the
oriented segment from `p` to `q` is `𝒥(p, q)`. -/
theorem proposition7_2_4 (p q : ℝ × ℝ) :
    curveArea (fun s => p + s • (q - p)) 0 1 = segArea p q := by
  rw [cvx_curveArea_of_primitive (ψ := fun _ => q - p) (M := ‖q - p‖₊) zero_le_one
    (integrableOn_const (by simp)) (fun _ _ => le_rfl)]
  · have : ∀ t : ℝ, cross (p + t • (q - p)) (q - p) = cross p q := by
      intro t; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    simp only [this, intervalIntegral.integral_const, sub_zero, segArea, smul_eq_mul]
    ring
  · intro t _
    simp [smul_sub]

/-- **Proposition 7.2.4** (`pro:curve-area-line-segment`), second claim: if `p ∈ l(t, h)` and
`q - p = d v_t`, then `𝒥(p, q) = hd/2`. -/
theorem proposition7_2_4_line {p q : ℝ × ℝ} {t h d : ℝ} (hp : p ∈ line t h)
    (hd : q - p = d • vvec t) : segArea p q = h * d / 2 := by
  have hq' : q = p + d • vvec t := by rw [← hd]; abel
  simp only [line, Set.mem_ofPred_eq] at hp
  rw [segArea, hq', cross_add_right, cross_self, cross_smul_right, cross_vvec, hp]
  ring

/-- **Proposition 7.2.5** (`pro:curve-area-line-segment-colinear`). If `p`, `q` and the origin lie
on a common line, then `𝒥(p, q) = 0`. -/
theorem proposition7_2_5 {p q : ℝ × ℝ} {t : ℝ} (hp : p ∈ line t 0) (hq : q ∈ line t 0) :
    segArea p q = 0 := by
  refine (proposition7_2_4_line hp (eq_smul_vvec_of_dot_uvec_eq_zero ?_)).trans (by ring)
  simp only [line, Set.mem_ofPred_eq] at hp hq
  rw [dot_sub_left, hp, hq, sub_zero]

/-- **Proposition 7.2.6** (`pro:curve-area-functional-additive`). The curve area functional is
additive under concatenation: `𝒥(x|_{[a,c]}) = 𝒥(x|_{[a,b]}) + 𝒥(x|_{[b,c]})`. -/
theorem proposition7_2_6 {x : ℝ → ℝ × ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hx : IsCBV x a c) : curveArea x a c = curveArea x a b + curveArea x b c := by
  have hac := hab.trans hbc
  unfold curveArea curveBilin
  rw [← Icc_union_Ioc_eq_Icc hab hbc, VectorMeasure.setIntegral_union
    (Set.disjoint_left.2 fun t ht ht' => absurd ht.2 (not_le.2 ht'.1)) measurableSet_Icc
    measurableSet_Ioc
    ((cvx_integrable_restrict_Icc (lsMeasure x a c) (hx.1.mono (Icc_subset_Icc le_rfl hbc))))
    (VectorMeasure.IntegrableOn.mono measurableSet_Icc Ioc_subset_Icc_self
      (cvx_integrable_restrict_Icc (lsMeasure x a c) (hx.1.mono (Icc_subset_Icc hab le_rfl))))]
  rw [VectorMeasure.setIntegral_congr_set (s := Ioc b c) (t := Icc b c) measurableSet_Ioc
    measurableSet_Icc]
  · rw [cvx_lsMeasure_restrict_Icc le_rfl hab hbc hx.2 hx.1,
      cvx_lsMeasure_restrict_Icc hab hbc le_rfl hx.2 hx.1]
    ring
  · refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 Ioc_subset_Icc_self, measure_empty], ?_⟩
    refine measure_mono_null (fun t ht => ?_) (cvx_lsMeasure_variation_singleton hac hx.2 hx.1 b)
    rw [mem_singleton_iff]
    by_contra hne
    exact ht.2 ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hne), ht.1.2⟩

/-- Splitting the curve area functional at two points. -/
lemma curveArea_split_three {Z : ℝ → ℝ × ℝ} {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (h : IsCBV Z a d) :
    curveArea Z a d = curveArea Z a b + curveArea Z b c + curveArea Z c d := by
  rw [proposition7_2_6 hab (hbc.trans hcd) h,
    proposition7_2_6 hbc hcd (isCBV_mono h hab le_rfl), add_assoc]

/-- Splitting the curve area functional at four points. -/
lemma curveArea_split_five {Z : ℝ → ℝ × ℝ} {a b c d e f : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) (hde : d ≤ e) (hef : e ≤ f) (h : IsCBV Z a f) :
    curveArea Z a f = curveArea Z a b + curveArea Z b c + curveArea Z c d + curveArea Z d e
      + curveArea Z e f := by
  have h₁ := isCBV_mono h hab le_rfl
  have h₂ := isCBV_mono h₁ hbc le_rfl
  rw [proposition7_2_6 hab (hbc.trans (hcd.trans (hde.trans hef))) h,
    proposition7_2_6 hbc (hcd.trans (hde.trans hef)) h₁, curveArea_split_three hcd hde hef h₂]
  ring

/-! ### Elementary properties of `𝒥` -/

/-- The curve area functional only depends on the values of the curve on `[a, b]`. -/
lemma curveArea_congr {x y : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn x y (Icc a b)) :
    curveArea x a b = curveArea y a b := by
  unfold curveArea curveBilin lsMeasure
  rw [clampFun_congr hab h]
  congr 1
  exact VectorMeasure.setIntegral_congr_fun h

/-- A curve that is constant on `[a, b]` has zero curve area functional. -/
lemma curveArea_const {x : ℝ → ℝ × ℝ} {a b : ℝ} {P : ℝ × ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, x t = P) : curveArea x a b = 0 := by
  rw [curveArea_congr hab (y := fun _ => P) h, curveArea_eq_integral hab contDiffOn_const]
  simp [cross]

/-- `𝒥(p, q) = -𝒥(q, p)`. -/
lemma segArea_swap (p q : ℝ × ℝ) : segArea p q = -segArea q p := by
  rw [segArea, segArea, cross_anticomm]; ring

/-- `𝒥(p, p) = 0`. -/
lemma segArea_self (p : ℝ × ℝ) : segArea p p = 0 := by
  simp [segArea]

/-- Collinear points: `𝒥(p, q) + 𝒥(q, r) = 𝒥(p, r)`. -/
lemma segArea_add_of_mem_line {p q r : ℝ × ℝ} {t c : ℝ} (hp : p ∈ line t c) (hq : q ∈ line t c)
    (hr : r ∈ line t c) : segArea p q + segArea q r = segArea p r := by
  -- by Proposition 7.2.4, `𝒥(x, y) = c ((y - x) · v_t) / 2` for `x, y ∈ l(t, c)`
  have h : ∀ {x y}, x ∈ line t c → y ∈ line t c → segArea x y = c * dot (y - x) (vvec t) / 2 :=
    fun hx hy => proposition7_2_4_line hx (eq_smul_vvec_of_dot_uvec_eq_zero (by
      simp only [line, Set.mem_ofPred_eq] at hx hy; rw [dot_sub_left, hx, hy, sub_self]))
  rw [h hp hq, h hq hr, h hp hr, dot_sub_left, dot_sub_left, dot_sub_left]
  ring

/-- Two points on the `x`-axis have zero curve area functional. -/
lemma segArea_of_snd_eq_zero {p q : ℝ × ℝ} (hp : p.2 = 0) (hq : q.2 = 0) : segArea p q = 0 := by
  simp only [segArea, cross, hp, hq]; ring

end MovingSofaOptimality
