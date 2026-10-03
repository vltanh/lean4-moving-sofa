module

public import MovingSofaOptimality.Convex.ConvexDomain

/-!
# The curve area functional (§7.2)

Definitions 7.2.4 (`def:plane-cross-product`), 7.2.5 (`def:bounded-variation-space`), 7.2.6
(`def:curve-area-functional`), 7.2.8 (`def:curve-area-line-segment`); Propositions 7.2.2, 7.2.4–7.2.6.

**Not formalized from this section.** The Jordan curve theorem (Theorem 7.2.1, cited), Green's theorem
for rectifiable Jordan curves (Theorem 7.2.3, cited from Apostol), the notions of Jordan arcs and
curves and their orientation (Definitions 7.2.1–7.2.3, 7.2.7, 7.2.9) and Proposition 7.2.7 (the
orientation of a Jordan curve with a boundary segment). The paper uses them to compute the areas of
specific regions (Lemmas 8.2.2–8.2.3, Theorem 8.4.6); the formalization computes those areas directly
(Fubini and changes of variables). The curve area functional is defined for every continuous curve of
bounded variation, as in Definition 7.2.6, and concatenation is splitting the parameter interval.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaOptimality

/-! ### Auxiliary results on Lebesgue–Stieltjes measures and vector-measure integrals -/

section aux

open scoped NNReal ENNReal

lemma cvx_clampFun_eq {α : Type*} (f : ℝ → α) {a b t : ℝ} (ht : t ∈ Icc a b) :
    clampFun f a b t = f t := by
  simp [clampFun, ht.1, ht.2]

lemma cvx_eVariationOn_add_le {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
    (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i ∈ Finset.range n, edist ((f + g) (u (i + 1))) ((f + g) (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
        gcongr with i hi
        exact edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s := by
        gcongr
        · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i _ ↦ u_mem i)
        · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i _ ↦ u_mem i)

lemma cvx_bv_add {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E] {f g : α → E}
    {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩) (cvx_eVariationOn_add_le f g s)

lemma cvx_bv_const_smul {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (c : ℝ) :
    BoundedVariationOn (c • f) s :=
  (lipschitzWith_smul c).lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) hf

variable {E : Type*} [NormedAddCommGroup E]

lemma cvx_bv_clampFun {f : ℝ → E} {a b : ℝ} (hf : BoundedVariationOn f (Icc a b)) :
    BoundedVariationOn (clampFun f a b) univ := by
  rcases le_or_gt a b with hab | hab
  · have hφ : Monotone (fun t : ℝ => max a (min b t)) :=
      fun x y h => max_le_max le_rfl (min_le_min le_rfl h)
    have hmaps : MapsTo (fun t : ℝ => max a (min b t)) univ (Icc a b) :=
      fun t _ => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
    exact ne_top_of_le_ne_top hf
      (eVariationOn.comp_le_of_monotoneOn f _ (hφ.monotoneOn univ) hmaps)
  · have : clampFun f a b = fun _ => f a := by
      funext t; simp [clampFun, (min_le_left b t).trans hab.le]
    rw [this]
    exact (eVariationOn.constant_on (by simp)).trans_lt ENNReal.zero_lt_top |>.ne

lemma cvx_continuous_clampFun {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : Continuous (clampFun f a b) := by
  have hφ : Continuous (fun t : ℝ => max a (min b t)) := by fun_prop
  exact hf.comp_continuous hφ fun t => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

variable [CompleteSpace E]

lemma cvx_lsMeasure_eq {f : ℝ → E} {a b : ℝ} (hf : BoundedVariationOn f (Icc a b)) :
    lsMeasure f a b = (cvx_bv_clampFun hf).vectorMeasure := by
  simp [lsMeasure, cvx_bv_clampFun hf]

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
  have hc := cvx_continuous_clampFun hab hfc
  rw [cvx_lsMeasure_eq hf, BoundedVariationOn.vectorMeasure_Icc _ hcd,
    hc.continuousAt.continuousWithinAt.rightLim_eq, hc.continuousAt.continuousWithinAt.leftLim_eq]

/-- A continuous curve of bounded variation gives no mass to points. -/
lemma cvx_lsMeasure_variation_singleton {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hfc : ContinuousOn f (Icc a b)) (t : ℝ) :
    (lsMeasure f a b).variation {t} = 0 := by
  have hc := cvx_continuous_clampFun hab hfc
  rw [cvx_lsMeasure_eq hf, BoundedVariationOn.variation_vectorMeasure_singleton,
    hc.continuousAt.continuousWithinAt.rightLim_eq, hc.continuousAt.continuousWithinAt.leftLim_eq]
  simp

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
      cvx_clampFun_eq f h1, cvx_clampFun_eq f h2, cvx_clampFun_eq f (hsub h1),
      cvx_clampFun_eq f (hsub h2)]
  · rw [Icc_eq_empty (not_le.2 h)]; simp

omit [CompleteSpace E] in
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

/-- The Lebesgue–Stieltjes measure of a primitive. -/
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
  have hp' : max a (min b p) ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hq' : max a (min b q) ∈ Icc a b := ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have key : clampFun x a b q - clampFun x a b p =
      ∫ t in (max a (min b p))..(max a (min b q)), ψ t := by
    simp only [clampFun]
    rw [hx _ hq', hx _ hp', add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hi _ hq') (hi _ hp')]
  have hpq' : max a (min b p) ≤ max a (min b q) := max_le_max le_rfl (min_le_min le_rfl hpq)
  rw [key, intervalIntegral.integral_of_le hpq', ← integral_Icc_eq_integral_Ioc]
  rcases le_or_gt (max p a) (min q b) with h | h
  · have e1 : max a (min b p) = max p a := by
      rw [min_eq_right (le_trans (le_max_left p a) (h.trans (min_le_right q b))), max_comm]
    have e2 : max a (min b q) = min q b := by
      rw [min_comm, max_eq_right ((le_max_right p a).trans h)]
    rw [e1, e2]
  · rw [Icc_eq_empty (not_le.2 h), Measure.restrict_empty, integral_zero_measure]
    have e : max a (min b p) = max a (min b q) := by
      rcases lt_or_ge q a with hq | hq
      · rw [max_eq_left ((min_le_right b q).trans hq.le),
          max_eq_left ((min_le_right b p).trans (hpq.trans hq.le))]
      · have hbq : b < q := by
          by_contra hcon
          push Not at hcon
          rw [min_eq_left hcon] at h
          exact absurd h (not_lt.2 (max_le hpq hq))
        have hbp : b < p := by
          by_contra hcon
          push Not at hcon
          rw [min_eq_right hbq.le] at h
          rcases le_total p a with hpa | hpa
          · rw [max_eq_right hpa] at h; linarith
          · rw [max_eq_left hpa] at h; linarith
        rw [min_eq_left hbp.le, min_eq_left hbq.le]
    rw [e, Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure]

omit [CompleteSpace E] in
lemma cvx_withDensityᵥ_restrict_self [NormedSpace ℝ E] {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {s : Set X} (hs : MeasurableSet s) {f : X → E}
    (hf : Integrable f (μ.restrict s)) :
    ((μ.restrict s).withDensityᵥ f).restrict s = (μ.restrict s).withDensityᵥ f := by
  ext t ht
  rw [VectorMeasure.restrict_apply _ hs ht, withDensityᵥ_apply hf (ht.inter hs),
    withDensityᵥ_apply hf ht, Measure.restrict_restrict (ht.inter hs), Measure.restrict_restrict ht,
    inter_assoc, inter_self]

end aux

section density

open scoped NNReal ENNReal

/-- A property of `L¹` functions stating the equality of two Lipschitz functionals is closed. -/
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
lemma cvx_variation_withDensityᵥ_le {μ : Measure X} {f : X → F} (hf : Integrable f μ) {M : ℝ≥0}
    (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) : (μ.withDensityᵥ f).variation ≤ (M : ℝ≥0∞) • μ := by
  rw [Measure.variation_withDensityᵥ hf, Measure.le_iff]
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hM] with x hx
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hx

/-- Integration against a vector measure with density with respect to a positive measure. -/
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
  refine hg.induction (P := fun g => ∫ᵛ x, g x ∂[B; ν] = ∫ x, B (g x) (f x) ∂μ) ?_ ?_ ?_ ?_
  · intro c s hs hμs
    have : IsFiniteMeasure (ν.variation.restrict s) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (hvar s).trans_lt (by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hμs)⟩
    rw [VectorMeasure.integral_indicator_const _ hs]
    have e : (fun x => B (s.indicator (fun _ => c) x) (f x)) = s.indicator (fun x => B c (f x)) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [e, integral_indicator hs, ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
      hν, withDensityᵥ_apply hf hs]
  · intro g₁ g₂ _ hg₁ hg₂ h₁ h₂
    simp only [Pi.add_apply, map_add, add_apply]
    rw [VectorMeasure.integral_fun_add (hint hg₁) (hint hg₂), integral_add (hint2 hg₁) (hint2 hg₂),
      h₁, h₂]
  · refine cvx_isClosed_eq_of_lipschitz (K := ‖B‖₊ * M)
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
  · intro g₁ g₂ hfg _ h₁
    rw [← VectorMeasure.integral_congr_ae (hac.ae_eq hfg), h₁]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

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
    cvx_bv_add (cvx_bv_const_smul hx.2 _) (cvx_bv_const_smul hy.2 _)⟩

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

/-- **Proposition 7.2.2** (`pro:curve-area-functional-quadratic`). `𝒥` is quadratic on `C^BV[a, b]`. -/
theorem proposition7_2_2 {a b : ℝ} (hab : a ≤ b) :
    (cbvDomain a b).IsQuadratic (fun x => curveArea x.1 a b) := by
  refine ⟨fun x y => curveBilin x.1 y.1 a b, ⟨?_, ?_⟩, fun x => rfl⟩
  · intro x c _ y z
    show curveBilin x.1 ((1 - c) • y.1 + c • z.1) a b =
      (1 - c) * curveBilin x.1 y.1 a b + c * curveBilin x.1 z.1 a b
    simp only [curveBilin]
    rw [cvx_lsMeasure_comb hab y.2 z.2 c, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure,
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
      smul_eq_mul, smul_eq_mul]
    · ring
    · exact (cvx_integrable_restrict_Icc _ x.2.1).smul_vectorMeasure _
    · exact (cvx_integrable_restrict_Icc _ x.2.1).smul_vectorMeasure _
  · intro y c _ x z
    exact cvx_curveBilin_comb_left y.1 x.2.1 z.2.1 c

/-- The curve area functional of a primitive of a bounded integrable function. -/
theorem cvx_curveArea_of_primitive {x ψ : ℝ → ℝ × ℝ} {a b : ℝ} {M : NNReal} (hab : a ≤ b)
    (hψ : IntegrableOn ψ (Icc a b)) (hψM : ∀ t ∈ Icc a b, ‖ψ t‖ ≤ M)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, ψ s) :
    curveArea x a b = (1 / 2) * ∫ t in a..b, cross (x t) (ψ t) := by
  have hlip := cvx_lipschitzOnWith_of_primitive hψ hψM hx
  have hbv : BoundedVariationOn x (Icc a b) := by
    have := hlip.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rwa [inter_self] at this
  have hxc := hlip.continuousOn
  unfold curveArea curveBilin
  rw [cvx_lsMeasure_eq_withDensityᵥ hab hψ hx hbv hxc,
    cvx_withDensityᵥ_restrict_self measurableSet_Icc hψ,
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

/-- **Proposition 7.2.4** (`pro:curve-area-line-segment`). The curve area functional of the oriented
segment from `p` to `q` is `𝒥(p, q)`; if `p, q ∈ l(t, h)` and `q - p = d v_t` then `𝒥(p, q) = hd/2`. -/
theorem proposition7_2_4 (p q : ℝ × ℝ) : curveArea (fun s => p + s • (q - p)) 0 1 = segArea p q := by
  rw [cvx_curveArea_of_primitive (ψ := fun _ => q - p) (M := ‖q - p‖₊) zero_le_one
    (integrableOn_const (by simp)) (fun _ _ => le_rfl)]
  · have : ∀ t : ℝ, cross (p + t • (q - p)) (q - p) = cross p q := by
      intro t; simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    simp only [this, intervalIntegral.integral_const, sub_zero, segArea, smul_eq_mul]
    ring
  · intro t _
    simp [smul_sub]

theorem proposition7_2_4_line {p q : ℝ × ℝ} {t h d : ℝ} (hp : p ∈ line t h)
    (hd : q - p = d • vvec t) : segArea p q = h * d / 2 := by
  have hq' : q = p + d • vvec t := by rw [← hd]; abel
  simp only [line, Set.mem_ofPred_eq] at hp
  rw [segArea, hq', cross_add_right, cross_self, cross_smul_right, cross_vvec, hp]
  ring

/-- **Proposition 7.2.5** (`pro:curve-area-line-segment-colinear`). If `p`, `q` and the origin lie on
a common line, then `𝒥(p, q) = 0`. -/
theorem proposition7_2_5 {p q : ℝ × ℝ} {t : ℝ} (hp : p ∈ line t 0) (hq : q ∈ line t 0) :
    segArea p q = 0 := by
  have hd : q - p = dot (q - p) (vvec t) • vvec t := by
    have h0 : dot (q - p) (uvec t) = 0 := by
      simp only [line, Set.mem_ofPred_eq] at hp hq
      rw [dot_sub_left, hp, hq, sub_zero]
    conv_lhs => rw [eq_dot_uvec_smul_add (q - p) t, h0, zero_smul, zero_add]
  rw [proposition7_2_4_line hp hd]
  ring

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

end MovingSofaOptimality
