module

public import MovingSofaOptimality.Injectivity.LimitIneq
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Bounding the arm lengths (§6.5); Theorem 6.1.1 and Theorem 1.7.1

Theorem 6.5.1 (`thm:leg-length-bounds`), Definitions 6.5.1–6.5.3, Lemmas 6.5.2–6.5.5, Theorem 6.5.6
(`thm:lower-bound-one`), Theorem 6.1.1 (`thm:injectivity`) and Theorem 1.7.1
(`thm:injectivity-abridged`).

**Reading of Lemma 6.5.5.** The paper states `f_11 > 1` on `(0, 1]`; its proof shows it on
`(0, π/2]`, which Theorem 6.5.6 needs. We state it on `(0, π/2]`. Lemma 6.5.4 is stated for continuous
functions, the domain of the operator `𝓕` (Definition 6.5.1).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace MovingSofaOptimality

/-! ### Arm lengths of balanced maximum caps -/

/-- `f_K(0) = 1`: the vertex `A_K(0) = A_K⁻(0)` is the corner `(h_K(0), 0)`. -/
lemma inj_fK_zero {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) : fK K 0 = 1 := by
  rw [fK, inj_fMinus_eq, (inj_cap_consecutive hK).1, zero_add, hK.2.2.2.1]
  simp [dot, vvec]

lemma inj_intervalIntegrable_m0_gK {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (fun u => m0 (gK K u)) volume a b :=
  (inj_intervalIntegrable_gPlus hK a b).sub (inj_intervalIntegrable_k0_gPlus hK a b)

/-- `σ_K((a, b]) ≤ ∫_a^b k₀(g_K)` for a balanced maximum cap and `0 ≤ a ≤ b < π/2`. -/
lemma inj_sigma_Ioc_le {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π / 2) :
    (sigma K (Ioc a b)).toReal ≤ ∫ u in a..b, k0 (gPlus K u) := by
  have hKc : IsConvexBody K := hK.2.1.2.1
  have hsub : Ioc a b ⊆ Ico 0 (π / 2) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := Measure.le_iff'.1 (theorem6_4_3 hK) (Ioc a b)
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 hsub,
    withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 hsub, ← ofReal_integral_eq_lintegral_ofReal
      (inj_intervalIntegrable_k0_gPlus hKc a b).1
      (Filter.Eventually.of_forall fun t => inj_k0_nonneg _), ← intervalIntegral.integral_of_le hab]
    at h
  exact ENNReal.toReal_le_of_le_ofReal
    (intervalIntegral.integral_nonneg hab fun t _ => inj_k0_nonneg _) h

/-- The integrated form of Theorem 6.5.1: `f_K(t) - f_K(0) ≥ ∫₀ᵗ m₀(g_K)` on `[0, π/2)`. -/
lemma inj_fK_sub_ge {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2)) : ∫ u in (0 : ℝ)..t, m0 (gK K u) ≤ fK K t - fK K 0 := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have hKc : IsConvexBody K := hcap.2.1
  have h1 := corollary6_4_4 hK
  have h5 := (proposition6_4_5 hcap h1).1
  rw [fK, fK, ← (h5 t ht).2, ← (h5 0 ⟨le_rfl, by positivity⟩).2,
    fPlus_sub_fPlus hKc ht.1]
  have hσ := inj_sigma_Ioc_le hK le_rfl ht.1 ht.2
  have e : ∫ u in (0 : ℝ)..t, m0 (gK K u) =
      (∫ u in (0 : ℝ)..t, gPlus K u) - ∫ u in (0 : ℝ)..t, k0 (gPlus K u) := by
    simp only [m0, gK]
    exact intervalIntegral.integral_sub (inj_intervalIntegrable_gPlus hKc 0 t)
      (inj_intervalIntegrable_k0_gPlus hKc 0 t)
  linarith

/-- `g_K(t) = f_{K^m}(π/2 - t)` for `t ∈ (0, π/2]`. -/
lemma inj_gK_eq_fK_mirror {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht : t ∈ Ioc 0 (π / 2)) : gK K t = fK (mirrorCap K (π / 2)) (π / 2 - t) := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have hm := proposition3_5_1 hK
  have h1 := corollary6_4_4 hK
  have h1m := corollary6_4_4 hm
  have hs : π / 2 - t ∈ Ico 0 (π / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [gK, ((proposition6_4_5 hcap h1).2 t ht).2, fK,
    ← ((proposition6_4_5 hm.2.1 h1m).1 _ hs).2, (proposition6_2_2 (K := K)).1,
    sub_sub_cancel]

/-- **Theorem 6.5.1** (`thm:leg-length-bounds`). For a balanced maximum cap, `f_K` is absolutely
continuous on `[0, π/2]` and `f_K'(t) ≥ m₀(g_K(t))` for almost every `t`. -/
theorem theorem6_5_1 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    AbsolutelyContinuousOnInterval (fK K) 0 (π / 2) ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 (π / 2))), m0 (gK K t) ≤ deriv (fK K) t := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have hKc : IsConvexBody K := hcap.2.1
  have h1 := corollary6_4_4 hK
  have h5 := (proposition6_4_5 hcap h1).1
  obtain ⟨r, -, hrm, -, hr0, -, hr, -⟩ := id h1
  have hπ : (0 : ℝ) < π / 2 := by positivity
  -- `r ≤ k₀(g_K)` almost everywhere on `[0, π/2)`
  have hrk : ∀ᵐ t ∂(volume.restrict (Ico 0 (π / 2))), r t ≤ k0 (gPlus K t) := by
    have hle := theorem6_4_3 hK
    rw [hr] at hle
    have := ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (μ := volume.restrict (Ico 0 (π / 2))) (f := fun t => ENNReal.ofReal (r t))
      (g := fun t => ENNReal.ofReal (k0 (gPlus K t))) hrm.ennreal_ofReal
      (fun s hs _ => by
        rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
        exact Measure.le_iff'.1 hle s)
    filter_upwards [this] with t ht
    exact (ENNReal.ofReal_le_ofReal_iff (inj_k0_nonneg _)).1 ht
  -- `r` is integrable on `[0, π/2)`
  have hfin : (sigma K) (Ico 0 (π / 2)) < ⊤ := measure_Ico_lt_top
  have hrint : IntegrableOn r (Ico 0 (π / 2)) volume := by
    refine ⟨hrm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hr0)]
    have e := congrArg (fun μ : Measure ℝ => μ univ) hr
    simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at e
    rw [← e]; exact hfin
  have hrint' : IntervalIntegrable r volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le]
    exact hrint.congr_set_ae Ico_ae_eq_Ioc.symm
  -- `σ_K((0, t)) = ∫₀ᵗ r`
  have hσIoo : ∀ t ∈ Icc (0 : ℝ) (π / 2), (sigma K (Ioo 0 t)).toReal = ∫ u in (0 : ℝ)..t, r u := by
    intro t ht
    have hsub : Ioo 0 t ⊆ Ico 0 (π / 2) := fun x hx => ⟨hx.1.le, lt_of_lt_of_le hx.2 ht.2⟩
    have e := congrArg (fun μ : Measure ℝ => μ (Ioo 0 t)) hr
    simp only [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 hsub,
      withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo] at e
    rw [e, ← ofReal_integral_eq_lintegral_ofReal (hrint.mono_set hsub)
      (Filter.Eventually.of_forall hr0), ENNReal.toReal_ofReal (integral_nonneg hr0),
      intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
  -- the integrated form
  set φ : ℝ → ℝ := fun u => gK K u - r u with hφ
  have hgint : IntervalIntegrable (gK K) volume 0 (π / 2) := inj_intervalIntegrable_gPlus hKc 0 _
  have hφint : IntervalIntegrable φ volume 0 (π / 2) := hgint.sub hrint'
  have hFTC : ∀ t ∈ Icc (0 : ℝ) (π / 2), fK K t = fK K 0 + ∫ u in (0 : ℝ)..t, φ u := by
    intro t ht
    have hgt : IntervalIntegrable (gK K) volume 0 t := hgint.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hπ.le]; exact Icc_subset_Icc le_rfl ht.2)
    have hrt : IntervalIntegrable r volume 0 t := hrint'.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hπ.le]; exact Icc_subset_Icc le_rfl ht.2)
    rw [intervalIntegral.integral_sub hgt hrt, ← hσIoo t ht]
    have hf0 : fK K 0 = fPlus K 0 := (h5 0 ⟨le_rfl, hπ⟩).2.symm
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0; simp
    have hIoc : Ioc 0 t = Ioo 0 t ∪ {t} := by
      ext x; simp only [mem_Ioc, mem_union, mem_Ioo, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; rcases eq_or_lt_of_le h2 with h | h
        · right; exact h
        · left; exact ⟨h1, h⟩
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨h1, h2.le⟩
        · rw [h]; exact ⟨h0, le_rfl⟩
    have hσIoc : (sigma K (Ioc 0 t)).toReal = (sigma K (Ioo 0 t)).toReal + sigmaAt K t := by
      rw [hIoc, measure_union (by simp) (measurableSet_singleton t),
        ENNReal.toReal_add measure_Ioo_lt_top.ne (by rw [← Icc_self]; exact measure_Icc_lt_top.ne),
        sigmaAt]
    have hFP := fPlus_sub_fPlus hKc h0.le
    rcases eq_or_lt_of_le ht.2 with hπt | hπt
    · -- `t = π/2`: `f_K(π/2) = f_K⁻(π/2) = f_K⁺(π/2) + σ_K(π/2)`
      have hfm : fK K t = fPlus K t + sigmaAt K t := by
        rw [fK, inj_fMinus_eq, inj_fPlus_eq, inj_sigmaAt_eq_dot hKc, dot_sub_left]; ring
      rw [hfm, hf0]
      simp only [gK] at *
      linarith
    · -- `t < π/2`: no atom at `t`
      have hσt : sigmaAt K t = 0 := by
        rw [sigmaAt, inj_sigma_singleton_of_injCond1 h1 (Or.inl ⟨ht.1, hπt⟩), ENNReal.toReal_zero]
      have hft : fK K t = fPlus K t := (h5 t ⟨ht.1, hπt⟩).2.symm
      rw [hft, hf0]
      simp only [gK] at *
      linarith
  -- absolute continuity
  have hAC0 :
      AbsolutelyContinuousOnInterval (fun t => fK K 0 + ∫ u in (0 : ℝ)..t, φ u) 0 (π / 2) := by
    have h0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => fK K 0) 0 (π / 2) :=
      (LipschitzWith.const (fK K 0)).lipschitzOnWith.absolutelyContinuousOnInterval
    have h2 := hφint.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    exact h0.add h2
  refine ⟨hAC0.congr (fun t ht => (hFTC t (by rwa [uIcc_of_le hπ.le] at ht)).symm), ?_⟩
  -- the derivative
  have hd := hφint.ae_hasDerivAt_integral
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneπ : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ π / 2 := by simp [ae_iff, measure_singleton]
  have hrk' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ico 0 (π / 2) → r t ≤ k0 (gPlus K t) :=
    (ae_restrict_iff' measurableSet_Ico).1 hrk
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hd, hne0, hneπ, hrk'] with t hdt ht0 htπ hrt htI
  have htI' : t ∈ Ioo 0 (π / 2) := ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htπ⟩
  have hmem : t ∈ uIcc 0 (π / 2) := by rw [uIcc_of_le hπ.le]; exact htI
  have hD : HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, φ u) (φ t) t := hdt hmem 0 left_mem_uIcc
  have hD' : HasDerivAt (fK K) (φ t) t := by
    have := hD.const_add (fK K 0)
    apply this.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds htI'.1 htI'.2] with x hx
    exact hFTC x ⟨hx.1.le, hx.2.le⟩
  rw [hD'.deriv]
  have := hrt ⟨htI.1, htI'.2⟩
  simp only [hφ, m0, gK]
  linarith

/-- The operator `𝓕 f(x) = 1 + ∫_0^x m₀(f(π/2 - u)) du` (Definition 6.5.1, `def:integral-operator`). -/
noncomputable def lowerOp (f : ℝ → ℝ) (x : ℝ) : ℝ := 1 + ∫ u in (0 : ℝ)..x, m0 (f (π / 2 - u))

/-- The lower bounds `f_0 = 0`, `f_{n+1} = max(f_n, 𝓕 f_n)` (Definition 6.5.2, `def:lower-bound-sequence`). -/
noncomputable def lowerSeq : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (lowerSeq n x) (lowerOp (lowerSeq n) x)

/-! ### The function `m₀` and the operator `𝓕` -/

lemma inj_continuous_m0 : Continuous m0 := by
  unfold m0; exact continuous_id.sub inj_continuous_k0

lemma inj_m0_mono : Monotone m0 := by
  intro x y hxy
  have h := inj_k0_lipschitz x y
  have e : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 hxy)
  rw [e] at h
  unfold m0
  linarith [(abs_le.1 h).1]

lemma inj_m0_of_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : m0 y = 3 * y / 2 - 1 := by
  unfold m0 k0
  rw [abs_of_nonpos (by linarith : y - 1 ≤ 0), max_eq_right (by linarith)]
  ring

lemma inj_continuous_lowerOp {f : ℝ → ℝ} (hf : Continuous f) : Continuous (lowerOp f) := by
  unfold lowerOp
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => (inj_continuous_m0.comp
      (hf.comp (continuous_const.sub continuous_id))).intervalIntegrable a b) 0)

lemma inj_continuous_lowerSeq (n : ℕ) : Continuous (lowerSeq n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    show Continuous fun x => max (lowerSeq n x) (lowerOp (lowerSeq n) x)
    exact ih.max (inj_continuous_lowerOp ih)

/-- **Lemma 6.5.2** (`lem:lower-bound-sequence`). Every balanced maximum cap satisfies
`f_K(t) ≥ f_n(t)` on `[0, π/2)` and `g_K(t) ≥ f_n(π/2 - t)` on `(0, π/2]`. -/
theorem lemma6_5_2 (n : ℕ) {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (∀ t ∈ Ico 0 (π / 2), lowerSeq n t ≤ fK K t) ∧
      ∀ t ∈ Ioc 0 (π / 2), lowerSeq n (π / 2 - t) ≤ gK K t := by
  have key : ∀ n : ℕ, ∀ K, IsBalancedMaxCap K (π / 2) →
      ∀ t ∈ Ico 0 (π / 2), lowerSeq n t ≤ fK K t := by
    intro n
    induction n with
    | zero =>
      intro K hK t _
      exact (inj_arm_nonneg hK.2.1.2.1 t).2.1
    | succ n ih =>
      intro K hK t ht
      have hKc : IsConvexBody K := hK.2.1.2.1
      have hgn : ∀ u ∈ Ioc 0 (π / 2), lowerSeq n (π / 2 - u) ≤ gK K u := by
        intro u hu
        rw [inj_gK_eq_fK_mirror hK hu]
        exact ih _ (proposition3_5_1 hK) _ ⟨by linarith [hu.2], by linarith [hu.1]⟩
      apply max_le (ih K hK t ht)
      have hF := inj_fK_sub_ge hK ht
      rw [inj_fK_zero hK.2.1] at hF
      have hmono : ∫ u in (0 : ℝ)..t, m0 (lowerSeq n (π / 2 - u)) ≤
          ∫ u in (0 : ℝ)..t, m0 (gK K u) :=
        intervalIntegral.integral_mono_on_of_le_Ioo ht.1
          ((inj_continuous_m0.comp ((inj_continuous_lowerSeq n).comp
            (continuous_const.sub continuous_id))).intervalIntegrable _ _)
          (inj_intervalIntegrable_m0_gK hKc _ _)
          (fun u hu => inj_m0_mono (hgn u ⟨hu.1, by linarith [hu.2, ht.2]⟩))
      show 1 + (∫ u in (0 : ℝ)..t, m0 (lowerSeq n (π / 2 - u))) ≤ fK K t
      linarith
  refine ⟨key n K hK, fun t ht => ?_⟩
  rw [inj_gK_eq_fK_mirror hK ht]
  exact key n _ (proposition3_5_1 hK) _ ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- `j_c(x) = max(1 - x, c)` (Definition 6.5.3, `def:lower-bound-j`). -/
noncomputable def jFun (c x : ℝ) : ℝ := max (1 - x) c

/-- **Lemma 6.5.3** (`lem:lower-bound-j-iter`). With `d₀ = 1/12`, for `c ∈ [0, 2/3]`,
`𝓕 j_c(x) ≥ j_{c + d₀}(x)` on `[0, π/2]`. -/
theorem lemma6_5_3 {c : ℝ} (hc : c ∈ Icc 0 (2 / 3)) {x : ℝ} (hx : x ∈ Icc 0 (π / 2)) :
    jFun (c + 1 / 12) x ≤ lowerOp (jFun c) x := by
  obtain ⟨hc0, hc1⟩ := hc
  obtain ⟨hx0, hx1⟩ := hx
  have hπ1 := pi_gt_d2
  have hπ2 := pi_lt_d2
  set h : ℝ → ℝ := fun u => m0 (jFun c (π / 2 - u)) with hh
  have hjc : Continuous (jFun c) := by unfold jFun; fun_prop
  have hhc : Continuous h := inj_continuous_m0.comp (hjc.comp (continuous_const.sub continuous_id))
  have hhval : ∀ u ∈ Icc (0 : ℝ) (π / 2), h u = 3 * max (u + 1 - π / 2) c / 2 - 1 := by
    intro u hu
    simp only [hh, jFun]
    rw [show 1 - (π / 2 - u) = u + 1 - π / 2 by ring]
    apply inj_m0_of_mem (le_trans hc0 (le_max_right _ _))
    exact max_le (by linarith [hu.2]) (by linarith)
  have hlow1 : ∀ u ∈ Icc (0 : ℝ) (π / 2), 3 * c / 2 - 1 ≤ h u := by
    intro u hu; rw [hhval u hu]; linarith [le_max_right (u + 1 - π / 2) c]
  have hlow2 : ∀ u ∈ Icc (0 : ℝ) (π / 2), 3 * (u + 1 - π / 2) / 2 - 1 ≤ h u := by
    intro u hu; rw [hhval u hu]; linarith [le_max_left (u + 1 - π / 2) c]
  have hint : ∀ a b, IntervalIntegrable h volume a b := fun a b => hhc.intervalIntegrable a b
  have hop : lowerOp (jFun c) x = 1 + ∫ u in (0 : ℝ)..x, h u := rfl
  -- the integral is at least `(3c/2 - 1) y` on `[0, y]`
  have hI1 : ∀ y ∈ Icc (0 : ℝ) (π / 2), (3 * c / 2 - 1) * y ≤ ∫ u in (0 : ℝ)..y, h u := by
    intro y hy
    have := intervalIntegral.integral_mono_on (μ := volume) hy.1 intervalIntegrable_const (hint 0 y)
      (fun u hu => hlow1 u ⟨hu.1, hu.2.trans hy.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  rw [hop]
  apply max_le
  · -- `1 - x ≤ 𝓕 j_c(x)`
    have := hI1 x ⟨hx0, hx1⟩
    nlinarith
  · set x₀ := π / 2 - 1 + c with hx₀
    rcases le_total x x₀ with hxx | hxx
    · have := hI1 x ⟨hx0, hx1⟩
      have hmul : (1 - 3 / 2 * c) * x ≤ (1 - 3 / 2 * c) * x₀ :=
        mul_le_mul_of_nonneg_left hxx (by linarith)
      nlinarith [sq_nonneg (c - (7 / 6 - π / 4))]
    · have hx₀0 : 0 ≤ x₀ := by rw [hx₀]; linarith
      have h1 := hI1 x₀ ⟨hx₀0, by linarith⟩
      have hpc : Continuous fun u : ℝ => 3 * (u + 1 - π / 2) / 2 - 1 := by fun_prop
      have h2 : ∫ u in x₀..x, (3 * (u + 1 - π / 2) / 2 - 1) ≤ ∫ u in x₀..x, h u :=
        intervalIntegral.integral_mono_on hxx (hpc.intervalIntegrable _ _) (hint _ _)
          (fun u hu => hlow2 u ⟨hx₀0.trans hu.1, hu.2.trans hx1⟩)
      have h3 : ∫ u in x₀..x, (3 * (u + 1 - π / 2) / 2 - 1) =
          (3 / 4 * (x + 1 - π / 2) ^ 2 - x) - (3 / 4 * (x₀ + 1 - π / 2) ^ 2 - x₀) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro u _
          have h1 : HasDerivAt (fun v : ℝ => v + 1 - π / 2) 1 u :=
            ((hasDerivAt_id' u).add_const 1).sub_const (π / 2)
          have h3 := ((h1.pow 2).const_mul (3 / 4)).sub (hasDerivAt_id' u)
          convert h3 using 1
          push_cast; ring
        · exact hpc.intervalIntegrable _ _
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 x₀) (hint x₀ x)]
      rw [h3] at h2
      have hx₀c : x₀ + 1 - π / 2 = c := by rw [hx₀]; ring
      rw [hx₀c] at h2
      have hfinal : c + 1 / 12 ≤ 1 + ((3 * c / 2 - 1) * x₀ +
          (3 / 4 * (x + 1 - π / 2) ^ 2 - x - (3 / 4 * c ^ 2 - x₀))) := by
        rw [hx₀]
        nlinarith [sq_nonneg (x + 1 - π / 2 - 2 / 3), sq_nonneg (c - (5 / 3 - π / 2))]
      linarith

/-- **Lemma 6.5.4** (`lem:operator-monotonicity`). `𝓕` is monotone on continuous functions on
`[0, π/2]`; the paper also asks them to be nonnegative, which is not needed. -/
theorem lemma6_5_4 {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (π / 2)))
    (hg : ContinuousOn g (Icc 0 (π / 2)))
    (hfg : ∀ x ∈ Icc 0 (π / 2), f x ≤ g x) : ∀ x ∈ Icc 0 (π / 2), lowerOp f x ≤ lowerOp g x := by
  intro x hx
  have hmaps : MapsTo (fun u : ℝ => π / 2 - u) (uIcc 0 x) (Icc 0 (π / 2)) := by
    intro u hu
    rw [uIcc_of_le hx.1] at hu
    exact ⟨by linarith [hu.2, hx.2], by linarith [hu.1]⟩
  have hcont : ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc 0 (π / 2)) →
      IntervalIntegrable (fun u => m0 (φ (π / 2 - u))) volume 0 x := by
    intro φ hφ
    apply ContinuousOn.intervalIntegrable
    exact inj_continuous_m0.comp_continuousOn
      (hφ.comp (continuous_const.sub continuous_id).continuousOn hmaps)
  unfold lowerOp
  have := intervalIntegral.integral_mono_on hx.1 (hcont f hf) (hcont g hg) (fun u hu =>
    inj_m0_mono (hfg _ ⟨by linarith [hu.2, hx.2], by linarith [hu.1]⟩))
  linarith

/-- **Lemma 6.5.5** (`lem:lower-bound-threshold`), on `(0, π/2]` (see the module docstring). -/
theorem lemma6_5_5 {x : ℝ} (hx : x ∈ Ioc 0 (π / 2)) : 1 < lowerSeq 11 x := by
  have hjc : ∀ c, Continuous (jFun c) := fun c => by unfold jFun; fun_prop
  -- `f_m ≥ j_{(m-1)/12}` for `1 ≤ m ≤ 10`
  have hstep : ∀ m : ℕ, 1 ≤ m → m ≤ 10 → ∀ y ∈ Icc (0 : ℝ) (π / 2),
      jFun (((m : ℝ) - 1) / 12) y ≤ lowerSeq m y := by
    intro m hm1 hm10
    induction m, hm1 using Nat.le_induction with
    | base =>
      intro y _
      have hm0 : m0 0 = -1 := by norm_num [m0, k0]
      have hop : lowerOp (lowerSeq 0) y = 1 - y := by
        simp only [lowerOp, lowerSeq, hm0, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring
      have e1 : lowerSeq 1 y = max (lowerSeq 0 y) (lowerOp (lowerSeq 0) y) := rfl
      rw [e1, hop]
      simp only [jFun, Nat.cast_one, sub_self, zero_div, lowerSeq]
      rw [max_comm]
    | succ m hm1 ih =>
      intro y hy
      have ih' := ih (by omega)
      have hc : ((m : ℝ) - 1) / 12 ∈ Icc (0 : ℝ) (2 / 3) := by
        have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        have h2 : (m : ℝ) ≤ 9 := by exact_mod_cast (by omega : m ≤ 9)
        constructor <;> linarith
      have hj0 : ∀ z ∈ Icc (0 : ℝ) (π / 2), 0 ≤ jFun (((m : ℝ) - 1) / 12) z :=
        fun z _ => le_trans hc.1 (le_max_right _ _)
      have h1 := lemma6_5_3 hc hy
      have h2 := lemma6_5_4 (hjc _).continuousOn (inj_continuous_lowerSeq m).continuousOn ih'
        y hy
      have h3 : lowerOp (lowerSeq m) y ≤ lowerSeq (m + 1) y := le_max_right _ _
      have e : ((m : ℝ) - 1) / 12 + 1 / 12 = (((m + 1 : ℕ) : ℝ) - 1) / 12 := by push_cast; ring
      rw [e] at h1
      linarith
  -- `f_10 ≥ 3/4`
  have h10 : ∀ y ∈ Icc (0 : ℝ) (π / 2), 3 / 4 ≤ lowerSeq 10 y := by
    intro y hy
    have := hstep 10 (by norm_num) le_rfl y hy
    have e : jFun ((((10 : ℕ) : ℝ) - 1) / 12) y = max (1 - y) (3 / 4) := by
      simp only [jFun]; norm_num
    rw [e] at this
    linarith [le_max_right (1 - y) (3 / 4 : ℝ)]
  -- `f_11 ≥ 𝓕 f_10 ≥ 1 + x/8`
  have hm34 : m0 (3 / 4) = 1 / 8 := by rw [inj_m0_of_mem (by norm_num) (by norm_num)]; norm_num
  have h11 : lowerOp (lowerSeq 10) x ≤ lowerSeq 11 x := le_max_right _ _
  have hint : IntervalIntegrable (fun u => m0 (lowerSeq 10 (π / 2 - u))) volume 0 x :=
    (inj_continuous_m0.comp ((inj_continuous_lowerSeq 10).comp
      (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => (1 / 8 : ℝ))
    (g := fun u => m0 (lowerSeq 10 (π / 2 - u))) hx.1.le intervalIntegrable_const hint
    (fun u hu => by
      rw [← hm34]
      exact inj_m0_mono (h10 _ ⟨by linarith [hu.2, hx.2], by linarith [hu.1]⟩))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have : lowerOp (lowerSeq 10) x = 1 + ∫ u in (0 : ℝ)..x, m0 (lowerSeq 10 (π / 2 - u)) := rfl
  nlinarith [hx.1]

/-- **Theorem 6.5.6** (`thm:lower-bound-one`). For a balanced maximum cap, `f_K > 1` on `(0, π/2]`
and `g_K > 1` on `[0, π/2)`. -/
theorem theorem6_5_6 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (∀ t ∈ Ioc 0 (π / 2), 1 < fK K t) ∧ ∀ t ∈ Ico 0 (π / 2), 1 < gK K t := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have h1 := corollary6_4_4 hK
  obtain ⟨-, -, hfc, hgc⟩ := proposition6_4_6_continuous hcap h1
  have hL := lemma6_5_2 11 hK
  have hseq := inj_continuous_lowerSeq 11
  have hπ : (0 : ℝ) < π / 2 := by positivity
  constructor
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with htπ | htπ
    · rw [htπ]
      have hlim1 : Tendsto (fK K) (𝓝[<] (π / 2)) (𝓝 (fK K (π / 2))) := by
        have := ((hfc (π / 2) ⟨hπ.le, le_rfl⟩).mono Ioo_subset_Icc_self).tendsto
        rwa [nhdsWithin_Ioo_eq_nhdsLT hπ] at this
      have hlim2 : Tendsto (lowerSeq 11) (𝓝[<] (π / 2)) (𝓝 (lowerSeq 11 (π / 2))) :=
        hseq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hle : lowerSeq 11 (π / 2) ≤ fK K (π / 2) := by
        refine le_of_tendsto_of_tendsto hlim2 hlim1 ?_
        filter_upwards [Ioo_mem_nhdsLT hπ] with u hu
        exact hL.1 u ⟨hu.1.le, hu.2⟩
      exact lt_of_lt_of_le (lemma6_5_5 ⟨hπ, le_rfl⟩) hle
    · exact lt_of_lt_of_le (lemma6_5_5 ht) (hL.1 t ⟨ht.1.le, htπ⟩)
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      have hlim1 : Tendsto (gK K) (𝓝[>] 0) (𝓝 (gK K 0)) := by
        have := ((hgc 0 ⟨le_rfl, hπ.le⟩).mono Ioo_subset_Icc_self).tendsto
        rwa [nhdsWithin_Ioo_eq_nhdsGT hπ] at this
      have hlim2 : Tendsto (fun u => lowerSeq 11 (π / 2 - u)) (𝓝[>] 0)
          (𝓝 (lowerSeq 11 (π / 2))) := by
        have hc : Continuous fun u => lowerSeq 11 (π / 2 - u) :=
          hseq.comp (continuous_const.sub continuous_id)
        have := hc.continuousAt (x := 0) |>.tendsto
        simp only [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      have hle : lowerSeq 11 (π / 2) ≤ gK K 0 := by
        refine le_of_tendsto_of_tendsto hlim2 hlim1 ?_
        filter_upwards [Ioo_mem_nhdsGT hπ] with u hu
        exact hL.2 u ⟨hu.1, hu.2.le⟩
      exact lt_of_lt_of_le (lemma6_5_5 ⟨hπ, le_rfl⟩) hle
    · exact lt_of_lt_of_le (lemma6_5_5 ⟨by linarith [ht.2], by linarith⟩)
        (hL.2 t ⟨ht0, ht.2.le⟩)

/-- **Theorem 6.1.1** (`thm:injectivity`). Every balanced maximum cap satisfies the injectivity
condition. -/
theorem theorem6_1_1 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : SatisfiesInjectivity K := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have h1 := corollary6_4_4 hK
  obtain ⟨hx, -, hder⟩ := proposition6_4_6_deriv hcap h1
  obtain ⟨hf, hg⟩ := theorem6_5_6 hK
  refine ⟨h1, hx, fun t ht => ?_⟩
  have hd := (hder t ⟨ht.1.le, ht.2.le⟩).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [hd.deriv]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec, dot_uvec_vvec,
    dot_vvec_self]
  have := hf t ⟨ht.1, ht.2.le⟩
  have := hg t ⟨ht.1.le, ht.2⟩
  constructor <;> linarith

/-- **Theorem 1.7.1** (`thm:injectivity-abridged`). The rotation path `x_K` of a balanced maximum sofa
is continuously differentiable on `[0, π/2]`, with `x_K'(t) · u_t < 0` and `x_K'(t) · v_t > 0` for
`t ∈ (0, π/2)`. -/
theorem theorem1_7_1 {S : Set (ℝ × ℝ)} (hS : IsBalancedMaxSofa S (π / 2)) :
    ContDiffOn ℝ 1 (innerCorner (capOf S (π / 2))) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Ioo 0 (π / 2), dot (deriv (innerCorner (capOf S (π / 2))) t) (uvec t) < 0 ∧
        0 < dot (deriv (innerCorner (capOf S (π / 2))) t) (vvec t) := by
  obtain ⟨-, h2, h3⟩ := theorem6_1_1 hS.2
  exact ⟨h2, h3⟩

end MovingSofaOptimality
