module

public import MovingSofa.Basic.SurfaceArea
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The arc-length parametrization of the boundary of a planar convex body

Auxiliary file for `External/AreaFormula.lean` (package X1, prefix `af_`).

For a convex body `K` with positive perimeter `P = σ_K((0, 2π])`, the distribution function
`F = sigmaStieltjes K` of `σ_K` satisfies `F(t + 2π) = F(t) + P`, so it is unbounded in both
directions. Its generalized inverse `τ(y) = inf {t | y ≤ F(t)}` (the normal angle at arc length `y`)
satisfies `τ(y) ≤ t ↔ y ≤ F(t)`, and pushes the Lebesgue measure forward to `σ_K`.

The curve `γ(y) = v_K⁺(0) + ∫_{F(0)}^{y} v_{τ(r)} dr` is the arc-length parametrization of `∂K`:
* `γ(y) = v_K⁺(τ(y)) - (F(τ(y)) - y) v_{τ(y)}` lies on the edge `e_K(τ(y))`, so
  `γ(y) · u_{τ(y)} = h_K(τ(y))` (`af_dot_gamma`, `af_gamma_mem`);
* every point of every edge is some `γ(y)` (`af_exists_gamma_eq`);
* `γ` is `P`-periodic, and injective on every interval `[a, a + P)` when `K` has positive width
  in every direction (`af_gamma_injOn`);
* `γ` has derivative `v_{τ(y)}` wherever `τ` is continuous, i.e. outside a countable set
  (`af_hasDerivAt_gamma`).
-/

@[expose] public section

open Real Set Filter MeasureTheory Topology Function

namespace MovingSofa

section GenInv

/-- The generalized inverse `y ↦ inf {t | y ≤ f t}` of a Stieltjes function. -/
noncomputable def af_ginv (f : StieltjesFunction ℝ) (y : ℝ) : ℝ := sInf {t | y ≤ f t}

variable {f : StieltjesFunction ℝ}

/-- If `f` takes values below every `y`, the sets `{t | y ≤ f t}` are bounded below. -/
lemma af_bddBelow (hbot : ∀ y, ∃ t, f t < y) (y : ℝ) : BddBelow {t | y ≤ f t} := by
  obtain ⟨t₀, ht₀⟩ := hbot y
  refine ⟨t₀, fun t ht => ?_⟩
  by_contra h
  exact absurd (lt_of_le_of_lt (f.mono (not_le.1 h).le) ht₀) (not_lt.2 ht)

/-- By right continuity, the infimum defining `af_ginv f y` is attained. -/
lemma af_le_ginv_apply (htop : ∀ y, ∃ t, y ≤ f t) (y : ℝ) :
    y ≤ f (af_ginv f y) := by
  have hne : {t | y ≤ f t}.Nonempty := htop y
  have key : ∀ t, af_ginv f y < t → y ≤ f t := by
    intro t ht
    obtain ⟨t', ht', ht't⟩ := exists_lt_of_csInf_lt hne ht
    exact le_trans ht' (f.mono ht't.le)
  have hc : ContinuousWithinAt f (Ioi (af_ginv f y)) (af_ginv f y) :=
    (f.right_continuous _).mono Ioi_subset_Ici_self
  exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall fun t ht => key t ht)

/-- The Galois connection `af_ginv f y ≤ t ↔ y ≤ f t`. -/
lemma af_ginv_le_iff (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) {y t : ℝ} :
    af_ginv f y ≤ t ↔ y ≤ f t := by
  constructor
  · intro h; exact (af_le_ginv_apply htop y).trans (f.mono h)
  · intro h; exact csInf_le (af_bddBelow hbot y) h

lemma af_lt_ginv_iff (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) {y t : ℝ} :
    t < af_ginv f y ↔ f t < y := by
  rw [← not_le, af_ginv_le_iff htop hbot, not_le]

lemma af_ginv_mono (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) :
    Monotone (af_ginv f) := by
  intro y y' hyy'
  rw [af_ginv_le_iff htop hbot]
  exact hyy'.trans (af_le_ginv_apply htop y')

lemma af_preimage_ginv_Ioc (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) (a b : ℝ) :
    af_ginv f ⁻¹' Ioc a b = Ioc (f a) (f b) := by
  ext y
  simp only [mem_preimage, mem_Ioc, af_lt_ginv_iff htop hbot, af_ginv_le_iff htop hbot]

lemma af_leftLim_ginv_le (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) (y : ℝ) :
    leftLim f (af_ginv f y) ≤ y := by
  rw [f.mono.leftLim_eq_sSup]
  refine csSup_le (nonempty_Iio.image f) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ((af_lt_ginv_iff htop hbot).1 ht).le

/-- The generalized inverse pushes the Lebesgue measure forward to the Stieltjes measure. -/
lemma af_map_ginv (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) :
    Measure.map (af_ginv f) volume = f.measure := by
  refine (Measure.ext_of_Ioc f.measure _ fun a b _ => ?_).symm
  rw [Measure.map_apply (af_ginv_mono htop hbot).measurable measurableSet_Ioc,
    af_preimage_ginv_Ioc htop hbot, Real.volume_Ioc, f.measure_Ioc]

/-- Change of variables along the generalized inverse. -/
lemma af_setIntegral_ginv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (htop : ∀ y, ∃ t, y ≤ f t) (hbot : ∀ y, ∃ t, f t < y) {G : ℝ → E}
    (hG : Continuous G) (a b : ℝ) :
    ∫ y in Ioc (f a) (f b), G (af_ginv f y) = ∫ t in Ioc a b, G t ∂f.measure := by
  rw [← af_map_ginv htop hbot, setIntegral_map measurableSet_Ioc hG.aestronglyMeasurable
    (af_ginv_mono htop hbot).measurable.aemeasurable, af_preimage_ginv_Ioc htop hbot]

end GenInv

/-! ## The arc-length parametrization of the boundary -/

lemma af_continuous_vvec : Continuous vvec := by unfold vvec; fun_prop

/-- `‖v_t‖ ≤ 1` for the sup norm of `ℝ × ℝ`. -/
lemma af_norm_vvec_le (t : ℝ) : ‖vvec t‖ ≤ 1 := by
  rw [Prod.norm_def]
  simp only [vvec, Real.norm_eq_abs, abs_neg]
  exact max_le (abs_sin_le_one t) (abs_cos_le_one t)

/-- Bounded measurable functions are interval integrable. -/
lemma af_intervalIntegrable_of_bound {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable g volume a b :=
  ⟨IntegrableOn.of_bound measure_Ioc_lt_top hg.restrict C (ae_of_all _ hC),
    IntegrableOn.of_bound measure_Ioc_lt_top hg.restrict C (ae_of_all _ hC)⟩

/-- `dot` with a fixed vector commutes with interval integrals. -/
lemma af_dot_intervalIntegral {g : ℝ → ℝ × ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (w : ℝ × ℝ) : dot (∫ r in a..b, g r) w = ∫ r in a..b, dot (g r) w := by
  let L : ℝ × ℝ →L[ℝ] ℝ :=
    w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ p, L p = dot p w := fun p => by simp [L, dot]; ring
  rw [← hL, ← L.intervalIntegral_comp_comm hg]
  simp_rw [hL]

section Param

variable {K : Set (ℝ × ℝ)}

lemma af_edge_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : edge K (t + 2 * π) = edge K t := by
  simp only [edge, suppLine, line, uvec_add_two_pi, supp_add_two_pi]

/-- `v_K⁺` is `2π`-periodic. -/
lemma af_vplus_add_two_pi (K : Set (ℝ × ℝ)) (t : ℝ) : vplus K (t + 2 * π) = vplus K t := by
  simp only [vplus, af_edge_add_two_pi, uvec_add_two_pi, vvec_add_two_pi, supp_add_two_pi]

/-- The perimeter `σ_K((0, 2π])`. -/
noncomputable def af_perim (K : Set (ℝ × ℝ)) : ℝ :=
  sigmaStieltjes K (2 * π) - sigmaStieltjes K 0

lemma af_sigma_Ioc (K : Set (ℝ × ℝ)) (a b : ℝ) :
    sigma K (Ioc a b) = ENNReal.ofReal (sigmaStieltjes K b - sigmaStieltjes K a) :=
  (sigmaStieltjes K).measure_Ioc a b

/-- The atom `σ_K({t})` is the jump `F(t) - F(t⁻)` of the distribution function. -/
lemma af_sigmaAt_eq (K : Set (ℝ × ℝ)) (t : ℝ) :
    sigmaAt K t = sigmaStieltjes K t - leftLim (sigmaStieltjes K) t := by
  rw [sigmaAt, sigma, StieltjesFunction.measure_singleton,
    ENNReal.toReal_ofReal (sub_nonneg.2 ((sigmaStieltjes K).mono.leftLim_le le_rfl))]

lemma af_stieltjes_sub_periodic (hK : IsConvexBody K) {t t' : ℝ} (h : t ≤ t') :
    sigmaStieltjes K (t' + 2 * π) - sigmaStieltjes K (t + 2 * π) =
      sigmaStieltjes K t' - sigmaStieltjes K t := by
  have h1 := sigma_periodic hK (Ioc t t')
  rw [image_add_const_Ioc, af_sigma_Ioc, af_sigma_Ioc] at h1
  have m := (sigmaStieltjes K).mono
  rwa [ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.2 (m (by linarith))) (sub_nonneg.2 (m h))] at h1

/-- `F(t + 2π) = F(t) + P`. -/
lemma af_stieltjes_add_two_pi (hK : IsConvexBody K) (t : ℝ) :
    sigmaStieltjes K (t + 2 * π) = sigmaStieltjes K t + af_perim K := by
  unfold af_perim
  rcases le_total 0 t with h | h
  · have := af_stieltjes_sub_periodic hK h
    rw [zero_add] at this
    linarith
  · have := af_stieltjes_sub_periodic hK h
    rw [zero_add] at this
    linarith

lemma af_perim_nonneg (K : Set (ℝ × ℝ)) : 0 ≤ af_perim K :=
  sub_nonneg.2 ((sigmaStieltjes K).mono (by positivity))

lemma af_stieltjes_add_int_mul (hK : IsConvexBody K) (t : ℝ) (n : ℤ) :
    sigmaStieltjes K (t + n * (2 * π)) = sigmaStieltjes K t + n * af_perim K := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have := af_stieltjes_add_two_pi hK (t + n * (2 * π))
    push_cast at ih ⊢
    rw [show t + (n + 1) * (2 * π) = t + n * (2 * π) + 2 * π by ring, this, ih]; ring
  | pred n ih =>
    have := af_stieltjes_add_two_pi hK (t + (-(n : ℝ) - 1) * (2 * π))
    push_cast at ih ⊢
    rw [show t + (-(n : ℝ) - 1) * (2 * π) + 2 * π = t + -(n : ℝ) * (2 * π) by ring, ih] at this
    linarith

/-- With positive perimeter, `F` is unbounded above. -/
lemma af_htop (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    ∃ t, y ≤ sigmaStieltjes K t := by
  set n : ℕ := ⌈(y - sigmaStieltjes K 0) / af_perim K⌉₊
  refine ⟨0 + ((n : ℤ) : ℝ) * (2 * π), ?_⟩
  rw [af_stieltjes_add_int_mul hK]
  have h1 := Nat.le_ceil ((y - sigmaStieltjes K 0) / af_perim K)
  rw [div_le_iff₀ hP] at h1
  push_cast
  linarith

/-- With positive perimeter, `F` is unbounded below. -/
lemma af_hbot (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    ∃ t, sigmaStieltjes K t < y := by
  set n : ℕ := ⌈(sigmaStieltjes K 0 - y) / af_perim K⌉₊ + 1
  refine ⟨0 + ((-(n : ℤ) : ℤ) : ℝ) * (2 * π), ?_⟩
  rw [af_stieltjes_add_int_mul hK]
  have h1 := Nat.le_ceil ((sigmaStieltjes K 0 - y) / af_perim K)
  rw [div_le_iff₀ hP] at h1
  simp only [n]
  push_cast
  nlinarith

/-- The normal angle `τ(y)` at arc-length position `y`: the generalized inverse of `σ_K`'s
distribution function. -/
noncomputable def af_tau (K : Set (ℝ × ℝ)) : ℝ → ℝ := af_ginv (sigmaStieltjes K)

/-- The arc-length parametrization `γ(y) = v_K⁺(0) + ∫_{F(0)}^{y} v_{τ(r)} dr` of `∂K`. -/
noncomputable def af_gamma (K : Set (ℝ × ℝ)) (y : ℝ) : ℝ × ℝ :=
  vplus K 0 + ∫ r in (sigmaStieltjes K 0)..y, vvec (af_tau K r)

lemma af_tau_le_iff (hK : IsConvexBody K) (hP : 0 < af_perim K) {y t : ℝ} :
    af_tau K y ≤ t ↔ y ≤ sigmaStieltjes K t :=
  af_ginv_le_iff (af_htop hK hP) (af_hbot hK hP)

lemma af_lt_tau_iff (hK : IsConvexBody K) (hP : 0 < af_perim K) {y t : ℝ} :
    t < af_tau K y ↔ sigmaStieltjes K t < y :=
  af_lt_ginv_iff (af_htop hK hP) (af_hbot hK hP)

lemma af_tau_mono (hK : IsConvexBody K) (hP : 0 < af_perim K) : Monotone (af_tau K) :=
  af_ginv_mono (af_htop hK hP) (af_hbot hK hP)

lemma af_measurable_tau (hK : IsConvexBody K) (hP : 0 < af_perim K) : Measurable (af_tau K) :=
  (af_tau_mono hK hP).measurable

/-- `F(τ(y)⁻) ≤ y ≤ F(τ(y))`. -/
lemma af_mem_Icc_tau (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    leftLim (sigmaStieltjes K) (af_tau K y) ≤ y ∧ y ≤ sigmaStieltjes K (af_tau K y) :=
  ⟨af_leftLim_ginv_le (af_htop hK hP) (af_hbot hK hP) y, af_le_ginv_apply (af_htop hK hP) y⟩

/-- `τ(y + P) = τ(y) + 2π`. -/
lemma af_tau_add_perim (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    af_tau K (y + af_perim K) = af_tau K y + 2 * π := by
  apply le_antisymm
  · rw [af_tau_le_iff hK hP, af_stieltjes_add_two_pi hK]
    linarith [(af_mem_Icc_tau hK hP y).2]
  · by_contra h
    have h1 : af_tau K (y + af_perim K) - 2 * π < af_tau K y := by linarith [not_le.1 h]
    rw [af_lt_tau_iff hK hP] at h1
    have h2 := af_stieltjes_add_two_pi hK (af_tau K (y + af_perim K) - 2 * π)
    rw [sub_add_cancel] at h2
    linarith [(af_mem_Icc_tau hK hP (y + af_perim K)).2]

/-- `τ` pushes the Lebesgue measure on `(F(a), F(b)]` forward to `σ_K` on `(a, b]`. -/
lemma af_setIntegral_tau {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hK : IsConvexBody K) (hP : 0 < af_perim K) {G : ℝ → E} (hG : Continuous G) (a b : ℝ) :
    ∫ y in Ioc (sigmaStieltjes K a) (sigmaStieltjes K b), G (af_tau K y) =
      ∫ t in Ioc a b, G t ∂(sigma K) :=
  af_setIntegral_ginv (af_htop hK hP) (af_hbot hK hP) hG a b

lemma af_intervalIntegrable_vvec_tau (hK : IsConvexBody K) (hP : 0 < af_perim K) (a b : ℝ) :
    IntervalIntegrable (fun r => vvec (af_tau K r)) volume a b :=
  af_intervalIntegrable_of_bound
    (af_continuous_vvec.measurable.comp (af_measurable_tau hK hP)).aestronglyMeasurable 1
    (fun _ => af_norm_vvec_le _) a b

/-- `∫_{F(a)}^{F(b)} v_{τ(r)} dr = v_K⁺(b) - v_K⁺(a)`, by `vplus_sub_vplus`. -/
lemma af_integral_vvec_tau (hK : IsConvexBody K) (hP : 0 < af_perim K) (a b : ℝ) :
    ∫ r in (sigmaStieltjes K a)..(sigmaStieltjes K b), vvec (af_tau K r) =
      vplus K b - vplus K a := by
  rw [intervalIntegral, af_setIntegral_tau hK hP af_continuous_vvec,
    af_setIntegral_tau hK hP af_continuous_vvec]
  rcases le_total a b with h | h
  · rw [Ioc_eq_empty (not_lt.2 h), setIntegral_empty, sub_zero, vplus_sub_vplus hK h]
  · rw [Ioc_eq_empty (not_lt.2 h), setIntegral_empty, zero_sub, ← vplus_sub_vplus hK h, neg_sub]

/-- `γ(F(t)) = v_K⁺(t)`. -/
lemma af_gamma_stieltjes (hK : IsConvexBody K) (hP : 0 < af_perim K) (t : ℝ) :
    af_gamma K (sigmaStieltjes K t) = vplus K t := by
  rw [af_gamma, af_integral_vvec_tau hK hP 0 t]; abel

lemma af_gamma_sub (hK : IsConvexBody K) (hP : 0 < af_perim K) (y y' : ℝ) :
    af_gamma K y' - af_gamma K y = ∫ r in y..y', vvec (af_tau K r) := by
  unfold af_gamma
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (af_intervalIntegrable_vvec_tau hK hP (sigmaStieltjes K 0) y)
    (af_intervalIntegrable_vvec_tau hK hP y y')]
  abel

/-- `τ = t` on `(F(t⁻), F(t)]`. -/
lemma af_tau_eq_of_mem (hK : IsConvexBody K) (hP : 0 < af_perim K) {t r : ℝ}
    (h1 : leftLim (sigmaStieltjes K) t < r) (h2 : r ≤ sigmaStieltjes K t) : af_tau K r = t := by
  apply le_antisymm ((af_tau_le_iff hK hP).2 h2)
  by_contra h
  have h3 := (sigmaStieltjes K).mono.le_leftLim (not_le.1 h)
  linarith [(af_mem_Icc_tau hK hP r).2]

/-- On `[F(t⁻), F(t)]` the curve `γ` runs along the edge `e_K(t)`:
`γ(y) = v_K⁺(t) - (F(t) - y) v_t`. -/
lemma af_gamma_eq_of_mem (hK : IsConvexBody K) (hP : 0 < af_perim K) {t y : ℝ}
    (h1 : leftLim (sigmaStieltjes K) t ≤ y) (h2 : y ≤ sigmaStieltjes K t) :
    af_gamma K y = vplus K t - (sigmaStieltjes K t - y) • vvec t := by
  have h := af_gamma_sub hK hP y (sigmaStieltjes K t)
  rw [af_gamma_stieltjes hK hP, intervalIntegral.integral_of_le h2] at h
  have h3 : ∫ r in Ioc y (sigmaStieltjes K t), vvec (af_tau K r) =
      ∫ r in Ioc y (sigmaStieltjes K t), vvec t := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [af_tau_eq_of_mem hK hP (h1.trans_lt hr.1) hr.2]
  rw [h3, setIntegral_const, Real.volume_real_Ioc_of_le h2] at h
  rw [← h]; abel

lemma af_gamma_eq (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    af_gamma K y = vplus K (af_tau K y) -
      (sigmaStieltjes K (af_tau K y) - y) • vvec (af_tau K y) :=
  af_gamma_eq_of_mem hK hP (af_mem_Icc_tau hK hP y).1 (af_mem_Icc_tau hK hP y).2

/-- `γ(y)` lies on the supporting line `l_K(τ(y))`. -/
lemma af_dot_gamma (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    dot (af_gamma K y) (uvec (af_tau K y)) = supp K (af_tau K y) := by
  rw [af_gamma_eq hK hP, dot_sub_left, dot_smul_left, dot_vplus_uvec, dot_vvec_uvec, mul_zero,
    sub_zero]

/-- `γ(y)` lies on the edge `e_K(τ(y)) = [v_K⁻, v_K⁺]`, hence in `K`. -/
lemma af_gamma_mem (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) : af_gamma K y ∈ K := by
  obtain ⟨h1, h2⟩ := af_mem_Icc_tau hK hP y
  set t := af_tau K y
  have hplus : vplus K t ∈ K := (vplus_mem_edge hK t).1
  have hminus : vminus K t ∈ K := (vminus_mem_edge hK t).1
  have hpm := (proposition2_1_2 hK t).2
  rw [af_sigmaAt_eq] at hpm
  rw [af_gamma_eq hK hP]
  rcases eq_or_lt_of_le (sub_nonneg.2 ((sigmaStieltjes K).mono.leftLim_le (le_refl t)))
    with h0 | hpos
  · have : sigmaStieltjes K t - y = 0 := by linarith
    rw [this, zero_smul, sub_zero]; exact hplus
  · have hmem := hK.2.2.add_smul_sub_mem hplus hminus
      (t := (sigmaStieltjes K t - y) / (sigmaStieltjes K t - leftLim (sigmaStieltjes K) t))
      ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩
    have e : vminus K t - vplus K t =
        -((sigmaStieltjes K t - leftLim (sigmaStieltjes K) t) • vvec t) := by
      rw [hpm]; abel
    rw [e, smul_neg, smul_smul, div_mul_cancel₀ _ hpos.ne', ← sub_eq_add_neg] at hmem
    exact hmem

/-- `γ(y + P) = γ(y)`. -/
lemma af_gamma_add_perim (hK : IsConvexBody K) (hP : 0 < af_perim K) (y : ℝ) :
    af_gamma K (y + af_perim K) = af_gamma K y := by
  rw [af_gamma_eq hK hP, af_gamma_eq hK hP y, af_tau_add_perim hK hP, af_vplus_add_two_pi,
    vvec_add_two_pi, af_stieltjes_add_two_pi hK]
  congr 2; ring

/-- Every point of every edge `e_K(t)` is on the curve `γ`. -/
lemma af_exists_gamma_eq (hK : IsConvexBody K) (hP : 0 < af_perim K) {q : ℝ × ℝ} {t : ℝ}
    (hq : q ∈ edge K t) : ∃ y, af_gamma K y = q := by
  rw [edge_eq_segment hK] at hq
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  have hpm := (proposition2_1_2 hK t).2
  rw [af_sigmaAt_eq] at hpm
  have hσ : 0 ≤ sigmaStieltjes K t - leftLim (sigmaStieltjes K) t :=
    sub_nonneg.2 ((sigmaStieltjes K).mono.leftLim_le le_rfl)
  refine ⟨sigmaStieltjes K t - a * (sigmaStieltjes K t - leftLim (sigmaStieltjes K) t), ?_⟩
  rw [af_gamma_eq_of_mem hK hP (t := t) (by nlinarith) (by nlinarith), hpm]
  obtain rfl : b = 1 - a := by linarith
  ext <;> simp <;> ring

lemma af_gamma_periodic (hK : IsConvexBody K) (hP : 0 < af_perim K) :
    Periodic (af_gamma K) (af_perim K) :=
  af_gamma_add_perim hK hP

lemma af_preimage_tau_Ioc (hK : IsConvexBody K) (hP : 0 < af_perim K) (a b : ℝ) :
    af_tau K ⁻¹' Ioc a b = Ioc (sigmaStieltjes K a) (sigmaStieltjes K b) :=
  af_preimage_ginv_Ioc (af_htop hK hP) (af_hbot hK hP) a b

/-- `G ∘ τ` is integrable on `(F(a), F(b)]` for continuous `G`. -/
lemma af_integrableOn_comp_tau {E : Type*} [NormedAddCommGroup E] (hK : IsConvexBody K)
    (hP : 0 < af_perim K) {G : ℝ → E} (hG : Continuous G) (a b : ℝ) :
    IntegrableOn (fun y => G (af_tau K y)) (Ioc (sigmaStieltjes K a) (sigmaStieltjes K b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hG.continuousOn
  refine IntegrableOn.of_bound measure_Ioc_lt_top
    (hG.comp_aestronglyMeasurable (af_measurable_tau hK hP).aestronglyMeasurable) C ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => hC _ ?_
  rw [← af_preimage_tau_Ioc hK hP] at hy
  exact Ioc_subset_Icc_self hy

/-- `γ'(y) = v_{τ(y)}` wherever `τ` is continuous. -/
lemma af_hasDerivAt_gamma (hK : IsConvexBody K) (hP : 0 < af_perim K) {y : ℝ}
    (hy : ContinuousAt (af_tau K) y) : HasDerivAt (af_gamma K) (vvec (af_tau K y)) y := by
  have hmeas : Measurable (fun r => vvec (af_tau K r)) :=
    af_continuous_vvec.measurable.comp (af_measurable_tau hK hP)
  have := intervalIntegral.integral_hasDerivAt_right
    (af_intervalIntegrable_vvec_tau hK hP (sigmaStieltjes K 0) y)
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (af_continuous_vvec.continuousAt.comp hy)
  exact this.const_add (vplus K 0)

/-- If the normal angle turns by less than `π` between `y < y'`, then `γ(y) ≠ γ(y')`: all the
directions `v_{τ(r)}`, `r ∈ (y, y')`, lie in an open half-plane. -/
lemma af_gamma_ne_of_lt (hK : IsConvexBody K) (hP : 0 < af_perim K) {y y' : ℝ} (hyy' : y < y')
    (h : af_tau K y' - af_tau K y < π) : af_gamma K y ≠ af_gamma K y' := by
  intro heq
  set m := (af_tau K y + af_tau K y') / 2
  have h1 : dot (af_gamma K y' - af_gamma K y) (vvec m) = 0 := by
    rw [heq, sub_self, dot_zero_left]
  rw [af_gamma_sub hK hP, af_dot_intervalIntegral (af_intervalIntegrable_vvec_tau hK hP y y')] at h1
  have h2 : 0 < ∫ r in y..y', dot (vvec (af_tau K r)) (vvec m) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun r hr => ?_) hyy'
    · refine af_intervalIntegrable_of_bound ?_ 1 (fun r => ?_) y y'
      · have hc : Continuous fun s => dot (vvec s) (vvec m) := by unfold dot vvec; fun_prop
        exact (hc.measurable.comp (af_measurable_tau hK hP)).aestronglyMeasurable
      · rw [dot_vvec_vvec, Real.norm_eq_abs]; exact abs_cos_le_one _
    · rw [dot_vvec_vvec]
      apply cos_pos_of_mem_Ioo
      have := af_tau_mono hK hP hr.1.le
      have := af_tau_mono hK hP hr.2.le
      have hm : m = (af_tau K y + af_tau K y') / 2 := rfl
      constructor <;> linarith
  linarith

/-- If `K` has positive width in every direction, `γ` is injective on `[a, a + P)`. -/
lemma af_gamma_injOn (hK : IsConvexBody K) (hP : 0 < af_perim K)
    (hw : ∀ t, 0 < supp K t + supp K (t + π)) (a : ℝ) :
    InjOn (af_gamma K) (Ico a (a + af_perim K)) := by
  suffices H : ∀ y y', y ∈ Ico a (a + af_perim K) → y' ∈ Ico a (a + af_perim K) → y < y' →
      af_gamma K y ≠ af_gamma K y' by
    intro y hy y' hy' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact H y y' hy hy' h heq
    · exact H y' y hy' hy h heq.symm
  intro y y' hy hy' hlt heq
  rcases lt_trichotomy (af_tau K y' - af_tau K y) π with h | h | h
  · exact af_gamma_ne_of_lt hK hP hlt h heq
  · have e1 := af_dot_gamma hK hP y
    have e2 := af_dot_gamma hK hP y'
    rw [← heq, show af_tau K y' = af_tau K y + π by linarith, uvec_add_pi, dot_neg_right] at e2
    linarith [hw (af_tau K y)]
  · have hlt' : y' < y + af_perim K := by linarith [hy'.2, hy.1]
    have h2 : af_tau K (y + af_perim K) - af_tau K y' < π := by
      rw [af_tau_add_perim hK hP]; linarith
    exact af_gamma_ne_of_lt hK hP hlt' h2 (by rw [af_gamma_add_perim hK hP, heq])

end Param

end MovingSofa
