module

public import MovingSofa.Injectivity.DiscreteIneq
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The inequality on balanced maximum caps (§6.4)

Lemmas 6.4.1 (`lem:arm-length-discrete-bound`), 6.4.2 (`lem:leg-convergence`), Theorem 6.4.3
(`thm:balanced-ineq-limit`), Corollary 6.4.4 (`cor:cap-nondegenerate`), Propositions 6.4.5–6.4.6 and
Definition 6.4.1 (`def:cap-nondegenerate`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory
open scoped Interval

namespace MovingSofa

/-! ### Lemma 6.4.1 -/

lemma inj_vplus_eq_vminus_of_sigma {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {t : ℝ}
    (h : sigma K {t} = 0) : vplus K t = vminus K t := by
  rw [(proposition2_1_2 hK t).2, sigmaAt, h, ENNReal.toReal_zero, zero_smul, add_zero]


lemma inj_grid_of_mem {k : ℕ} {t : ℝ} (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    ∃ m : ℕ, m + 1 ≤ 2 ^ (k + 1) ∧ t = m * stepSize k := by
  rcases ht with rfl | ht
  · exact ⟨0, Nat.one_le_two_pow, by simp⟩
  · obtain ⟨j, -, hjn, rfl⟩ := inj_mem_angles.1 ht
    exact ⟨j, hjn, rfl⟩

lemma inj_hasDerivAt_dot_uvec (w : ℝ × ℝ) (s : ℝ) :
    HasDerivAt (fun x => dot w (uvec x)) (dot w (vvec s)) s := by
  have h := ((hasDerivAt_cos s).const_mul w.1).add ((hasDerivAt_sin s).const_mul w.2)
  have e1 : (fun x => dot w (uvec x)) = fun x => w.1 * cos x + w.2 * sin x := by
    funext x; simp [dot, uvec]
  have e2 : dot w (vvec s) = w.1 * -sin s + w.2 * cos s := by unfold dot vvec; ring
  rw [e1, e2]; exact h

lemma inj_dot_le_of_norm2 {w : ℝ × ℝ} (h : norm2 w ≤ 5) (s : ℝ) : -5 ≤ dot w (vvec s) := by
  have h1 : dot w w ≤ 25 := by
    have := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 5)).1 h
    linarith
  have e := inj_dot_self_eq w s
  nlinarith [sq_nonneg (dot w (uvec s))]

/-- **Lemma 6.4.1** (`lem:arm-length-discrete-bound`). For a maximum polygon cap with step size `δ`,
`t ∈ {0} ∪ Θ_n` and `t' ∈ (t, t + δ)`: (1) `g_K⁺(t) ≥ g_K⁺(t') = g_K⁻(t') ≥ g_K⁻(t + δ)`;
(2) `g_K⁺(t) - g_K⁻(t + δ) ≤ 5δ`. -/
theorem lemma6_4_1 {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    (∀ t' ∈ Ioo t (t + stepSize k), gPlus K t' ≤ gPlus K t ∧ gPlus K t' = gMinus K t' ∧
        gMinus K (t + stepSize k) ≤ gMinus K t') ∧
      gPlus K t - gMinus K (t + stepSize k) ≤ 5 * stepSize k := by
  have hKp := hK.1
  have hKc : IsConvexBody K := hKp.1.2.1
  have hδ := inj_stepSize_pos k
  have hn := inj_two_pow_mul_stepSize k
  obtain ⟨hc, hs, -, -, -⟩ := inj_step_trig k
  obtain ⟨m, hm, htm⟩ := inj_grid_of_mem ht
  obtain ⟨hAK, hA1, hA2, hA3⟩ := inj_polygon_consecutive hKp (m := m) (by omega) htm
  obtain ⟨hCK, hC1, hC2, hC3⟩ := inj_polygon_consecutive hKp (m := 2 ^ (k + 1) + m) (by omega)
    (a := t + π / 2) (by rw [htm, ← hn]; push_cast; ring)
  have hsinne : sin (t + stepSize k - t) ≠ 0 := by rw [add_sub_cancel_left]; exact hs.ne'
  have hsinne' : sin (t + π / 2 + stepSize k - (t + π / 2)) ≠ 0 := by
    rw [add_sub_cancel_left]; exact hs.ne'
  set A := vint K t (t + stepSize k) with hAdef
  set C := vint K (t + π / 2) (t + π / 2 + stepSize k) with hCdef
  have hsuppA : ∀ s ∈ Icc t (t + stepSize k), supp K s = dot A (uvec s) := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with rfl | h1
    · exact (vint_mem_line_left K _ _).symm
    rcases eq_or_lt_of_le hs'.2 with rfl | h2
    · exact (vint_mem_line_right K hsinne).symm
    · exact (hA3 s ⟨h1, h2⟩).1
  have hsuppC : ∀ s ∈ Icc t (t + stepSize k), supp K (s + π / 2) = dot C (uvec (s + π / 2)) := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with rfl | h1
    · exact (vint_mem_line_left K _ _).symm
    rcases eq_or_lt_of_le hs'.2 with rfl | h2
    · rw [show t + stepSize k + π / 2 = t + π / 2 + stepSize k by ring]
      exact (vint_mem_line_right K hsinne').symm
    · exact (hC3 (s + π / 2) ⟨by linarith, by linarith⟩).1
  set G : ℝ → ℝ := fun s => dot (A - C) (uvec s) with hG
  have hgt : gPlus K t = G t := by
    rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, hC1,
      hsuppA t ⟨le_rfl, by linarith⟩]
    exact (dot_sub_left _ _ _).symm
  have hgtd : gMinus K (t + stepSize k) = G (t + stepSize k) := by
    rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, cMinus,
      show t + stepSize k + π / 2 = t + π / 2 + stepSize k by ring, hC2,
      hsuppA (t + stepSize k) ⟨by linarith, le_rfl⟩]
    exact (dot_sub_left _ _ _).symm
  have hgs : ∀ s ∈ Ioo t (t + stepSize k), gPlus K s = G s ∧ gMinus K s = G s := by
    intro s hs'
    have hC := hC3 (s + π / 2) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    constructor
    · rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus, hC.2.1,
        hsuppA s ⟨hs'.1.le, hs'.2.le⟩]
      exact (dot_sub_left _ _ _).symm
    · rw [gMinus, dot_sub_left, inj_dot_outerCorner_uvec, cMinus, hC.2.2,
        hsuppA s ⟨hs'.1.le, hs'.2.le⟩]
      exact (dot_sub_left _ _ _).symm
  -- the derivative `G'(s) = (A - C) · v_s ∈ [-5, 0]`
  have hGd : ∀ s, HasDerivAt G (dot (A - C) (vvec s)) s := fun s =>
    inj_hasDerivAt_dot_uvec (A - C) s
  have hGneg : ∀ s ∈ Icc t (t + stepSize k), dot (A - C) (vvec s) ≤ 0 := by
    intro s hs'
    rw [dot_sub_left, ← uvec_add_pi_div_two, ← hsuppC s hs']
    linarith [dot_le_supp hKc.2.1 hAK (s + π / 2)]
  have hG5 : ∀ s, -5 ≤ dot (A - C) (vvec s) := fun s =>
    inj_dot_le_of_norm2 ((lemma6_3_1 hK).1 A hAK C hCK) s
  have hGc : Continuous G := by
    simp only [hG, dot, uvec]; fun_prop
  have hanti : AntitoneOn G (Icc t (t + stepSize k)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hGc.continuousOn
      (fun s _ => (hGd s).differentiableAt.differentiableWithinAt)
    intro s hs'
    rw [interior_Icc] at hs'
    rw [(hGd s).deriv]
    exact hGneg s ⟨hs'.1.le, hs'.2.le⟩
  have hmono : MonotoneOn (fun s => G s + 5 * s) (Icc t (t + stepSize k)) := by
    have hd : ∀ s, HasDerivAt (fun s => G s + 5 * s) (dot (A - C) (vvec s) + 5) s := by
      intro s
      have := (hGd s).add ((hasDerivAt_id s).const_mul 5)
      rw [mul_one] at this
      exact this
    have hc5 : Continuous (fun s => G s + 5 * s) := hGc.add (continuous_const.mul continuous_id)
    apply monotoneOn_of_deriv_nonneg (f := fun s => G s + 5 * s) (convex_Icc _ _)
      hc5.continuousOn (fun s _ => (hd s).differentiableAt.differentiableWithinAt)
    intro s _
    rw [(hd s).deriv]
    linarith [hG5 s]
  have htI : t ∈ Icc t (t + stepSize k) := ⟨le_rfl, by linarith⟩
  have htdI : t + stepSize k ∈ Icc t (t + stepSize k) := ⟨by linarith, le_rfl⟩
  refine ⟨fun t' ht' => ?_, ?_⟩
  · have ht'I : t' ∈ Icc t (t + stepSize k) := ⟨ht'.1.le, ht'.2.le⟩
    obtain ⟨hp, hm'⟩ := hgs t' ht'
    refine ⟨?_, by rw [hp, hm'], ?_⟩
    · rw [hp, hgt]; exact hanti htI ht'I ht'.1.le
    · rw [hm', hgtd]; exact hanti ht'I htdI ht'.2.le
  · rw [hgt, hgtd]
    have := hmono htI htdI (by linarith)
    simp only at this
    linarith

/-! ### Hausdorff convergence and the support function -/

/-- The support function of a convex body is bounded. -/
lemma inj_supp_bounded {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : ∃ R, ∀ t, |supp K t| ≤ R := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  refine ⟨2 * C, fun t => ?_⟩
  obtain ⟨p, hp, hpt⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  rw [← hpt]
  have h1 : |p.1| ≤ C := (norm_fst_le p).trans (hC p hp)
  have h2 : |p.2| ≤ C := (norm_snd_le p).trans (hC p hp)
  simp only [dot, uvec]
  calc |p.1 * cos t + p.2 * sin t| ≤ |p.1 * cos t| + |p.2 * sin t| := abs_add_le _ _
    _ = |p.1| * |cos t| + |p.2| * |sin t| := by rw [abs_mul, abs_mul]
    _ ≤ |p.1| * 1 + |p.2| * 1 := by
        gcongr
        · exact abs_cos_le_one t
        · exact abs_sin_le_one t
    _ ≤ 2 * C := by linarith

lemma inj_abs_supp_sub_le {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (t : ℝ) : |supp K₁ t - supp K₂ t| ≤ hausdorffDist K₁ K₂ := by
  obtain ⟨R₁, hR₁⟩ := inj_supp_bounded h₁
  obtain ⟨R₂, hR₂⟩ := inj_supp_bounded h₂
  refine le_ciSup (f := fun t => |supp K₁ t - supp K₂ t|) ⟨R₁ + R₂, ?_⟩ t
  rintro _ ⟨s, rfl⟩
  calc |supp K₁ s - supp K₂ s| ≤ |supp K₁ s| + |supp K₂ s| := abs_sub _ _
    _ ≤ R₁ + R₂ := add_le_add (hR₁ s) (hR₂ s)

lemma inj_tendsto_supp {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)} (hKs : ∀ n, IsConvexBody (Ks n))
    (hK : IsConvexBody K) (hlim : HausdorffTendsto Ks K) (t : ℝ) :
    Tendsto (fun n => supp (Ks n) t) atTop (𝓝 (supp K t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => inj_abs_supp_sub_le (hKs n) hK t) hlim

lemma inj_tendsto_vint {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hsupp : ∀ t, Tendsto (fun n => supp (Ks n) t) atTop (𝓝 (supp K t))) (a b : ℝ) :
    Tendsto (fun n => vint (Ks n) a b) atTop (𝓝 (vint K a b)) := by
  unfold vint
  exact ((hsupp a).smul_const _).add
    ((((hsupp b).sub ((hsupp a).mul_const _)).div_const _).smul_const _)

/-- `v_K⁺(s) · v_s ≤ v_K(s, s + ε) · v_s` for `ε ∈ (0, π)`. -/
lemma inj_dot_vplus_le_vint {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hεπ : ε < π) :
    dot (vplus K s) (vvec s) ≤ dot (vint K s (s + ε)) (vvec s) := by
  have hsin : 0 < sin ε := sin_pos_of_pos_of_lt_pi hε hεπ
  have hq1 : dot (vint K s (s + ε)) (uvec s) = supp K s := vint_mem_line_left K s (s + ε)
  have hq2 : dot (vint K s (s + ε)) (uvec (s + ε)) = supp K (s + ε) :=
    vint_mem_line_right K (by rw [add_sub_cancel_left]; exact hsin.ne')
  have hv2 : dot (vplus K s) (uvec (s + ε)) ≤ supp K (s + ε) :=
    dot_le_supp hK.2.1 (vplus_mem_edge hK s).1 _
  have e := inj_eq_add_smul_vvec (p := vplus K s) (q := vint K s (s + ε)) (t := s)
    (by rw [dot_vplus_uvec, hq1])
  rw [e, dot_add_left, dot_smul_left, dot_vvec_uvec', hq2, add_sub_cancel_left] at hv2
  have : dot (vplus K s - vint K s (s + ε)) (vvec s) ≤ 0 := by nlinarith
  rw [dot_sub_left] at this; linarith

/-- `v_K(s - ε, s) · v_s ≤ v_K⁻(s) · v_s` for `ε ∈ (0, π)`. -/
lemma inj_vint_le_dot_vminus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hεπ : ε < π) :
    dot (vint K (s - ε) s) (vvec s) ≤ dot (vminus K s) (vvec s) := by
  have hsin : 0 < sin ε := sin_pos_of_pos_of_lt_pi hε hεπ
  have hq1 : dot (vint K (s - ε) s) (uvec (s - ε)) = supp K (s - ε) :=
    vint_mem_line_left K (s - ε) s
  have hq2 : dot (vint K (s - ε) s) (uvec s) = supp K s :=
    vint_mem_line_right K (by rw [sub_sub_cancel]; exact hsin.ne')
  have hv2 : dot (vminus K s) (uvec (s - ε)) ≤ supp K (s - ε) :=
    dot_le_supp hK.2.1 (vminus_mem_edge hK s).1 _
  have e := inj_eq_add_smul_vvec (p := vminus K s) (q := vint K (s - ε) s) (t := s)
    (by rw [dot_vminus_uvec, hq2])
  rw [e, dot_add_left, dot_smul_left, dot_vvec_uvec', hq1, show s - ε - s = -ε by ring,
    sin_neg] at hv2
  have : 0 ≤ dot (vminus K s - vint K (s - ε) s) (vvec s) := by nlinarith
  rw [dot_sub_left] at this; linarith

lemma inj_tendsto_add_right (s : ℝ) : Tendsto (fun ε : ℝ => s + ε) (𝓝[>] 0) (𝓝[>] s) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Continuous (fun ε : ℝ => s + ε) := continuous_const.add continuous_id
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [mem_Ioi] at hε ⊢; linarith

lemma inj_tendsto_sub_right (s : ℝ) : Tendsto (fun ε : ℝ => s - ε) (𝓝[>] 0) (𝓝[<] s) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Continuous (fun ε : ℝ => s - ε) := continuous_const.sub continuous_id
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [mem_Ioi, mem_Iio] at hε ⊢; linarith

lemma inj_tendsto_vint_right_dot {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) :
    Tendsto (fun ε => dot (vint K s (s + ε)) (vvec s)) (𝓝[>] 0) (𝓝 (dot (vplus K s) (vvec s))) :=
  ((inj_continuous_dot (vvec s)).tendsto _).comp
    ((tendsto_vint_right hK s).comp (inj_tendsto_add_right s))

lemma inj_tendsto_vint_left_dot {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (s : ℝ) :
    Tendsto (fun ε => dot (vint K (s - ε) s) (vvec s)) (𝓝[>] 0) (𝓝 (dot (vminus K s) (vvec s))) :=
  ((inj_continuous_dot (vvec s)).tendsto _).comp
    ((tendsto_vint_left hK s).comp (inj_tendsto_sub_right s))

lemma inj_eventually_pos_lt_pi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < π := by
  filter_upwards [Ioo_mem_nhdsGT pi_pos] with ε hε using hε

/-- If `K_n → K` and `v_K⁺(s) · v_s = v_K⁻(s) · v_s`, then `v_{K_n}⁺(s) · v_s → v_K⁺(s) · v_s`. -/
lemma inj_tendsto_dvplus {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K)
    (hsupp : ∀ t, Tendsto (fun n => supp (Ks n) t) atTop (𝓝 (supp K t))) {s : ℝ}
    (hs : dot (vplus K s) (vvec s) = dot (vminus K s) (vvec s)) :
    Tendsto (fun n => dot (vplus (Ks n) s) (vvec s)) atTop (𝓝 (dot (vplus K s) (vvec s))) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    rw [hs] at ha
    obtain ⟨ε, hε, ⟨hε0, hεπ⟩⟩ :=
      (((inj_tendsto_vint_left_dot hK s).eventually (lt_mem_nhds ha)).and
        inj_eventually_pos_lt_pi).exists
    have hn : Tendsto (fun n => dot (vint (Ks n) (s - ε) s) (vvec s)) atTop
        (𝓝 (dot (vint K (s - ε) s) (vvec s))) :=
      ((inj_continuous_dot (vvec s)).tendsto _).comp (inj_tendsto_vint hsupp _ _)
    filter_upwards [hn.eventually (lt_mem_nhds hε)] with n hn'
    exact lt_of_lt_of_le hn' ((inj_vint_le_dot_vminus (hKs n) s hε0 hεπ).trans
      (dot_vminus_le_dot_vplus (hKs n) s))
  · intro b hb
    obtain ⟨ε, hε, ⟨hε0, hεπ⟩⟩ :=
      (((inj_tendsto_vint_right_dot hK s).eventually (gt_mem_nhds hb)).and
        inj_eventually_pos_lt_pi).exists
    have hn : Tendsto (fun n => dot (vint (Ks n) s (s + ε)) (vvec s)) atTop
        (𝓝 (dot (vint K s (s + ε)) (vvec s))) :=
      ((inj_continuous_dot (vvec s)).tendsto _).comp (inj_tendsto_vint hsupp _ _)
    filter_upwards [hn.eventually (gt_mem_nhds hε)] with n hn'
    exact lt_of_le_of_lt (inj_dot_vplus_le_vint (hKs n) s hε0 hεπ) hn'

lemma inj_measurable_gPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) : Measurable (gPlus K) := by
  have e : gPlus K = fun t => supp K t +
      (sigmaFun K (t + π / 2) - ∫ s in (0 : ℝ)..(t + π / 2), supp K s) := by
    funext t; rw [inj_gPlus_eq, inj_dot_vplus_vvec_eq]
  rw [e]
  have h1 : Measurable (supp K) := (inj_continuous_supp hK).measurable
  have h2 : Measurable fun t => sigmaFun K (t + π / 2) :=
    ((monotone_sigmaFun hK).comp
      (fun x y h => by linarith : Monotone fun t : ℝ => t + π / 2)).measurable
  have h3 : Measurable fun t => ∫ s in (0 : ℝ)..(t + π / 2), supp K s :=
    ((inj_continuous_primitive_supp hK).comp (continuous_id.add continuous_const)).measurable
  exact h1.add (h2.sub h3)

lemma inj_gPlus_le_width {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    gPlus K t ≤ supp K t + supp K (t + π) := by
  rw [gPlus, dot_sub_left, inj_dot_outerCorner_uvec, cPlus]
  have := dot_le_supp hK.2.1 (vplus_mem_edge hK (t + π / 2)).1 (t + π)
  rw [uvec_add_pi, dot_neg_right] at this
  linarith

/-- The atoms of `σ_K` form a countable set. -/
lemma inj_countable_atoms (K : Set (ℝ × ℝ)) : Set.Countable {x : ℝ | sigma K {x} ≠ 0} := by
  refine (sigmaStieltjes K).countable_leftLim_ne.mono ?_
  intro x hx h
  apply hx
  rw [sigma, StieltjesFunction.measure_singleton, h, sub_self, ENNReal.ofReal_zero]

/-- **Lemma 6.4.2** (`lem:leg-convergence`). If polygon caps `K_n` (rotation angle `π/2`) converge to a
cap `K` in the Hausdorff distance, then `∫_0^{π/2} |g_{K_n}⁺ - g_K⁺| → 0`. -/
theorem lemma6_4_2 {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hΘ : ∀ n, (Θs n).ω = π / 2) (hKs : ∀ n, IsPolygonCap (Θs n) (Ks n)) (hK : IsCap K (π / 2))
    (hlim : HausdorffTendsto Ks K) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(π / 2), |gPlus (Ks n) t - gPlus K t|) atTop (𝓝 0) := by
  have hKc : IsConvexBody K := hK.2.1
  have hKsc : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.2.1
  have hsupp := inj_tendsto_supp hKsc hKc hlim
  obtain ⟨R, hR⟩ := inj_supp_bounded hKc
  have hev : ∀ᶠ n in atTop, hausdorffDist (Ks n) K ≤ 1 := hlim.eventually (ge_mem_nhds one_pos)
  -- the pointwise limit, off the countable set of atoms of `σ_K`
  have hcount : Set.Countable {t : ℝ | sigma K {t + π / 2} ≠ 0} :=
    ((inj_countable_atoms K).image (fun x => x - π / 2)).mono
      (fun t ht => show t ∈ (fun x => x - π / 2) '' {x : ℝ | sigma K {x} ≠ 0} from
        ⟨t + π / 2, ht, by ring⟩)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), sigma K {t + π / 2} = 0 := by
    rw [ae_iff]
    exact hcount.measure_zero _
  have hlimit : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) (π / 2) →
      Tendsto (fun n => |gPlus (Ks n) t - gPlus K t|) atTop (𝓝 0) := by
    filter_upwards [hae] with t ht _
    have heq : dot (vplus K (t + π / 2)) (vvec (t + π / 2)) =
        dot (vminus K (t + π / 2)) (vvec (t + π / 2)) := by
      rw [inj_vplus_eq_vminus_of_sigma hKc ht]
    have hg : Tendsto (fun n => gPlus (Ks n) t) atTop (𝓝 (gPlus K t)) := by
      simp_rw [inj_gPlus_eq]
      exact (hsupp t).add (inj_tendsto_dvplus hKsc hKc hsupp heq)
    have := (hg.sub_const (gPlus K t)).abs
    simpa using this
  -- the domination
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) (π / 2) →
      ‖|gPlus (Ks n) t - gPlus K t|‖ ≤ 4 * R + 2 := by
    filter_upwards [hev] with n hn
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    have h1 := inj_abs_supp_sub_le (hKsc n) hKc t
    have h2 := inj_abs_supp_sub_le (hKsc n) hKc (t + π)
    have g1 := inj_gPlus_le_width (hKsc n) t
    have g2 := inj_gPlus_le_width hKc t
    have g3 := (inj_arm_nonneg (hKsc n) t).2.2.1
    have g4 := (inj_arm_nonneg hKc t).2.2.1
    have r1 := abs_le.1 (hR t)
    have r2 := abs_le.1 (hR (t + π))
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    rw [abs_le] at h1 h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (fun t => |gPlus (Ks n) t - gPlus K t|)
      ((volume : Measure ℝ).restrict (Ι (0 : ℝ) (π / 2))) :=
    Filter.Eventually.of_forall fun n =>
      (continuous_abs.measurable.comp
        ((inj_measurable_gPlus (hKsc n)).sub (inj_measurable_gPlus hKc))).aestronglyMeasurable
  have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 4 * R + 2) hmeas hbound intervalIntegrable_const hlimit
  simpa using this

/-! ### Theorem 6.4.3 -/

/-- Finite measures on `ℝ` compare as soon as they compare on open intervals. -/
lemma inj_measure_le_of_Ioo {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b, a < b → μ (Ioo a b) ≤ ν (Ioo a b)) : μ ≤ ν := by
  have hIoc : ∀ a b, a < b → μ (Ioc a b) ≤ ν (Ioc a b) := by
    intro a b hab
    have e : ⋂ r > b, Ioo a r = Ioc a b := by
      ext x
      simp only [mem_iInter, mem_Ioo, mem_Ioc]
      constructor
      · intro hx
        refine ⟨(hx (b + 1) (by linarith)).1, ?_⟩
        by_contra hxb
        rw [not_le] at hxb
        exact lt_irrefl x (hx x hxb).2
      · rintro ⟨h1, h2⟩ r hr
        exact ⟨h1, lt_of_le_of_lt h2 hr⟩
    have hm : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
        Tendsto (fun r => ρ (Ioo a r)) (𝓝[>] b) (𝓝 (ρ (Ioc a b))) := by
      intro ρ _
      rw [← e]
      exact tendsto_measure_biInter_gt (fun r _ => measurableSet_Ioo.nullMeasurableSet)
        (fun i j _ hij => Ioo_subset_Ioo_right hij) ⟨b + 1, by linarith, measure_ne_top ρ _⟩
    apply le_of_tendsto_of_tendsto (hm μ) (hm ν)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact h a r (lt_trans hab hr)
  have hIic : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (x y : ℝ), x ≤ y →
      ρ.real (Iic y) = ρ.real (Iic x) + ρ.real (Ioc x y) := by
    intro ρ _ x y hxy
    rw [← Iic_union_Ioc_eq_Iic hxy, measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  set F : ℝ → ℝ := fun x => ν.real (Iic x) - μ.real (Iic x) with hF
  have hmono : Monotone F := by
    intro x y hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    simp only [hF]
    rw [hIic ν x y hxy, hIic μ x y hxy]
    have h1 : μ.real (Ioc x y) ≤ ν.real (Ioc x y) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hIoc x y hlt)
    linarith
  have hrc : ∀ x, ContinuousWithinAt F (Ici x) x := by
    intro x
    have hm : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
        Tendsto (fun r => ρ.real (Iic r)) (𝓝[>] x) (𝓝 (ρ.real (Iic x))) := by
      intro ρ _
      have e : ⋂ r > x, Iic r = Iic x := by
        ext y
        simp only [mem_iInter, mem_Iic]
        constructor
        · intro hy
          by_contra hxy
          rw [not_le] at hxy
          have := hy ((x + y) / 2) (by linarith)
          linarith
        · intro hy r hr; linarith
      have := tendsto_measure_biInter_gt (μ := ρ) (s := fun r => Iic r) (a := x)
        (fun r _ => measurableSet_Iic.nullMeasurableSet) (fun i j _ hij => Iic_subset_Iic.2 hij)
        ⟨x + 1, by linarith, measure_ne_top ρ _⟩
      rw [e] at this
      exact (ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp this
    apply continuousWithinAt_Ioi_iff_Ici.1
    exact (hm ν).sub (hm μ)
  let S : StieltjesFunction ℝ := ⟨F, hmono, hrc⟩
  have key : ν = μ + S.measure := by
    apply Measure.ext_of_Ioc
    intro a b hab
    symm
    rw [Measure.add_apply, StieltjesFunction.measure_Ioc]
    show μ (Ioc a b) + ENNReal.ofReal (F b - F a) = ν (Ioc a b)
    have e1 : F b - F a = ν.real (Ioc a b) - μ.real (Ioc a b) := by
      simp only [hF]; rw [hIic ν a b hab.le, hIic μ a b hab.le]; ring
    have h1 : μ.real (Ioc a b) ≤ ν.real (Ioc a b) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hIoc a b hab)
    rw [e1, ← ofReal_measureReal (μ := μ), ← ENNReal.ofReal_add measureReal_nonneg (by linarith),
      add_sub_cancel, ofReal_measureReal]
  calc μ ≤ μ + S.measure := Measure.le_add_right le_rfl
    _ = ν := key.symm

lemma inj_tendsto_dot {α : Type*} {l : Filter α} {f g : α → ℝ × ℝ} {a b : ℝ × ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x => dot (f x) (g x)) l (𝓝 (dot a b)) := by
  unfold dot
  exact ((hf.fst_nhds).mul (hg.fst_nhds)).add ((hf.snd_nhds).mul (hg.snd_nhds))

/-- `σ_K((a, b)) = v_K⁻(b) · v_b - v_K⁺(a) · v_a + ∫_a^b h_K`. -/
lemma inj_sigma_Ioo_toReal {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a < b) :
    (sigma K (Ioo a b)).toReal =
      dot (vminus K b) (vvec b) - dot (vplus K a) (vvec a) + ∫ t in a..b, supp K t := by
  have hc := inj_continuous_supp hK
  have hS : sigma K (Ioo a b) =
      ENNReal.ofReal (Function.leftLim (sigmaFun K) b - sigmaFun K a) := by
    simp [sigma, sigmaStieltjes, hK, StieltjesFunction.measure_Ioo]
  have hv : Continuous vvec := (continuous_sin.neg).prodMk continuous_cos
  have hlim : Function.leftLim (sigmaFun K) b =
      dot (vminus K b) (vvec b) + ∫ t in (0 : ℝ)..b, supp K t := by
    apply leftLim_eq_of_tendsto
    have h1 : Tendsto (fun x => dot (vplus K x) (vvec x)) (𝓝[<] b)
        (𝓝 (dot (vminus K b) (vvec b))) :=
      inj_tendsto_dot (tendsto_vplus_left hK b)
        (hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have h2 : Tendsto (fun x => ∫ t in (0 : ℝ)..x, supp K t) (𝓝[<] b)
        (𝓝 (∫ t in (0 : ℝ)..b, supp K t)) :=
      (inj_continuous_primitive_supp hK).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact h1.add h2
  have hnn : 0 ≤ Function.leftLim (sigmaFun K) b - sigmaFun K a :=
    sub_nonneg.2 ((monotone_sigmaFun hK).le_leftLim hab)
  rw [hS, ENNReal.toReal_ofReal hnn, hlim, sigmaFun]
  have h3 := intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable (μ := volume) 0 b) (hc.intervalIntegrable 0 a)
  linarith

lemma inj_continuous_k0 : Continuous k0 := by
  unfold k0; fun_prop

lemma inj_k0_lipschitz (x y : ℝ) : |k0 x - k0 y| ≤ |x - y| := by
  unfold k0
  have h := abs_abs_sub_abs_le_abs_sub (x - 1) (y - 1)
  rw [show x - 1 - (y - 1) = x - y by ring] at h
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le h ?_)
  rw [show (|x - 1| + 1) / 2 - (|y - 1| + 1) / 2 = (|x - 1| - |y - 1|) / 2 by ring, abs_div,
    abs_two]
  linarith [abs_nonneg (x - y)]

lemma inj_k0_le (x : ℝ) : k0 x ≤ |x| + 1 := by
  unfold k0
  have h := abs_sub x 1
  rw [abs_one] at h
  apply max_le <;> linarith [abs_nonneg x]

lemma inj_k0_le_four {x : ℝ} (h0 : 0 ≤ x) (h5 : x ≤ 5) : k0 x ≤ 4 := by
  unfold k0
  have : |x - 1| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  apply max_le <;> linarith

lemma inj_intervalIntegrable_k0_gPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (fun u => k0 (gPlus K u)) volume a b := by
  obtain ⟨R, hR⟩ := inj_supp_bounded hK
  have hmeas : Measurable fun u => k0 (gPlus K u) :=
    inj_continuous_k0.measurable.comp (inj_measurable_gPlus hK)
  refine IntegrableOn.intervalIntegrable (IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    hmeas.aestronglyMeasurable (2 * R + 1) (Filter.Eventually.of_forall fun u => ?_))
  have g1 := inj_gPlus_le_width hK u
  have g0 := (inj_arm_nonneg hK u).2.2.1
  have r1 := abs_le.1 (hR u)
  have r2 := abs_le.1 (hR (u + π))
  have k1 := inj_k0_le (gPlus K u)
  have k2 := inj_k0_nonneg (gPlus K u)
  rw [Real.norm_eq_abs, abs_of_nonneg k2]
  rw [abs_of_nonneg g0] at k1
  linarith

lemma inj_intervalIntegrable_abs_gPlus_sub {K K' : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    (hK' : IsConvexBody K') (a b : ℝ) :
    IntervalIntegrable (fun u => |gPlus K' u - gPlus K u|) volume a b := by
  obtain ⟨R, hR⟩ := inj_supp_bounded hK
  obtain ⟨R', hR'⟩ := inj_supp_bounded hK'
  have hmeas : Measurable fun u => |gPlus K' u - gPlus K u| :=
    continuous_abs.measurable.comp ((inj_measurable_gPlus hK').sub (inj_measurable_gPlus hK))
  refine IntegrableOn.intervalIntegrable (IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
    hmeas.aestronglyMeasurable (2 * R + 2 * R') (Filter.Eventually.of_forall fun u => ?_))
  have g1 := inj_gPlus_le_width hK u
  have g0 := (inj_arm_nonneg hK u).2.2.1
  have g1' := inj_gPlus_le_width hK' u
  have g0' := (inj_arm_nonneg hK' u).2.2.1
  have r1 := abs_le.1 (hR u)
  have r2 := abs_le.1 (hR (u + π))
  have r1' := abs_le.1 (hR' u)
  have r2' := abs_le.1 (hR' (u + π))
  rw [Real.norm_eq_abs, abs_abs, abs_le]
  constructor <;> linarith

/-- One step of the discrete inequality, in integrated form:
`σ_K(t) ≤ ∫_t^{t+δ} k₀(g_K⁺) + (C + 5) δ²` for `t ∈ {0} ∪ Θ_n`. -/
lemma inj_step_bound {C : ℝ} (hC : ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
      ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
        sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2)
    {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    sigmaAt K t ≤ (∫ u in t..(t + stepSize k), k0 (gPlus K u)) + (C + 5) * stepSize k ^ 2 := by
  have hKc : IsConvexBody K := hK.1.1.2.1
  have hδ := inj_stepSize_pos k
  have h1 := hC k K hK t ht
  obtain ⟨hmon, h5⟩ := lemma6_4_1 hK ht
  have hint : (k0 (gPlus K t) - 5 * stepSize k) * stepSize k ≤
      ∫ u in t..(t + stepSize k), k0 (gPlus K u) := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := t)
      (b := t + stepSize k) (f := fun _ => k0 (gPlus K t) - 5 * stepSize k)
      (g := fun u => k0 (gPlus K u)) (by linarith) intervalIntegrable_const
      (inj_intervalIntegrable_k0_gPlus hKc _ _) ?_
    · rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
      linarith
    · intro u hu
      obtain ⟨hu1, -, hu3⟩ := hmon u hu
      have hu2 := (hmon u hu).2.1
      have hlip := inj_k0_lipschitz (gPlus K u) (gPlus K t)
      have hg : |gPlus K u - gPlus K t| ≤ 5 * stepSize k := by
        rw [abs_le]; constructor <;> linarith
      linarith [(abs_le.1 hlip).1]
  nlinarith

/-- The discrete inequality summed over an interval `[a, b) ⊆ [0, π/2]`. -/
lemma inj_polygon_Ico_bound {C : ℝ} (hC : ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
      ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
        sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2) (hC0 : 0 ≤ C)
    {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ico a b)).toReal ≤
      (∫ u in a..b, k0 (gPlus K u)) + (8 + π / 2 * (C + 5)) * stepSize k := by
  have hKp := hK.1
  have hcap : IsCap K (π / 2) := hKp.1
  have hKc : IsConvexBody K := hcap.2.1
  have hδ := inj_stepSize_pos k
  have hn : ((2 ^ (k + 1) : ℕ) : ℝ) * stepSize k = π / 2 := by
    push_cast; exact inj_two_pow_mul_stepSize k
  set δ := stepSize k with hδdef
  set n := 2 ^ (k + 1) with hndef
  have hint := inj_intervalIntegrable_k0_gPlus hKc
  have hk04 : ∀ u ∈ Icc (0 : ℝ) (π / 2), k0 (gPlus K u) ≤ 4 := by
    intro u hu
    exact inj_k0_le_four (inj_arm_nonneg hKc u).2.2.1 ((lemma6_3_1 hK).2 u hu).2.2.1
  -- the sum over the grid
  have hsum : ∀ p m : ℕ, p ≤ m → m ≤ n →
      (sigma K (Ico (p * δ) (m * δ))).toReal ≤
        (∫ u in (p * δ)..(m * δ), k0 (gPlus K u)) + (m - p) * ((C + 5) * δ ^ 2) := by
    intro p m hpm hmn
    induction m, hpm using Nat.le_induction with
    | base => simp
    | succ m hpm ih =>
      have ih := ih (by omega)
      have hmδ : (m : ℝ) * δ ≤ ((m + 1 : ℕ) : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) hδ.le
      have hpδ : (p : ℝ) * δ ≤ m * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hpm) hδ.le
      have e1 : Ico ((p : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) =
          Ico ((p : ℝ) * δ) (m * δ) ∪ Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) :=
        (Ico_union_Ico_eq_Ico hpδ hmδ).symm
      have hm1 : (((m + 1 : ℕ) : ℝ) * δ) = m * δ + δ := by push_cast; ring
      -- the atom at `mδ`
      have hmΘ : (m : ℝ) * δ ∈ insert 0 ((rightAngleSet k).angles : Set ℝ) := by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · left; simp
        · right; exact inj_mem_angles.2 ⟨m, hm0, by omega, rfl⟩
      obtain ⟨-, hA1, -, hA3⟩ := inj_polygon_consecutive hKp (m := m) (by omega) rfl
      have hIoo : sigma K (Ioo ((m : ℝ) * δ) (m * δ + δ)) = 0 := by
        apply inj_sigma_Ioo_eq_zero hKc (by linarith) (q := vint K (m * δ) (m * δ + δ))
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | h1
        · exact hA1
        · exact (hA3 s ⟨h1, hs.2⟩).2.1
      have hstep : (sigma K (Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ))).toReal =
          sigmaAt K (m * δ) := by
        rw [hm1, ← Ioo_insert_left (by linarith), insert_eq,
          measure_union (disjoint_singleton_left.2 (fun h => lt_irrefl _ h.1)) measurableSet_Ioo,
          hIoo, add_zero, sigmaAt]
      have hs := inj_step_bound hC hK hmΘ
      rw [← hδdef] at hs
      rw [e1, measure_union Ico_disjoint_Ico_same measurableSet_Ico,
        ENNReal.toReal_add measure_Ico_lt_top.ne measure_Ico_lt_top.ne, hstep,
        ← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ) * δ) (hint _ _) (hint _ _),
        hm1]
      push_cast
      nlinarith
  -- rounding to the grid
  set p := ⌊a / δ⌋₊ with hp
  set q := ⌈b / δ⌉₊ with hq
  have hpa : (p : ℝ) * δ ≤ a := by
    have := Nat.floor_le (div_nonneg ha hδ.le)
    rw [← hp] at this
    calc (p : ℝ) * δ ≤ a / δ * δ := by gcongr
      _ = a := div_mul_cancel₀ a hδ.ne'
  have hpa' : a < (p : ℝ) * δ + δ := by
    have := Nat.lt_floor_add_one (a / δ)
    rw [← hp] at this
    calc a = a / δ * δ := (div_mul_cancel₀ a hδ.ne').symm
      _ < ((p : ℝ) + 1) * δ := by gcongr
      _ = p * δ + δ := by ring
  have hqb : b ≤ (q : ℝ) * δ := by
    have := Nat.le_ceil (b / δ)
    rw [← hq] at this
    calc b = b / δ * δ := (div_mul_cancel₀ b hδ.ne').symm
      _ ≤ q * δ := by gcongr
  have hqb' : (q : ℝ) * δ < b + δ := by
    have := Nat.ceil_lt_add_one (div_nonneg (ha.trans hab) hδ.le)
    rw [← hq] at this
    calc (q : ℝ) * δ < (b / δ + 1) * δ := by gcongr
      _ = b + δ := by rw [add_mul, div_mul_cancel₀ b hδ.ne', one_mul]
  have hqn : q ≤ n := by
    rw [hq]
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hδ, hn]; exact hb
  have hpq : p ≤ q := by
    have : (p : ℝ) * δ ≤ q * δ := hpa.trans (hab.trans hqb)
    exact_mod_cast le_of_mul_le_mul_right this hδ
  have hqπ : (q : ℝ) * δ ≤ π / 2 := by
    rw [← hn]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqn) hδ.le
  have hp0 : (0 : ℝ) ≤ p * δ := by positivity
  have h1 := hsum p q hpq hqn
  -- the endpoint pieces
  have hleft : ∫ u in (p * δ)..a, k0 (gPlus K u) ≤ 4 * δ := by
    have := intervalIntegral.integral_mono_on (μ := volume) hpa (hint _ _)
      (intervalIntegrable_const (c := (4 : ℝ)))
      (fun u hu => hk04 u ⟨hp0.trans hu.1, by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith
  have hright : ∫ u in b..(q * δ), k0 (gPlus K u) ≤ 4 * δ := by
    have := intervalIntegral.integral_mono_on (μ := volume) hqb (hint _ _)
      (intervalIntegrable_const (c := (4 : ℝ)))
      (fun u hu => hk04 u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith
  have hsplit : ∫ u in (p * δ)..(q * δ), k0 (gPlus K u) =
      (∫ u in (p * δ)..a, k0 (gPlus K u)) + (∫ u in a..b, k0 (gPlus K u)) +
        ∫ u in b..(q * δ), k0 (gPlus K u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmono : (sigma K (Ico a b)).toReal ≤ (sigma K (Ico ((p : ℝ) * δ) (q * δ))).toReal :=
    ENNReal.toReal_mono measure_Ico_lt_top.ne (measure_mono (Ico_subset_Ico hpa hqb))
  have hqp : ((q : ℝ) - p) * ((C + 5) * δ ^ 2) ≤ π / 2 * (C + 5) * δ := by
    have hqp' : ((q : ℝ) - p) ≤ n := by
      have : (q : ℝ) ≤ n := by exact_mod_cast hqn
      linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    have hC5 : 0 ≤ (C + 5) * δ ^ 2 := by positivity
    calc ((q : ℝ) - p) * ((C + 5) * δ ^ 2) ≤ n * ((C + 5) * δ ^ 2) :=
          mul_le_mul_of_nonneg_right hqp' hC5
      _ = ((n : ℝ) * δ) * (C + 5) * δ := by ring
      _ = π / 2 * (C + 5) * δ := by rw [hn]
  linarith

/-- The discrete inequality on an open interval `(a, b) ⊆ (-π/2, π/2]`. -/
lemma inj_polygon_Ioo_bound {C : ℝ} (hC : ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
      ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
        sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2) (hC0 : 0 ≤ C)
    {k : ℕ} {K : Set (ℝ × ℝ)} (hK : IsMaxPolygonCap (rightAngleSet k) K) {a b : ℝ}
    (ha : -(π / 2) ≤ a) (hab : max a 0 ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ioo a b)).toReal ≤
      (∫ u in (max a 0)..b, k0 (gPlus K u)) + (8 + π / 2 * (C + 5)) * stepSize k := by
  have hcap : IsCap K (π / 2) := hK.1.1
  have hKc : IsConvexBody K := hcap.2.1
  obtain ⟨-, hc2, hc3⟩ := inj_cap_consecutive hcap
  have h0 : sigma K (Ioo (-(π / 2)) 0) = 0 := by
    apply inj_sigma_Ioo_eq_zero hKc (by linarith [pi_pos]) (q := (supp K 0, 0))
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | h1
    · exact hc2
    · exact hc3 s ⟨h1, hs.2⟩
  have hsub : Ioo a b ⊆ Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b := by
    intro x hx
    by_cases hx0 : x < 0
    · left; exact ⟨by linarith [hx.1], hx0⟩
    · right; exact ⟨max_le hx.1.le (not_lt.1 hx0), hx.2⟩
  have hle : sigma K (Ioo a b) ≤ sigma K (Ico (max a 0) b) := by
    calc sigma K (Ioo a b) ≤ sigma K (Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b) := measure_mono hsub
      _ ≤ sigma K (Ioo (-(π / 2)) 0) + sigma K (Ico (max a 0) b) := measure_union_le _ _
      _ = sigma K (Ico (max a 0) b) := by rw [h0, zero_add]
  calc (sigma K (Ioo a b)).toReal ≤ (sigma K (Ico (max a 0) b)).toReal :=
        ENNReal.toReal_mono measure_Ico_lt_top.ne hle
    _ ≤ _ := inj_polygon_Ico_bound hC hC0 hK (le_max_right _ _) hab hb

/-- The limit inequality on an open interval `(a, b) ⊆ (-π/2, π/2]`. -/
lemma inj_limit_Ioo_bound {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) {a b : ℝ}
    (ha : -(π / 2) ≤ a) (hab : a < b) (hab' : max a 0 ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ioo a b)).toReal ≤ ∫ u in (max a 0)..b, k0 (gPlus K u) := by
  obtain ⟨hω, hcap, k, Ks, hk, hKs, hlim⟩ := hK
  have hKs' : ∀ i, IsMaxPolygonCap (rightAngleSet (k i)) (Ks i) := hKs
  obtain ⟨C, hC⟩ := theorem6_3_3
  have hC' : ∀ k : ℕ, ∀ K, IsMaxPolygonCap (rightAngleSet k) K →
      ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
        sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + max C 0 * stepSize k ^ 2 := by
    intro k K hK t ht
    have := hC k K hK t ht
    have : C * stepSize k ^ 2 ≤ max C 0 * stepSize k ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    linarith
  have hKc : IsConvexBody K := hcap.2.1
  have hKsc : ∀ i, IsConvexBody (Ks i) := fun i => (hKs' i).1.1.2.1
  have hsupp := inj_tendsto_supp hKsc hKc hlim
  set C₂ := 8 + π / 2 * (max C 0 + 5)
  set a' := max a 0 with ha'
  have ha'0 : 0 ≤ a' := le_max_right _ _
  -- the step sizes tend to zero
  have hδ : Tendsto (fun i => stepSize (k i)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun m : ℕ => stepSize m) atTop (𝓝 0) := by
      unfold stepSize
      have : Tendsto (fun m : ℕ => (2 : ℝ) ^ (m + 1)) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
      exact tendsto_const_nhds.div_atTop this
    exact h2.comp hk.tendsto_atTop
  -- the right-hand sides converge
  have hU : Tendsto (fun i => (∫ u in a'..b, k0 (gPlus (Ks i) u)) + C₂ * stepSize (k i)) atTop
      (𝓝 (∫ u in a'..b, k0 (gPlus K u))) := by
    have h1 : Tendsto (fun i => ∫ u in a'..b, k0 (gPlus (Ks i) u)) atTop
        (𝓝 (∫ u in a'..b, k0 (gPlus K u))) := by
      have hL := lemma6_4_2 (Θs := fun i => rightAngleSet (k i)) (fun i => rfl)
        (fun i => (hKs' i).1) hcap hlim
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hL
      rw [← intervalIntegral.integral_sub (inj_intervalIntegrable_k0_gPlus (hKsc i) _ _)
        (inj_intervalIntegrable_k0_gPlus hKc _ _)]
      calc ‖∫ u in a'..b, (k0 (gPlus (Ks i) u) - k0 (gPlus K u))‖
          ≤ ∫ u in a'..b, ‖k0 (gPlus (Ks i) u) - k0 (gPlus K u)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab'
        _ ≤ ∫ u in a'..b, |gPlus (Ks i) u - gPlus K u| := by
            apply intervalIntegral.integral_mono_on hab'
            · exact ((inj_intervalIntegrable_k0_gPlus (hKsc i) _ _).sub
                (inj_intervalIntegrable_k0_gPlus hKc _ _)).norm
            · exact inj_intervalIntegrable_abs_gPlus_sub hKc (hKsc i) _ _
            · intro u _
              rw [Real.norm_eq_abs]
              exact inj_k0_lipschitz _ _
        _ ≤ ∫ u in (0 : ℝ)..(π / 2), |gPlus (Ks i) u - gPlus K u| :=
            intervalIntegral.integral_mono_interval ha'0 hab' hb
              (Filter.Eventually.of_forall fun u => abs_nonneg _)
              (inj_intervalIntegrable_abs_gPlus_sub hKc (hKsc i) _ _)
    have h2 : Tendsto (fun i => C₂ * stepSize (k i)) atTop (𝓝 0) := by
      simpa using hδ.const_mul C₂
    simpa using h1.add h2
  -- the integrals of the support functions converge
  have hI : Tendsto (fun i => ∫ t in a..b, supp (Ks i) t) atTop (𝓝 (∫ t in a..b, supp K t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hd : Tendsto (fun i => hausdorffDist (Ks i) K * |b - a|) atTop (𝓝 0) := by
      simpa using hlim.mul_const |b - a|
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hd
    rw [← intervalIntegral.integral_sub ((inj_continuous_supp (hKsc i)).intervalIntegrable _ _)
      ((inj_continuous_supp hKc).intervalIntegrable _ _)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => by rw [Real.norm_eq_abs]; exact inj_abs_supp_sub_le (hKsc i) hKc t)
  -- the lower bounds `Φ(ε)`
  set Φ : ℝ → ℝ := fun ε => dot (vint K (b - ε) b) (vvec b) - dot (vint K a (a + ε)) (vvec a) +
    ∫ t in a..b, supp K t with hΦ
  have hΦle : ∀ ε, 0 < ε → ε < π → Φ ε ≤ ∫ u in a'..b, k0 (gPlus K u) := by
    intro ε hε0 hεπ
    have hΦi : Tendsto (fun i => dot (vint (Ks i) (b - ε) b) (vvec b) -
        dot (vint (Ks i) a (a + ε)) (vvec a) + ∫ t in a..b, supp (Ks i) t) atTop (𝓝 (Φ ε)) :=
      ((inj_tendsto_dot (inj_tendsto_vint hsupp _ _) tendsto_const_nhds).sub
        (inj_tendsto_dot (inj_tendsto_vint hsupp _ _) tendsto_const_nhds)).add hI
    refine le_of_tendsto_of_tendsto' hΦi hU (fun i => ?_)
    calc _ ≤ (sigma (Ks i) (Ioo a b)).toReal := by
          rw [inj_sigma_Ioo_toReal (hKsc i) hab]
          linarith [inj_vint_le_dot_vminus (hKsc i) b hε0 hεπ,
            inj_dot_vplus_le_vint (hKsc i) a hε0 hεπ]
      _ ≤ _ := inj_polygon_Ioo_bound hC' (le_max_right _ _) (hKs' i) ha hab' hb
  have hΦlim : Tendsto Φ (𝓝[>] 0) (𝓝 ((sigma K (Ioo a b)).toReal)) := by
    rw [inj_sigma_Ioo_toReal hKc hab]
    exact ((inj_tendsto_vint_left_dot hKc b).sub (inj_tendsto_vint_right_dot hKc a)).add
      tendsto_const_nhds
  exact le_of_tendsto hΦlim
    (by filter_upwards [inj_eventually_pos_lt_pi] with ε hε using hΦle ε hε.1 hε.2)

/-- **Theorem 6.4.3** (`thm:balanced-ineq-limit`). A balanced maximum cap satisfies
`σ_K ≤ k₀(g_K⁺(t)) dt` on `[0, π/2)`. -/
theorem theorem6_4_3 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) :
    (sigma K).restrict (Ico 0 (π / 2)) ≤
      (volume.restrict (Ico 0 (π / 2))).withDensity (fun t => ENNReal.ofReal (k0 (gPlus K t))) := by
  have hcap : IsCap K (π / 2) := hK.2.1
  have hKc : IsConvexBody K := hcap.2.1
  have hint := inj_intervalIntegrable_k0_gPlus hKc
  have hk0 : ∀ t, 0 ≤ k0 (gPlus K t) := fun t => inj_k0_nonneg _
  have hπ : (0 : ℝ) < π / 2 := by positivity
  -- integrals over intervals
  have hlin : ∀ x y : ℝ, x ≤ y → ∀ s : Set ℝ, (s = Ico x y ∨ s = Ioo x y) →
      ∫⁻ t in s, ENNReal.ofReal (k0 (gPlus K t)) =
        ENNReal.ofReal (∫ t in x..y, k0 (gPlus K t)) := by
    intro x y hxy s hs
    have hIoc : IntegrableOn (fun t => k0 (gPlus K t)) (Ioc x y) volume := (hint x y).1
    rw [intervalIntegral.integral_of_le hxy]
    rcases hs with rfl | rfl
    · rw [← integral_Ico_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal
        (hIoc.congr_set_ae Ico_ae_eq_Ioc) (Filter.Eventually.of_forall fun t => hk0 t)]
    · rw [integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal
        (hIoc.mono_set Ioo_subset_Ioc_self) (Filter.Eventually.of_forall fun t => hk0 t)]
  have : IsFiniteMeasure ((sigma K).restrict (Ico 0 (π / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have : IsFiniteMeasure ((volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (k0 (gPlus K t)))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlin 0 (π / 2) hπ.le _
      (Or.inl rfl)]
    exact ENNReal.ofReal_lt_top
  apply inj_measure_le_of_Ioo
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  set b' := min b (π / 2) with hb'
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'π : b' ≤ π / 2 := min_le_right _ _
  by_cases ha : a < 0
  · by_cases hb0 : 0 < b'
    · have e : Ioo a b ∩ Ico 0 (π / 2) = Ico 0 b' := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, hb', lt_min_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h3, h2, h4⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, h2⟩, h1, h3⟩
      rw [e, hlin 0 b' hb0.le _ (Or.inl rfl)]
      have h2 := inj_limit_Ioo_bound hK (a := -(π / 2)) le_rfl (by linarith)
        (by rw [max_eq_right (by linarith)]; exact hb0.le) hb'π
      rw [max_eq_right (by linarith)] at h2
      calc sigma K (Ico 0 b') ≤ sigma K (Ioo (-(π / 2)) b') :=
            measure_mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
        _ = ENNReal.ofReal (sigma K (Ioo (-(π / 2)) b')).toReal :=
            (ENNReal.ofReal_toReal measure_Ioo_lt_top.ne).symm
        _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..b', k0 (gPlus K t)) := ENNReal.ofReal_le_ofReal h2
    · have e : Ioo a b ∩ Ico 0 (π / 2) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h2⟩, h3, h4⟩
        have : x < b' := lt_min h2 h4
        linarith
      rw [e]; simp
  · rw [not_lt] at ha
    by_cases hab' : a < b'
    · have e : Ioo a b ∩ Ico 0 (π / 2) = Ioo a b' := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, hb', lt_min_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith, h3⟩
      rw [e, hlin a b' hab'.le _ (Or.inr rfl)]
      have h2 := inj_limit_Ioo_bound hK (a := a) (by linarith) hab'
        (by rw [max_eq_left ha]; exact hab'.le) hb'π
      rw [max_eq_left ha] at h2
      calc sigma K (Ioo a b') = ENNReal.ofReal (sigma K (Ioo a b')).toReal :=
            (ENNReal.ofReal_toReal measure_Ioo_lt_top.ne).symm
        _ ≤ ENNReal.ofReal (∫ t in a..b', k0 (gPlus K t)) := ENNReal.ofReal_le_ofReal h2
    · have e : Ioo a b ∩ Ico 0 (π / 2) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, h2⟩, _, h4⟩
        have : x < b' := lt_min h2 h4
        rw [not_lt] at hab'
        linarith
      rw [e]; simp

/-- **Corollary 6.4.4** (`cor:cap-nondegenerate`). A balanced maximum cap satisfies condition (1) of
the injectivity condition. -/
theorem corollary6_4_4 {K : Set (ℝ × ℝ)} (hK : IsBalancedMaxCap K (π / 2)) : InjCond1 K := by
  -- absolute continuity on `[0, π/2)`
  have hac : ∀ K', IsBalancedMaxCap K' (π / 2) →
      (sigma K').restrict (Ico 0 (π / 2)) ≪ volume.restrict (Ico 0 (π / 2)) := fun K' hK' =>
    (Measure.absolutelyContinuous_of_le (theorem6_4_3 hK')).trans
      (withDensity_absolutelyContinuous _ _)
  -- absolute continuity on `(π/2, π]`, by the mirror symmetry
  have hac2 : (sigma K).restrict (Ioc (π / 2) π) ≪ volume.restrict (Ioc (π / 2) π) := by
    have hm := hac _ (proposition3_5_1 hK)
    have hσ := proposition2_5_4_sigma hK.2.1
    set φ : ℝ → ℝ := fun s => π / 2 + π / 2 - s with hφ
    have hφm : Measurable φ := measurable_const.sub measurable_id
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    rw [Measure.restrict_apply hA] at hA0 ⊢
    have hBm : MeasurableSet (A ∩ Ioc (π / 2) π) := hA.inter measurableSet_Ioc
    have e1 : sigma K (A ∩ Ioc (π / 2) π) =
        sigma (mirrorCap K (π / 2)) (φ ⁻¹' (A ∩ Ioc (π / 2) π)) := by
      rw [hσ, Measure.map_apply hφm (hφm hBm)]
      congr 1
      ext x
      simp [hφ]
    have hsub : φ ⁻¹' (A ∩ Ioc (π / 2) π) ⊆ Ico 0 (π / 2) := by
      rintro x ⟨_, h1, h2⟩
      simp only [hφ] at h1 h2
      constructor <;> linarith
    have hvol : volume (φ ⁻¹' (A ∩ Ioc (π / 2) π)) = 0 := by
      have e2 : φ ⁻¹' (A ∩ Ioc (π / 2) π) =
          (fun x : ℝ => -1 * x) ⁻¹' ((fun y : ℝ => π + y) ⁻¹' (A ∩ Ioc (π / 2) π)) := by
        ext x
        simp only [mem_preimage, hφ]
        ring_nf
      rw [e2, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add, hA0, mul_zero]
    rw [e1]
    have h0 : (sigma (mirrorCap K (π / 2))).restrict (Ico 0 (π / 2))
        (φ ⁻¹' (A ∩ Ioc (π / 2) π)) = 0 := by
      apply hm
      rw [Measure.restrict_apply (hφm hBm)]
      exact measure_mono_null inter_subset_left hvol
    rwa [Measure.restrict_apply (hφm hBm), inter_eq_left.2 hsub] at h0
  -- the Radon–Nikodym theorem
  have hrn : ∀ {μ : Measure ℝ} {I : Set ℝ} [IsFiniteMeasure μ], μ ≪ volume.restrict I →
      ∃ r : ℝ → ℝ, Measurable r ∧ (∀ t, 0 ≤ r t) ∧
        μ = (volume.restrict I).withDensity (fun t => ENNReal.ofReal (r t)) := by
    intro μ I _ h
    refine ⟨fun t => (μ.rnDeriv (volume.restrict I) t).toReal,
      (Measure.measurable_rnDeriv _ _).ennreal_toReal, fun t => ENNReal.toReal_nonneg, ?_⟩
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ (volume.restrict I)] with t ht
    rw [ENNReal.ofReal_toReal ht.ne]
  have : IsFiniteMeasure ((sigma K).restrict (Ico 0 (π / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have : IsFiniteMeasure ((sigma K).restrict (Ioc (π / 2) π)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  obtain ⟨r, hr_meas, hr_nn, hr⟩ := hrn (hac K hK)
  obtain ⟨s', hs_meas, hs_nn, hs⟩ := hrn hac2
  refine ⟨r, fun x => s' (x + π / 2), hr_meas, hs_meas.comp (measurable_id.add_const _), hr_nn,
    fun x => hs_nn _, hr, ?_⟩
  simpa using hs

/-! ### Consequences of condition (1) -/

/-- Under condition (1), `σ_K` has no atom on `[0, π/2) ∪ (π/2, π]`. -/
lemma inj_sigma_singleton_of_injCond1 {K : Set (ℝ × ℝ)} (h1 : InjCond1 K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) : sigma K {t} = 0 := by
  obtain ⟨r, s, -, -, -, -, hr, hs⟩ := h1
  rcases ht with ht | ht
  · have e : sigma K {t} = (sigma K).restrict (Ico 0 (π / 2)) {t} := by
      rw [Measure.restrict_apply (measurableSet_singleton t), singleton_inter_of_mem ht]
    rw [e, hr]
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)
  · have e : sigma K {t} = (sigma K).restrict (Ioc (π / 2) π) {t} := by
      rw [Measure.restrict_apply (measurableSet_singleton t), singleton_inter_of_mem ht]
    rw [e, hs]
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    exact measure_mono_null inter_subset_left (Real.volume_singleton)

lemma inj_vplus_eq_vminus_of_injCond1 {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (h1 : InjCond1 K)
    {t : ℝ} (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) : vplus K t = vminus K t :=
  inj_vplus_eq_vminus_of_sigma hK (inj_sigma_singleton_of_injCond1 h1 ht)

/-- **Proposition 6.4.5** (`pro:cap-nondegenerate`). Under condition (1), `A_K⁺ = A_K⁻`,
`f_K⁺ = f_K⁻` on `[0, π/2)` and `C_K⁺ = C_K⁻`, `g_K⁺ = g_K⁻` on `(0, π/2]`. -/
theorem proposition6_4_5 {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    (∀ t ∈ Ico 0 (π / 2), aPlus K t = aMinus K t ∧ fPlus K t = fMinus K t) ∧
      ∀ t ∈ Ioc 0 (π / 2), cPlus K t = cMinus K t ∧ gPlus K t = gMinus K t := by
  have hKc : IsConvexBody K := hK.2.1
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have e := inj_vplus_eq_vminus_of_injCond1 hKc h1 (Or.inl ht)
    exact ⟨e, by rw [fPlus, fMinus, aPlus, aMinus, e]⟩
  · have e := inj_vplus_eq_vminus_of_injCond1 hKc h1 (t := t + π / 2)
      (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact ⟨e, by rw [gPlus, gMinus, cPlus, cMinus, e]⟩

/-- `A_K(t)` (Definition 6.4.1): the common value `A_K^±(t)` for `t < π/2`, and `A_K⁻(π/2)` at `π/2`;
that is, `A_K⁻` on `[0, π/2]` (Proposition 6.4.5). -/
noncomputable def aK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := aMinus K t
/-- `f_K(t)` (Definition 6.4.1): `f_K⁻` on `[0, π/2]`. -/
noncomputable def fK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := fMinus K t
/-- `C_K(t)` (Definition 6.4.1): the common value `C_K^±(t)` for `t > 0`, and `C_K⁺(0)` at `0`; that
is, `C_K⁺` on `[0, π/2]`. -/
noncomputable def cK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ × ℝ := cPlus K t
/-- `g_K(t)` (Definition 6.4.1): `g_K⁺` on `[0, π/2]`. -/
noncomputable def gK (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ := gPlus K t

/-- **Proposition 6.4.6** (`pro:cap-nondegenerate-continuity`) (1): under condition (1), `A_K`, `C_K`,
`f_K` and `g_K` are continuous on `[0, π/2]`. -/
theorem proposition6_4_6_continuous {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    ContinuousOn (aK K) (Icc 0 (π / 2)) ∧ ContinuousOn (cK K) (Icc 0 (π / 2)) ∧
      ContinuousOn (fK K) (Icc 0 (π / 2)) ∧ ContinuousOn (gK K) (Icc 0 (π / 2)) := by
  have hKc : IsConvexBody K := hK.2.1
  have hA : ContinuousOn (aK K) (Icc 0 (π / 2)) := by
    intro t ht
    have hl : ContinuousWithinAt (vminus K) (Iic t) t :=
      continuousWithinAt_Iio_iff_Iic.1 (tendsto_vminus_left hKc t)
    rcases eq_or_lt_of_le ht.2 with htπ | htπ
    · exact hl.mono (fun x hx => by rw [htπ]; exact hx.2)
    · have hr : ContinuousWithinAt (vminus K) (Ici t) t := by
        apply continuousWithinAt_Ioi_iff_Ici.1
        have := tendsto_vminus_right hKc t
        rwa [inj_vplus_eq_vminus_of_injCond1 hKc h1 (Or.inl ⟨ht.1, htπ⟩)] at this
      exact (continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩).continuousWithinAt
  have hC : ContinuousOn (cK K) (Icc 0 (π / 2)) := by
    intro t ht
    have hr : ContinuousWithinAt (vplus K) (Ici (t + π / 2)) (t + π / 2) :=
      continuousWithinAt_Ioi_iff_Ici.1 (tendsto_vplus_right hKc _)
    have hsh : Continuous fun x : ℝ => x + π / 2 := continuous_id.add continuous_const
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · have : ContinuousWithinAt (fun x => vplus K (x + π / 2)) (Ici t) t :=
        ContinuousWithinAt.comp (g := vplus K) (f := fun x : ℝ => x + π / 2) (x := t) hr
          hsh.continuousWithinAt (fun x hx => by simp only [mem_Ici] at hx ⊢; linarith)
      exact this.mono (fun x hx => by rw [← ht0]; exact hx.1)
    · have hl : ContinuousWithinAt (vplus K) (Iic (t + π / 2)) (t + π / 2) := by
        apply continuousWithinAt_Iio_iff_Iic.1
        have := tendsto_vplus_left hKc (t + π / 2)
        rwa [← inj_vplus_eq_vminus_of_injCond1 hKc h1
          (Or.inr ⟨by linarith, by linarith [ht.2]⟩)] at this
      have hc : ContinuousAt (vplus K) (t + π / 2) :=
        continuousAt_iff_continuous_left_right.2 ⟨hl, hr⟩
      exact (ContinuousAt.comp (g := vplus K) (f := fun x : ℝ => x + π / 2) (x := t) hc
        hsh.continuousAt).continuousWithinAt
  have hu : Continuous uvec := continuous_cos.prodMk continuous_sin
  have hv : Continuous vvec := (continuous_sin.neg).prodMk continuous_cos
  have hs : Continuous (supp K) := inj_continuous_supp hKc
  have hy : Continuous (outerCorner K) := by
    have e : outerCorner K = fun x => supp K x • uvec x + supp K (x + π / 2) • vvec x := by
      funext x; exact proposition2_2_2_outerCorner K x
    rw [e]
    exact (hs.smul hu).add ((hs.comp (continuous_id.add continuous_const)).smul hv)
  refine ⟨hA, hC, ?_, ?_⟩
  · have e : fK K = fun t => dot (outerCorner K t - aK K t) (vvec t) := rfl
    rw [e]
    have h1' : ContinuousOn (fun t => outerCorner K t - aK K t) (Icc 0 (π / 2)) :=
      hy.continuousOn.sub hA
    unfold dot
    exact ((continuous_fst.comp_continuousOn h1').mul (continuous_fst.comp hv).continuousOn).add
      ((continuous_snd.comp_continuousOn h1').mul (continuous_snd.comp hv).continuousOn)
  · have e : gK K = fun t => dot (outerCorner K t - cK K t) (uvec t) := rfl
    rw [e]
    have h1' : ContinuousOn (fun t => outerCorner K t - cK K t) (Icc 0 (π / 2)) :=
      hy.continuousOn.sub hC
    unfold dot
    exact ((continuous_fst.comp_continuousOn h1').mul (continuous_fst.comp hu).continuousOn).add
      ((continuous_snd.comp_continuousOn h1').mul (continuous_snd.comp hu).continuousOn)

/-- **Proposition 6.4.6** (2): under condition (1), `x_K` and `y_K` are continuously differentiable on
`[0, π/2]` with `x_K' = -(f_K - 1) u_t + (g_K - 1) v_t` and `y_K' = -f_K u_t + g_K v_t`. -/
theorem proposition6_4_6_deriv {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) (h1 : InjCond1 K) :
    ContDiffOn ℝ 1 (innerCorner K) (Icc 0 (π / 2)) ∧ ContDiffOn ℝ 1 (outerCorner K) (Icc 0 (π / 2)) ∧
      ∀ t ∈ Icc 0 (π / 2),
        HasDerivWithinAt (innerCorner K) (-(fK K t - 1) • uvec t + (gK K t - 1) • vvec t)
            (Icc 0 (π / 2)) t ∧
          HasDerivWithinAt (outerCorner K) (-fK K t • uvec t + gK K t • vvec t) (Icc 0 (π / 2)) t := by
  have hKc : IsConvexBody K := hK.2.1
  obtain ⟨h5a, h5c⟩ := proposition6_4_5 hK h1
  have hderiv : ∀ t ∈ Icc 0 (π / 2),
      HasDerivWithinAt (innerCorner K) (-(fK K t - 1) • uvec t + (gK K t - 1) • vvec t)
          (Icc 0 (π / 2)) t ∧
        HasDerivWithinAt (outerCorner K) (-fK K t • uvec t + gK K t • vvec t)
          (Icc 0 (π / 2)) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with htπ | htπ
    · have ht0 : 0 < t := by rw [htπ]; positivity
      have hl := theorem6_2_3_left hK ⟨ht0, ht.2⟩
      have hg : gK K t = gMinus K t := (h5c t ⟨ht0, ht.2⟩).2
      have hsub : Icc 0 (π / 2) ⊆ Iic t := fun x hx => by rw [htπ]; exact hx.2
      rw [show fK K t = fMinus K t from rfl, hg]
      exact ⟨hl.2.mono hsub, hl.1.mono hsub⟩
    · have hr := theorem6_2_3_right hK ⟨ht.1, htπ⟩
      have hf : fK K t = fPlus K t := (h5a t ⟨ht.1, htπ⟩).2.symm
      have hsub : Icc 0 (π / 2) ⊆ Ici t ∨ 0 < t := by
        rcases eq_or_lt_of_le ht.1 with ht0 | ht0
        · left; intro x hx; rw [← ht0]; exact hx.1
        · right; exact ht0
      rcases hsub with hsub | ht0
      · rw [hf, show gK K t = gPlus K t from rfl]
        exact ⟨hr.2.mono hsub, hr.1.mono hsub⟩
      · have hl := theorem6_2_3_left hK ⟨ht0, ht.2⟩
        have hg : gPlus K t = gMinus K t := (h5c t ⟨ht0, ht.2⟩).2
        have hf' : fPlus K t = fMinus K t := (h5a t ⟨ht.1, htπ⟩).2
        rw [← hf', ← hg] at hl
        rw [hf, show gK K t = gPlus K t from rfl]
        have hy := hr.1.union hl.1
        have hx := hr.2.union hl.2
        rw [Ici_union_Iic, hasDerivWithinAt_univ] at hy hx
        exact ⟨hx.hasDerivWithinAt, hy.hasDerivWithinAt⟩
  have hcont := proposition6_4_6_continuous hK h1
  have hu : Continuous uvec := continuous_cos.prodMk continuous_sin
  have hv : Continuous vvec := (continuous_sin.neg).prodMk continuous_cos
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) (π / 2)) := uniqueDiffOn_Icc (by positivity)
  refine ⟨?_, ?_, hderiv⟩
  · rw [contDiffOn_one_iff_derivWithin hU]
    refine ⟨fun t ht => (hderiv t ht).1.differentiableWithinAt, ?_⟩
    have hc : ContinuousOn (fun t => -(fK K t - 1) • uvec t + (gK K t - 1) • vvec t)
        (Icc 0 (π / 2)) :=
      (((hcont.2.2.1.sub continuousOn_const).neg).smul hu.continuousOn).add
        ((hcont.2.2.2.sub continuousOn_const).smul hv.continuousOn)
    exact hc.congr fun t ht => (hderiv t ht).1.derivWithin (hU t ht)
  · rw [contDiffOn_one_iff_derivWithin hU]
    refine ⟨fun t ht => (hderiv t ht).2.differentiableWithinAt, ?_⟩
    have hc : ContinuousOn (fun t => -fK K t • uvec t + gK K t • vvec t) (Icc 0 (π / 2)) :=
      ((hcont.2.2.1.neg).smul hu.continuousOn).add (hcont.2.2.2.smul hv.continuousOn)
    exact hc.congr fun t ht => (hderiv t ht).2.derivWithin (hU t ht)

end MovingSofa
