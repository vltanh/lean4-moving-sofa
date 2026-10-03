module

public import SofaUniqueness.PolygonMeasureBounds
public import SofaUniqueness.CurvatureRegularity

/-!
# Curvature domination from arbitrary polygon approximations

The hypotheses are convergence of polygon caps and an integrated inequality
with a vanishing total error. No maximum-polygon or balanced-cap predicate is
used. Supporting-line intersections furnish lower bounds on open-interval
curvature masses, so no absence of endpoint atoms is assumed in the passage
to the limit. The interval comparison then yields domination on [0,pi/2).

Uncompiled source. No admissions or decision tactics.
-/

@[expose] public section
noncomputable section

open Set Real Filter Topology MeasureTheory MovingSofa

namespace SofaUniqueness

/-- L1 continuity of the arms implies convergence of k0-arm integrals on each
subinterval, without pointwise differentiability of the limiting support. -/
theorem k0_integral_tendsto {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ n, IsPolygonCap (Θs n) (Ks n)) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hlim : HausdorffTendsto Ks K)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    Tendsto (fun n => ∫ u in a..b, k0 (gPlus (Ks n) u)) atTop
      (𝓝 (∫ u in a..b, k0 (gPlus K u))) := by
  have hc := hK.2.1
  have hcs : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.2.1
  have hL := lemma6_4_2 hKs hK hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL
  rw [← intervalIntegral.integral_sub (inj_intervalIntegrable_k0_gPlus (hcs n) _ _)
    (inj_intervalIntegrable_k0_gPlus hc _ _)]
  calc
    ‖∫ u in a..b, (k0 (gPlus (Ks n) u) - k0 (gPlus K u))‖
        ≤ ∫ u in a..b, ‖k0 (gPlus (Ks n) u) - k0 (gPlus K u)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u in a..b, |gPlus (Ks n) u - gPlus K u| := by
      apply intervalIntegral.integral_mono_on hab
      · exact ((inj_intervalIntegrable_k0_gPlus (hcs n) _ _).sub
          (inj_intervalIntegrable_k0_gPlus hc _ _)).norm
      · exact inj_intervalIntegrable_abs_gPlus_sub hc (hcs n) _ _
      · intro u _
        rw [Real.norm_eq_abs]
        exact inj_k0_lipschitz _ _
    _ ≤ ∫ u in (0 : ℝ)..(π / 2), |gPlus (Ks n) u - gPlus K u| :=
      intervalIntegral.integral_mono_interval ha hab hb
        (Eventually.of_forall fun u => abs_nonneg _)
        (inj_intervalIntegrable_abs_gPlus_sub hc (hcs n) _ _)

/-- Upper support integrals are continuous under Hausdorff convergence. -/
theorem support_integral_tendsto {Ks : ℕ → Set (ℝ × ℝ)} {K : Set (ℝ × ℝ)}
    (hKs : ∀ n, IsConvexBody (Ks n)) (hK : IsConvexBody K)
    (hlim : HausdorffTendsto Ks K) (a b : ℝ) :
    Tendsto (fun n => ∫ t in a..b, supp (Ks n) t) atTop
      (𝓝 (∫ t in a..b, supp K t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hd : Tendsto (fun n => hausdorffDist (Ks n) K * |b - a|) atTop (𝓝 0) := by
    simpa using hlim.mul_const |b - a|
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hd
  rw [← intervalIntegral.integral_sub ((inj_continuous_supp (hKs n)).intervalIntegrable _ _)
    ((inj_continuous_supp hK).intervalIntegrable _ _)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => by rw [Real.norm_eq_abs]; exact inj_abs_supp_sub_le (hKs n) hK t)

/-- The integrated limit inequality includes intervals starting strictly below
zero. This is what later excludes a curvature atom at zero. -/
theorem curvature_Ioo_limit {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ n, IsPolygonCap (Θs n) (Ks n)) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hlim : HausdorffTendsto Ks K)
    (error : ℕ → ℝ) (herr : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n a b, -(π / 2) ≤ a → a < b → max a 0 ≤ b → b ≤ π / 2 →
      (sigma (Ks n) (Ioo a b)).toReal ≤
        (∫ u in (max a 0)..b, k0 (gPlus (Ks n) u)) + error n)
    {a b : ℝ} (ha : -(π / 2) ≤ a) (hab : a < b)
    (hab' : max a 0 ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ioo a b)).toReal ≤ ∫ u in (max a 0)..b, k0 (gPlus K u) := by
  have hc := hK.2.1
  have hcs : ∀ n, IsConvexBody (Ks n) := fun n => (hKs n).1.2.1
  have hsupp := inj_tendsto_supp hcs hc hlim
  have hU : Tendsto (fun n => (∫ u in (max a 0)..b, k0 (gPlus (Ks n) u)) + error n)
      atTop (𝓝 (∫ u in (max a 0)..b, k0 (gPlus K u))) := by
    simpa using (k0_integral_tendsto hKs hK hlim (le_max_right _ _) hab' hb).add herr
  have hI := support_integral_tendsto hcs hc hlim a b
  let Φ : ℝ → ℝ := fun ε => dot (vint K (b - ε) b) (vvec b) -
    dot (vint K a (a + ε)) (vvec a) + ∫ t in a..b, supp K t
  have hΦle : ∀ ε, 0 < ε → ε < π → Φ ε ≤ ∫ u in (max a 0)..b, k0 (gPlus K u) := by
    intro ε hε0 hεπ
    have hΦn : Tendsto (fun n => dot (vint (Ks n) (b - ε) b) (vvec b) -
        dot (vint (Ks n) a (a + ε)) (vvec a) + ∫ t in a..b, supp (Ks n) t)
        atTop (𝓝 (Φ ε)) :=
      ((inj_tendsto_dot (inj_tendsto_vint hsupp _ _) tendsto_const_nhds).sub
        (inj_tendsto_dot (inj_tendsto_vint hsupp _ _) tendsto_const_nhds)).add hI
    apply le_of_tendsto_of_tendsto' hΦn hU
    intro n
    calc
      _ ≤ (sigma (Ks n) (Ioo a b)).toReal := by
        rw [inj_sigma_Ioo_toReal (hcs n) hab]
        linarith [inj_vint_le_dot_vminus (hcs n) b hε0 hεπ,
          inj_dot_vplus_le_vint (hcs n) a hε0 hεπ]
      _ ≤ _ := hbound n a b ha hab hab' hb
  have hΦlim : Tendsto Φ (𝓝[>] 0) (𝓝 ((sigma K (Ioo a b)).toReal)) := by
    rw [inj_sigma_Ioo_toReal hc hab]
    exact ((inj_tendsto_vint_left_dot hc b).sub (inj_tendsto_vint_right_dot hc a)).add
      tendsto_const_nhds
  apply le_of_tendsto hΦlim
  filter_upwards [inj_eventually_pos_lt_pi] with ε hε
  exact hΦle ε hε.1 hε.2

/-- Open-interval mass bounds imply the endpoint-safe restricted measure
inequality. The derivation explicitly includes zero and excludes only the top. -/
theorem firstCurvature_of_Ioo {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hbound : ∀ a b, -(π / 2) ≤ a → a < b → max a 0 ≤ b → b ≤ π / 2 →
      (sigma K (Ioo a b)).toReal ≤ ∫ u in (max a 0)..b, k0 (gPlus K u)) :
    FirstCurvatureBound K := by
  have hc := hK.2.1
  have hint := inj_intervalIntegrable_k0_gPlus hc
  have hk0 : ∀ t, 0 ≤ k0 (gPlus K t) := fun t => inj_k0_nonneg _
  have hπ : (0 : ℝ) < π / 2 := by positivity
  have hlin : ∀ x y : ℝ, x ≤ y → ∀ s : Set ℝ, (s = Ico x y ∨ s = Ioo x y) →
      ∫⁻ t in s, ENNReal.ofReal (k0 (gPlus K t)) =
        ENNReal.ofReal (∫ t in x..y, k0 (gPlus K t)) := by
    intro x y hxy s hs
    have hIoc : IntegrableOn (fun t => k0 (gPlus K t)) (Ioc x y) volume := (hint x y).1
    rw [intervalIntegral.integral_of_le hxy]
    rcases hs with rfl | rfl
    · rw [← integral_Ico_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal
        (hIoc.congr_set_ae Ico_ae_eq_Ioc) (Eventually.of_forall fun t => hk0 t)]
    · rw [integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal
        (hIoc.mono_set Ioo_subset_Ioc_self) (Eventually.of_forall fun t => hk0 t)]
  have : IsFiniteMeasure ((sigma K).restrict (Ico 0 (π / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have : IsFiniteMeasure ((volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (k0 (gPlus K t)))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      hlin 0 (π / 2) hπ.le _ (Or.inl rfl)]
    exact ENNReal.ofReal_lt_top
  apply inj_measure_le_of_Ioo
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  let b' := min b (π / 2)
  have hb'b : b' ≤ b := min_le_left _ _
  have hb'π : b' ≤ π / 2 := min_le_right _ _
  by_cases ha : a < 0
  · by_cases hb0 : 0 < b'
    · have heq : Ioo a b ∩ Ico 0 (π / 2) = Ico 0 b' := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, b', lt_min_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          exact ⟨h3, h2, h4⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨by linarith, h2⟩, h1, h3⟩
      rw [heq, hlin 0 b' hb0.le _ (Or.inl rfl)]
      have h := hbound (-(π / 2)) b' le_rfl (by linarith)
        (by rw [max_eq_right (by linarith)]; exact hb0.le) hb'π
      rw [max_eq_right (by linarith)] at h
      calc
        sigma K (Ico 0 b') ≤ sigma K (Ioo (-(π / 2)) b') :=
          measure_mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
        _ = ENNReal.ofReal (sigma K (Ioo (-(π / 2)) b')).toReal :=
          (ENNReal.ofReal_toReal measure_Ioo_lt_top.ne).symm
        _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..b', k0 (gPlus K t)) := ENNReal.ofReal_le_ofReal h
    · have heq : Ioo a b ∩ Ico 0 (π / 2) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, h2⟩, h3, h4⟩
        have : x < b' := lt_min h2 h4
        linarith
      rw [heq]
      simp
  · have ha0 := not_lt.mp ha
    by_cases hab' : a < b'
    · have heq : Ioo a b ∩ Ico 0 (π / 2) = Ioo a b' := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, b', lt_min_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, by linarith, h3⟩
      rw [heq, hlin a b' hab'.le _ (Or.inr rfl)]
      have h := hbound a b' (by linarith) hab'
        (by rw [max_eq_left ha0]; exact hab'.le) hb'π
      rw [max_eq_left ha0] at h
      calc
        sigma K (Ioo a b') = ENNReal.ofReal (sigma K (Ioo a b')).toReal :=
          (ENNReal.ofReal_toReal measure_Ioo_lt_top.ne).symm
        _ ≤ ENNReal.ofReal (∫ t in a..b', k0 (gPlus K t)) := ENNReal.ofReal_le_ofReal h
    · have heq : Ioo a b ∩ Ico 0 (π / 2) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioo, mem_Ico, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, h2⟩, _, h4⟩
        have : x < b' := lt_min h2 h4
        linarith
      rw [heq]
      simp

/-- Reusable limiting theorem for any convergent polygon sequence with a
vanishing total integrated error. -/
theorem firstCurvature_of_polygon_errors {Θs : ℕ → AngleSet} {Ks : ℕ → Set (ℝ × ℝ)}
    (hKs : ∀ n, IsPolygonCap (Θs n) (Ks n)) {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hlim : HausdorffTendsto Ks K)
    (error : ℕ → ℝ) (herr : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n a b, -(π / 2) ≤ a → a < b → max a 0 ≤ b → b ≤ π / 2 →
      (sigma (Ks n) (Ioo a b)).toReal ≤
        (∫ u in (max a 0)..b, k0 (gPlus (Ks n) u)) + error n) :
    FirstCurvatureBound K := by
  apply firstCurvature_of_Ioo hK
  intro a b ha hab hab' hb
  exact curvature_Ioo_limit hKs hK hlim error herr hbound ha hab hab' hb

end SofaUniqueness
