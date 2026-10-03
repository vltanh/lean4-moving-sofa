module

public import MovingSofaOptimality.Injectivity.BoundingArms
public import MovingSofaOptimality.Injectivity.LimitIneq
public import MovingSofaOptimality.Injectivity.DiscreteIneq
public import MovingSofaUniqueness.Variation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Proposition 3: every maximizing right-angle cap satisfies the injectivity condition

The variation bounds give curvature bounds for the selected polygons, which pass to the limit cap:
the surface area measure of a maximizing cap is dominated as in inequality (16) of note 20
(`curvature_of_maximal_positive`). Comparing the arm functions with the lower sequence of Baek's
Lemma 6.5.5 then gives the injectivity condition of Baek's Chapter 6
(`injectivity_of_curvature`).
-/

@[expose] public section
noncomputable section

/-!
## Regularity and integrated arm bounds without balancedness

The hypotheses are the two measure inequalities themselves. The paper's
balanced-cap hypothesis is not used. In particular the endpoints 0 and pi are
included in the restricted measures; the possible atom at pi/2 is excluded.

The second arm identity is derived directly, so reflection of a selected
maximizer and an unproved mirrored density bound are unnecessary.
-/

section

open Real Set MeasureTheory Filter MovingSofaOptimality

namespace MovingSofaUniqueness

def FirstCurvatureBound (K : Set (ℝ × ℝ)) : Prop :=
  (sigma K).restrict (Ico 0 (π / 2)) ≤
    (volume.restrict (Ico 0 (π / 2))).withDensity
      (fun t => ENNReal.ofReal (k0 (gPlus K t)))

def SecondCurvatureBound (K : Set (ℝ × ℝ)) : Prop :=
  (sigma K).restrict (Ioc (π / 2) π) ≤
    (volume.restrict (Ioc (π / 2) π)).withDensity
      (fun t => ENNReal.ofReal (k0 (fMinus K (t - π / 2))))

/-- Domination by a density gives both absolutely continuous curvature pieces. -/
theorem injCond1_of_curvature {K : Set (ℝ × ℝ)}
    (hfirst : FirstCurvatureBound K) (hsecond : SecondCurvatureBound K) : InjCond1 K := by
  have h1 : (sigma K).restrict (Ico 0 (π / 2)) ≪ volume.restrict (Ico 0 (π / 2)) :=
    (Measure.absolutelyContinuous_of_le hfirst).trans (withDensity_absolutelyContinuous _ _)
  have h2 : (sigma K).restrict (Ioc (π / 2) π) ≪ volume.restrict (Ioc (π / 2) π) :=
    (Measure.absolutelyContinuous_of_le hsecond).trans (withDensity_absolutelyContinuous _ _)
  have hrn : ∀ {μ : Measure ℝ} {J : Set ℝ} [IsFiniteMeasure μ], μ ≪ volume.restrict J →
      ∃ r : ℝ → ℝ, Measurable r ∧ (∀ t, 0 ≤ r t) ∧
        μ = (volume.restrict J).withDensity (fun t => ENNReal.ofReal (r t)) := by
    intro μ J _ h
    refine ⟨fun t => (μ.rnDeriv (volume.restrict J) t).toReal,
      (Measure.measurable_rnDeriv _ _).ennreal_toReal,
      fun t => ENNReal.toReal_nonneg, ?_⟩
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ (volume.restrict J)] with t ht
    rw [ENNReal.ofReal_toReal ht.ne]
  have : IsFiniteMeasure ((sigma K).restrict (Ico 0 (π / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have : IsFiniteMeasure ((sigma K).restrict (Ioc (π / 2) π)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  obtain ⟨r, hrm, hr0, hr⟩ := hrn h1
  obtain ⟨s, hsm, hs0, hs⟩ := hrn h2
  refine ⟨r, fun t => s (t + π / 2), hrm,
    hsm.comp (measurable_id.add_const _), hr0, fun t => hs0 _, hr, ?_⟩
  simpa using hs

/-- Convert a restricted measure inequality into its real interval-integral bound. -/
theorem interval_mass_le_integral {μ : Measure ℝ} {J : Set ℝ} {k : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hsub : Ioc a b ⊆ J)
    (h : μ.restrict J ≤ (volume.restrict J).withDensity (fun t => ENNReal.ofReal (k t)))
    (hk : IntervalIntegrable k volume a b) (hk0 : ∀ t, 0 ≤ k t) :
    (μ (Ioc a b)).toReal ≤ ∫ t in a..b, k t := by
  have hi := Measure.le_iff'.1 h (Ioc a b)
  rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 hsub,
    withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 hsub, ← ofReal_integral_eq_lintegral_ofReal hk.1
      (Filter.Eventually.of_forall hk0), ← intervalIntegral.integral_of_le hab] at hi
  exact ENNReal.toReal_le_of_le_ofReal
    (intervalIntegral.integral_nonneg hab fun t _ => hk0 t) hi

/-- Integral of the first arm, before replacing its endpoint convention. -/
theorem integral_fPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    (∫ t in a..b, fPlus K t) =
      (∫ t in (a + π / 2)..(b + π / 2), supp K t) - (supp K b - supp K a) := by
  have hh : IntervalIntegrable (fun t => supp K (t + π / 2)) volume a b :=
    ((inj_continuous_supp hK).comp
      (continuous_id.add (continuous_const (y := π / 2)))).intervalIntegrable a b
  have hd : IntervalIntegrable (fun t => dot (vplus K t) (vvec t)) volume a b := by
    simpa only [add_zero] using inj_intervalIntegrable_dvplus hK 0 a b
  have e : fPlus K = fun t => supp K (t + π / 2) - dot (vplus K t) (vvec t) :=
    funext (inj_fPlus_eq K)
  rw [e, intervalIntegral.integral_sub hh hd,
    intervalIntegral.integral_comp_add_right (supp K), ← inj_supp_sub_supp hK a b]

/-- Integrated second-arm identity, valid for arbitrary convex bodies. -/
theorem gPlus_sub_gPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) {a b : ℝ} (hab : a ≤ b) :
    gPlus K b - gPlus K a =
      (sigma K (Ioc (a + π / 2) (b + π / 2))).toReal - ∫ t in a..b, fPlus K t := by
  have hs : (sigma K (Ioc (a + π / 2) (b + π / 2))).toReal =
      dot (vplus K (b + π / 2)) (vvec (b + π / 2)) -
        dot (vplus K (a + π / 2)) (vvec (a + π / 2)) +
        ∫ t in (a + π / 2)..(b + π / 2), supp K t := by
    rw [sigma_Ioc hK, ENNReal.toReal_ofReal
      (sub_nonneg.2 (monotone_sigmaFun hK (by linarith)))]
    have hi := intervalIntegral.integral_interval_sub_left
      ((inj_continuous_supp hK).intervalIntegrable (μ := volume) 0 (b + π / 2))
      ((inj_continuous_supp hK).intervalIntegrable 0 (a + π / 2))
    simp only [sigmaFun]
    linarith
  rw [inj_gPlus_eq, inj_gPlus_eq, hs, integral_fPlus hK]
  ring

/-- The two first-arm endpoint conventions agree in integrals over the cap interval. -/
theorem integral_fPlus_eq_fK {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    (∫ t in a..b, fPlus K t) = ∫ t in a..b, fK K t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact ((proposition6_4_5 hK h1).1 t ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩).2

/-- The bottom-left endpoint fixes the terminal value of the second arm. -/
theorem gK_end {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) : gK K (π / 2) = 1 := by
  have h := inj_fK_zero (proposition2_5_4_isCap hK)
  have he := (proposition6_2_2 (K := K) (t := 0)).2.1
  change fMinus (mirrorCap K (π / 2)) 0 = 1 at h
  have h' : gPlus K (π / 2) = 1 := by simpa only [sub_zero] using he.symm.trans h
  exact h'

/-- Integrated lower bound for the first arm on the endpoint-safe half interval. -/
theorem first_arm_integral_lower {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) (hbound : FirstCurvatureBound K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2)) :
    (∫ u in (0 : ℝ)..t, m0 (gK K u)) ≤ fK K t - 1 := by
  have hsub : Ioc 0 t ⊆ Ico 0 (π / 2) :=
    fun u hu => ⟨hu.1.le, hu.2.trans_lt ht.2⟩
  have hb := interval_mass_le_integral ht.1 hsub hbound
    (inj_intervalIntegrable_k0_gPlus hK.2.1 0 t) (fun u => inj_k0_nonneg _)
  have he := inj_fPlus_sub_fPlus hK.2.1 ht.1
  have hf (u : ℝ) (hu : u ∈ Ico 0 (π / 2)) : fPlus K u = fMinus K u :=
    ((proposition6_4_5 hK h1).1 u hu).2
  rw [hf t ht, hf 0 ⟨le_rfl, by positivity⟩] at he
  change fK K t - fK K 0 = _ at he
  rw [inj_fK_zero hK] at he
  have hi : (∫ u in (0 : ℝ)..t, m0 (gK K u)) =
      (∫ u in (0 : ℝ)..t, gPlus K u) - ∫ u in (0 : ℝ)..t, k0 (gPlus K u) := by
    simp only [m0, gK]
    exact intervalIntegral.integral_sub (inj_intervalIntegrable_gPlus hK.2.1 0 t)
      (inj_intervalIntegrable_k0_gPlus hK.2.1 0 t)
  linarith

/-- Integrated lower bound for the second arm, obtained from the second curvature piece. -/
theorem second_arm_integral_lower {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) (hbound : SecondCurvatureBound K) {t : ℝ}
    (ht : t ∈ Ioc 0 (π / 2)) :
    (∫ u in t..(π / 2), m0 (fK K u)) ≤ gK K t - 1 := by
  have hfc := (proposition6_4_6_continuous hK h1).2.2.1
  have hfint : IntervalIntegrable (fK K) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.2]
    exact hfc.mono (Icc_subset_Icc ht.1.le le_rfl)
  have hkint : IntervalIntegrable (fun u => k0 (fK K u)) volume t (π / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.2]
    exact inj_continuous_k0.comp_continuousOn
      (hfc.mono (Icc_subset_Icc ht.1.le le_rfl))
  have hshift : IntervalIntegrable (fun u => k0 (fMinus K (u - π / 2)))
      volume (t + π / 2) π := by
    apply ContinuousOn.intervalIntegrable
    apply inj_continuous_k0.comp_continuousOn
    apply hfc.comp (continuous_id.sub continuous_const).continuousOn
    intro u hu
    rw [uIcc_of_le (by linarith [ht.2])] at hu
    show u - π / 2 ∈ Icc 0 (π / 2)
    constructor <;> linarith [hu.1, hu.2, ht.1]
  have hsub : Ioc (t + π / 2) π ⊆ Ioc (π / 2) π := by
    intro u hu
    exact ⟨by linarith [hu.1, ht.1], hu.2⟩
  have hb := interval_mass_le_integral (by linarith [ht.2]) hsub hbound
    hshift (fun u => inj_k0_nonneg _)
  change (sigma K (Ioc (t + π / 2) π)).toReal ≤
    ∫ u in (t + π / 2)..π, k0 (fK K (u - π / 2)) at hb
  rw [intervalIntegral.integral_comp_sub_right (fun u => k0 (fK K u)),
    add_sub_cancel_right, show π - π / 2 = π / 2 by ring] at hb
  have he := gPlus_sub_gPlus hK.2.1 ht.2
  rw [show π / 2 + π / 2 = π by ring,
    integral_fPlus_eq_fK hK h1 ht.1.le ht.2 le_rfl] at he
  change gK K (π / 2) - gK K t = _ at he
  rw [gK_end hK] at he
  have hi : (∫ u in t..(π / 2), m0 (fK K u)) =
      (∫ u in t..(π / 2), fK K u) - ∫ u in t..(π / 2), k0 (fK K u) := by
    simp only [m0]
    exact intervalIntegral.integral_sub hfint hkint
  linarith

end MovingSofaUniqueness

end

/-!
## Cellwise arm control without a maximal-polygon assumption

The old Lemma 6.4.1 uses maximality only to obtain the fixed diameter bound 5.
Here the same geometric conclusion is stated for any polygon cap with an
explicit diameter bound D. This is the hypothesis actually available for
selected approximations of a specified cap.

No assertion that penalized maximizers are balanced is made. The parameter
D need not be the sharp Euclidean diameter; any nonnegative upper bound works.
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The tangential projection is bounded below by any Euclidean norm bound. -/
theorem neg_bound_le_dot_vvec {w : ℝ × ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hw : norm2 w ≤ D) (t : ℝ) : -D ≤ dot w (vvec t) := by
  have hww : dot w w ≤ D ^ 2 := by
    have h := (Real.sqrt_le_left hD).mp hw
    exact h
  have he := inj_dot_self_eq w t
  nlinarith [sq_nonneg (dot w (uvec t))]

/-- Both the within-cell monotonicity and the quantitative endpoint estimate
hold for arbitrary polygon caps under the stated diameter bound. -/
theorem polygon_arm_cell {k : ℕ} {K : Set (ℝ × ℝ)}
    (hKp : IsPolygonCap (rightAngleSet k) K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ)) :
    (∀ t' ∈ Ioo t (t + stepSize k), gPlus K t' ≤ gPlus K t ∧
      gPlus K t' = gMinus K t' ∧ gMinus K (t + stepSize k) ≤ gMinus K t') ∧
      gPlus K t - gMinus K (t + stepSize k) ≤ D * stepSize k := by
  have hKc : IsConvexBody K := hKp.1.2.1
  have hδ := inj_stepSize_pos k
  have hn := inj_two_pow_mul_stepSize k
  obtain ⟨hc, hs, _, _, _⟩ := inj_step_trig k
  obtain ⟨m, hm, htm⟩ := inj_grid_of_mem ht
  obtain ⟨hAK, hA1, hA2, hA3⟩ := inj_polygon_consecutive hKp (m := m) (by omega) htm
  obtain ⟨hCK, hC1, hC2, hC3⟩ := inj_polygon_consecutive hKp
    (m := 2 ^ (k + 1) + m) (by omega) (a := t + π / 2)
    (by rw [htm, ← hn]; push_cast; ring)
  have hsinne : sin (t + stepSize k - t) ≠ 0 := by
    rw [add_sub_cancel_left]
    exact hs.ne'
  have hsinne' : sin (t + π / 2 + stepSize k - (t + π / 2)) ≠ 0 := by
    rw [add_sub_cancel_left]
    exact hs.ne'
  set A := vint K t (t + stepSize k) with hAdef
  set C := vint K (t + π / 2) (t + π / 2 + stepSize k) with hCdef
  have hsuppA : ∀ s ∈ Icc t (t + stepSize k), supp K s = dot A (uvec s) := by
    intro s hs'
    rcases eq_or_lt_of_le hs'.1 with rfl | h1
    · exact (vint_mem_line_left K _ _).symm
    rcases eq_or_lt_of_le hs'.2 with rfl | h2
    · exact (vint_mem_line_right K hsinne).symm
    · exact (hA3 s ⟨h1, h2⟩).1
  have hsuppC : ∀ s ∈ Icc t (t + stepSize k),
      supp K (s + π / 2) = dot C (uvec (s + π / 2)) := by
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
  have hGd : ∀ s, HasDerivAt G (dot (A - C) (vvec s)) s :=
    fun s => inj_hasDerivAt_dot_uvec (A - C) s
  have hGneg : ∀ s ∈ Icc t (t + stepSize k), dot (A - C) (vvec s) ≤ 0 := by
    intro s hs'
    rw [dot_sub_left, ← uvec_add_pi_div_two, ← hsuppC s hs']
    linarith [dot_le_supp hKc.2.1 hAK (s + π / 2)]
  have hGD : ∀ s, -D ≤ dot (A - C) (vvec s) :=
    fun s => neg_bound_le_dot_vvec hD (hdiam A hAK C hCK) s
  have hGc : Continuous G := by
    simp only [hG, dot, uvec]
    fun_prop
  have hanti : AntitoneOn G (Icc t (t + stepSize k)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hGc.continuousOn
      (fun s _ => (hGd s).differentiableAt.differentiableWithinAt)
    intro s hs'
    rw [interior_Icc] at hs'
    rw [(hGd s).deriv]
    exact hGneg s ⟨hs'.1.le, hs'.2.le⟩
  have hmono : MonotoneOn (fun s => G s + D * s) (Icc t (t + stepSize k)) := by
    have hd : ∀ s, HasDerivAt (fun s => G s + D * s)
        (dot (A - C) (vvec s) + D) s := by
      intro s
      have h := (hGd s).add ((hasDerivAt_id' s).const_mul D)
      rw [mul_one] at h
      exact h
    apply monotoneOn_of_deriv_nonneg (f := fun s => G s + D * s)
      (convex_Icc _ _) (hGc.add (continuous_const.mul continuous_id)).continuousOn
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt)
    intro s _
    rw [(hd s).deriv]
    linarith [hGD s]
  have htI : t ∈ Icc t (t + stepSize k) := ⟨le_rfl, by linarith⟩
  have htdI : t + stepSize k ∈ Icc t (t + stepSize k) := ⟨by linarith, le_rfl⟩
  refine ⟨fun t' ht' => ?_, ?_⟩
  · have ht'I : t' ∈ Icc t (t + stepSize k) := ⟨ht'.1.le, ht'.2.le⟩
    obtain ⟨hp, hm'⟩ := hgs t' ht'
    refine ⟨?_, by rw [hp, hm'], ?_⟩
    · rw [hp, hgt]
      exact hanti htI ht'I ht'.1.le
    · rw [hm', hgtd]
      exact hanti ht'I htdI ht'.2.le
  · rw [hgt, hgtd]
    have h := hmono htI htdI (by linarith)
    linarith

/-- Convert a pointwise discrete estimate with a mesh-local error into an
integrated estimate on one cell. -/
theorem polygon_step_integral_bound {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C η : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ))
    (hlocal : sigmaAt K t ≤ k0 (gPlus K t) * stepSize k +
      C * stepSize k ^ 2 + η * stepSize k) :
    sigmaAt K t ≤ (∫ u in t..(t + stepSize k), k0 (gPlus K u)) +
      (C + D) * stepSize k ^ 2 + η * stepSize k := by
  have hδ := inj_stepSize_pos k
  obtain ⟨hmon, hDstep⟩ := polygon_arm_cell hK hD hdiam ht
  have hint : (k0 (gPlus K t) - D * stepSize k) * stepSize k ≤
      ∫ u in t..(t + stepSize k), k0 (gPlus K u) := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (a := t) (b := t + stepSize k)
      (f := fun _ => k0 (gPlus K t) - D * stepSize k)
      (g := fun u => k0 (gPlus K u)) (by linarith) intervalIntegrable_const
      (inj_intervalIntegrable_k0_gPlus hK.1.2.1 _ _) (by
        intro u hu
        obtain ⟨hu1, hu2, hu3⟩ := hmon u hu
        have hlip := inj_k0_lipschitz (gPlus K u) (gPlus K t)
        have hg : |gPlus K u - gPlus K t| ≤ D * stepSize k := by
          rw [abs_le]
          constructor <;> linarith
        linarith [(abs_le.mp hlip).1])
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at h
    linarith
  nlinarith

end MovingSofaUniqueness

end

/-!
## Curvature estimates for penalized polygon maximizers

The inner-ray geometry in the proof of Theorem 6.3.3 does not require
maximality or balancedness. We first extract its estimate for tau, rather than
replacing tau by sigma. A one-sided defect sigma<=tau+e is then sufficient for

  sigma(t) <= k0(gPlus(t))*delta + (D+4)*delta^2 + e.

Here D is an arbitrary uniform arm bound. Thus the diameter bound for specially
chosen exact maximizers is not applied to the specified-cap approximations.
The geometric proof follows `inj_sigmaAt_le_geom`, retaining its endpoint and
zero-measure singleton cases but removing its use of Theorem 3.4.9.
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The inner-ray estimate holds for every polygon cap. -/
theorem polygon_tau_le_geom {k : ℕ} {K : Set (ℝ × ℝ)}
    (hKp : IsPolygonCap (rightAngleSet k) K)
    {t : ℝ} (ht : t ∈ (rightAngleSet k).angles) :
    tau (rightAngleSet k) K t ≤
      max (max (tan (stepSize k) * (gMinus K t - 1 + tan (stepSize k / 2)))
        (tan (stepSize k) * (1 - gPlus K t + tan (stepSize k / 2)))) 0 +
      max (2 * tan (stepSize k / 2) - sigmaAt K t) 0 := by
  obtain ⟨hc, hs, htan, hT0, hT⟩ := inj_step_trig k
  have htI := (rightAngleSet k).subset t ht
  simp only [inj_rightAngleSet_ω] at htI
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [htI.1, pi_pos], htI.2⟩
  have hlen := (lemma3_4_5_one hKp ht).2.1
  set s₀ := supp K (t + π / 2) - 1 with hs₀
  set s₁ := (supp K (t + π / 2 - stepSize k) - 1 - (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁
  set s₁' := (supp K (t + π / 2 + stepSize k) - 1 + (supp K t - 1) * sin (stepSize k)) /
    cos (stepSize k) with hs₁'
  set sp := (supp K (t + stepSize k) - 1 - (supp K t - 1) * cos (stepSize k)) / sin (stepSize k)
    with hsp
  set sm := ((supp K t - 1) * cos (stepSize k) - supp K (t - stepSize k) + 1) / sin (stepSize k)
    with hsm
  set z₀ := -((supp K t - 1) * sin t) / cos t with hz₀
  set Q := {s : ℝ | (supp K t - 1) • uvec t + s • vvec t ∈
    frontier (polyNiche (rightAngleSet k) K) ∩ wallBVec K t} with hQ
  have hτ : tau (rightAngleSet k) K t = (volume Q).toReal := by
    rw [← hlen, lineLength]
  have hincl : Q ⊆ ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀} := by
    intro s hsQ
    obtain ⟨hxF, hxW⟩ := hsQ
    have hsW : s ≤ s₀ := inj_mem_wallBVec.1 hxW
    by_cases hD1 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t - stepSize k)
    · have : s ∈ Icc s₁ s₀ := by
        rw [← inj_param_minus hc]
        exact ⟨hxW, hD1⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_left _ _) this.1, this.2⟩))
    by_cases hD2 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K (t + stepSize k)
    · have : s ∈ Icc s₁' s₀ := by
        rw [← inj_param_plus hc]
        exact ⟨hxW, hD2⟩
      exact Or.inl (Or.inl (Or.inl ⟨le_trans (min_le_right _ _) this.1, this.2⟩))
    by_cases hD0 : (supp K t - 1) • uvec t + s • vvec t ∈ halfD K t
    · rw [inj_mem_halfD, sub_self, sin_zero, cos_zero] at hD0
      exact Or.inl (Or.inl (Or.inr (le_antisymm hsW (by linarith))))
    have hx2 := inj_frontier_niche_snd (inj_rightAngleSet_ω k) hxF
    have hx2e : ((supp K t - 1) • uvec t + s • vvec t).2 = (supp K t - 1) * sin t + s * cos t := by
      simp [uvec, vvec]
    rcases hx2.lt_or_eq with hx2 | hx2
    · left
      right
      have hB : ∀ u, (u ∈ (rightAngleSet k).angles ∨ u = 0 ∨ u = π / 2) →
          (supp K t - 1) • uvec t + s • vvec t ∉ halfD K u →
          (supp K t - 1) • uvec t + s • vvec t ∈ halfB K u := by
        intro u hu hnD
        have hq := inj_not_mem_qMinus hKp hxF hx2 hu
        rw [proposition2_2_2_qMinus] at hq
        simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, not_and_or, not_lt] at hq
        rcases hq with hq | hq
        · exact hq
        · exact absurd hq hnD
      have h1 := hB (t + stepSize k) ((inj_angles_succ ht).elim Or.inl (fun h => Or.inr (Or.inr h))) hD2
      have h2 := hB (t - stepSize k) ((inj_angles_pred ht).elim Or.inl (fun h => Or.inr (Or.inl h))) hD1
      rw [inj_mem_halfB] at h1 h2
      have e1 : t - (t + stepSize k) = -stepSize k := by ring
      have e2 : t + stepSize k - t = stepSize k := by ring
      have e3 : t - (t - stepSize k) = stepSize k := by ring
      have e4 : t - stepSize k - t = -stepSize k := by ring
      rw [e1, e2, cos_neg] at h1
      rw [e3, e4, sin_neg] at h2
      constructor
      · rw [hsp, div_le_iff₀ hs]
        linarith
      · rw [hsm, le_div_iff₀ hs]
        linarith
    · right
      rw [mem_singleton_iff, hz₀, eq_div_iff hct.ne']
      rw [hx2e] at hx2
      linarith
  have hvol : volume Q ≤ ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
    calc
      volume Q ≤ volume (((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) ∪ {z₀}) := measure_mono hincl
      _ ≤ volume ((Icc (min s₁ s₁') s₀ ∪ {s₀}) ∪ Icc sp sm) + volume ({z₀} : Set ℝ) :=
        measure_union_le _ _
      _ ≤ (volume (Icc (min s₁ s₁') s₀) + volume ({s₀} : Set ℝ)) + volume (Icc sp sm) + 0 := by
        rw [measure_singleton]
        gcongr
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp) := by
        rw [measure_singleton, Real.volume_Icc, Real.volume_Icc, add_zero, add_zero]
  have hreal : tau (rightAngleSet k) K t ≤ max (s₀ - min s₁ s₁') 0 + max (sm - sp) 0 := by
    rw [hτ]
    calc
      (volume Q).toReal ≤ (ENNReal.ofReal (s₀ - min s₁ s₁') + ENNReal.ofReal (sm - sp)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hvol
      _ = _ := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rw [← max_sub_sub_left, inj_param_minus_length hKp ht, inj_param_plus_length hKp ht,
    inj_polygon_sigmaAt_eq hKp ht] at hreal
  exact hreal

/-- Robust version of the discrete curvature estimate, with an arbitrary arm
bound and an explicit nonnegative stationarity error. -/
theorem polygon_curvature_with_defect {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K)
    {t D e : ℝ} (ht : t ∈ (rightAngleSet k).angles)
    (hD : 0 ≤ D) (hgD : gPlus K t ≤ D) (he : 0 ≤ e)
    (hdefect : sigmaAt K t ≤ tau (rightAngleSet k) K t + e) :
    sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + (D + 4) * stepSize k ^ 2 + e := by
  have hgeom := polygon_tau_le_geom hK ht
  have hKc : IsConvexBody K := hK.1.2.1
  have hg0 : 0 ≤ gPlus K t := (inj_arm_nonneg hKc t).2.2.1
  have hgmp : gMinus K t ≤ gPlus K t := by
    have h := (proposition2_1_2 hKc (t + π / 2)).2
    have hσ0 : 0 ≤ sigmaAt K (t + π / 2) := ENNReal.toReal_nonneg
    rw [gMinus, gPlus, dot_sub_left, dot_sub_left, cPlus, cMinus, h,
      dot_add_left, dot_smul_left, vvec_add_pi_div_two, dot_neg_left, dot_uvec_self]
    linarith
  have hδ := inj_stepSize_pos k
  have hδ4 := inj_stepSize_le k
  have hδ1 : stepSize k ≤ 1 := by linarith [pi_le_four]
  obtain ⟨_, _, htan0, hT0, _⟩ := inj_step_trig k
  have htan := inj_tan_le hδ.le hδ4
  have hT := inj_tan_le (x := stepSize k / 2) (by linarith) (by linarith)
  set δ := stepSize k
  set T := tan (δ / 2)
  set M := |gPlus K t - 1|
  have hM0 : 0 ≤ M := abs_nonneg _
  have hMD : M ≤ D + 1 := by
    rw [show M = |gPlus K t - 1| from rfl, abs_le]
    constructor <;> linarith
  have hMg : gMinus K t - 1 ≤ M := (by linarith : gMinus K t - 1 ≤ gPlus K t - 1).trans
    (le_abs_self (gPlus K t - 1))
  have hMg' : 1 - gPlus K t ≤ M := by
    change 1 - gPlus K t ≤ |gPlus K t - 1|
    rw [abs_sub_comm]
    exact le_abs_self _
  have hfirst : max (max (tan δ * (gMinus K t - 1 + T))
      (tan δ * (1 - gPlus K t + T))) 0 ≤ δ * M + (D + 3) * δ ^ 2 := by
    have hTδ : T ≤ δ := by nlinarith
    have hprod : tan δ * (M + T) ≤ (δ + δ ^ 2) * (M + δ) :=
      mul_le_mul htan (by linarith) (by positivity) (by positivity)
    have hrest : (δ + δ ^ 2) * (M + δ) ≤ δ * M + (D + 3) * δ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hMD (sq_nonneg δ)
      have hcube := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg δ)
      nlinarith
    have hb := hprod.trans hrest
    refine max_le (max_le ?_ ?_) (by positivity)
    · exact (mul_le_mul_of_nonneg_left (by linarith : gMinus K t - 1 + T ≤ M + T) htan0.le).trans hb
    · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - gPlus K t + T ≤ M + T) htan0.le).trans hb
  have hk : M ≤ k0 (gPlus K t) := le_max_left _ _
  have hk' : (M + 1) / 2 ≤ k0 (gPlus K t) := le_max_right _ _
  have hkδ := mul_le_mul_of_nonneg_left hk hδ.le
  have hkδ' := mul_le_mul_of_nonneg_left hk' hδ.le
  rcases le_total (2 * T - sigmaAt K t) 0 with hcase | hcase
  · change tau (rightAngleSet k) K t ≤ _ + max (2 * T - sigmaAt K t) 0 at hgeom
    rw [max_eq_right hcase] at hgeom
    nlinarith [sq_nonneg δ]
  · change tau (rightAngleSet k) K t ≤ _ + max (2 * T - sigmaAt K t) 0 at hgeom
    rw [max_eq_left hcase] at hgeom
    have hDsq := mul_nonneg (show 0 ≤ D + 4 by linarith) (sq_nonneg δ)
    nlinarith [sq_nonneg δ]

end MovingSofaUniqueness

end

/-!
## Reflection preserves the specified maximizer

These lemmas concern the actual reflected cap, not a replacement obtained
from existence of a balanced maximizer. They are independent of injectivity.
The sofa-area identity uses the reflected niche, including its strict inner
quadrants.
-/

section

open Real Set MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Reflection preserves the cap-minus-niche area functional. -/
theorem sofaArea_mirror (K : Set (ℝ × ℝ)) (ω : ℝ) :
    sofaArea ω (mirrorCap K ω) = sofaArea ω K := by
  unfold sofaArea
  rw [(proposition2_5_4_sets (K := K) (ω := ω) 0).2.2]
  change area (mirror ω '' K) - area (mirror ω '' niche K ω) = _
  rw [mpc_area_mirror, mpc_area_mirror]

/-- At a right angle the mirror is the involution `(x,y) ↦ (-x,y)`. -/
theorem mirrorCap_rightAngle_involutive (K : Set (ℝ × ℝ)) :
    mirrorCap (mirrorCap K (π / 2)) (π / 2) = K := by
  have hinv (p : ℝ × ℝ) : mirror (π / 2) (mirror (π / 2) p) = p := by
    rcases p with ⟨x, y⟩
    simp only [inj_mirror_pi_div_two, neg_neg]
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [hinv] using hr
  · intro p hp
    exact ⟨mirror (π / 2) p, ⟨p, hp, rfl⟩, hinv p⟩

/-- The reflection of this maximizer is again a maximizer. -/
theorem maximal_sofaArea_mirror {K : Set (ℝ × ℝ)}
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    ∀ C, IsCap C (π / 2) →
      sofaArea (π / 2) C ≤ sofaArea (π / 2) (mirrorCap K (π / 2)) := by
  intro C hC
  rw [sofaArea_mirror]
  exact hmax C hC

/-- The endpoint conventions matter: the reflected plus-arm is the original
minus-arm. No atom-free or differentiability hypothesis is needed. -/
theorem gPlus_mirror_eq_fMinus (K : Set (ℝ × ℝ)) (t : ℝ) :
    gPlus (mirrorCap K (π / 2)) t = fMinus K (π / 2 - t) :=
  (proposition6_2_2 (K := K) (t := t)).2.2.1

end MovingSofaUniqueness

end

/-!
## Injectivity from curvature bounds for the specified cap

The operator comparison below is simultaneous in the two arm functions. It
never assumes that the cap is balanced or replaces it by its mirror's chosen
maximizer. Only the two integrated inequalities and nonnegativity are used.

For the final strict threshold we reuse the existing analytic Lemma 6.5.5.
Its finite induction consists of real integral inequalities and rational
algebraic proofs, not a Boolean evaluation or a decision procedure. The
alternative maximum-deficit argument of the notes is not needed here.
-/

section

open Real Set MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The lower sequence bounds both arms without any cap-specific hypothesis.
The opposite endpoint conventions are kept throughout the induction. -/
theorem lowerSeq_le_of_integral_bounds {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (π / 2))) (hg : ContinuousOn g (Icc 0 (π / 2)))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) (π / 2), 0 ≤ f t)
    (hg0 : ∀ t ∈ Icc (0 : ℝ) (π / 2), 0 ≤ g t)
    (hfi : ∀ t ∈ Ico (0 : ℝ) (π / 2),
      (∫ u in (0 : ℝ)..t, m0 (g u)) ≤ f t - 1)
    (hgi : ∀ t ∈ Ioc (0 : ℝ) (π / 2),
      (∫ u in t..(π / 2), m0 (f u)) ≤ g t - 1) :
    ∀ n : ℕ,
      (∀ t ∈ Ico (0 : ℝ) (π / 2), lowerSeq n t ≤ f t) ∧
      (∀ t ∈ Ioc (0 : ℝ) (π / 2), lowerSeq n (π / 2 - t) ≤ g t) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun t ht => hf0 t ⟨ht.1, ht.2.le⟩,
      fun t ht => hg0 t ⟨ht.1.le, ht.2⟩⟩
  | succ n ih =>
    constructor
    · intro t ht
      change max (lowerSeq n t) (lowerOp (lowerSeq n) t) ≤ f t
      apply max_le (ih.1 t ht)
      have hseq : IntervalIntegrable
          (fun u => m0 (lowerSeq n (π / 2 - u))) volume 0 t :=
        (inj_continuous_m0.comp ((inj_continuous_lowerSeq n).comp
          (continuous_const.sub continuous_id))).intervalIntegrable _ _
      have hgint : IntervalIntegrable (fun u => m0 (g u)) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.1]
        exact inj_continuous_m0.comp_continuousOn
          (hg.mono (Icc_subset_Icc le_rfl ht.2.le))
      have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.1 hseq hgint
        (fun u hu => inj_m0_mono (ih.2 u ⟨hu.1, hu.2.le.trans ht.2.le⟩))
      have hb := hfi t ht
      unfold lowerOp
      linarith
    · intro t ht
      change max (lowerSeq n (π / 2 - t))
        (lowerOp (lowerSeq n) (π / 2 - t)) ≤ g t
      apply max_le (ih.2 t ht)
      have hseq : IntervalIntegrable (fun u => m0 (lowerSeq n u))
          volume t (π / 2) :=
        (inj_continuous_m0.comp (inj_continuous_lowerSeq n)).intervalIntegrable _ _
      have hfint : IntervalIntegrable (fun u => m0 (f u)) volume t (π / 2) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.2]
        exact inj_continuous_m0.comp_continuousOn
          (hf.mono (Icc_subset_Icc ht.1.le le_rfl))
      have hi := intervalIntegral.integral_mono_on_of_le_Ioo ht.2 hseq hfint
        (fun u hu => inj_m0_mono (ih.1 u ⟨ht.1.le.trans hu.1.le, hu.2⟩))
      have hb := hgi t ht
      rw [lowerOp, intervalIntegral.integral_comp_sub_left (fun u => m0 (lowerSeq n u)),
        sub_sub_cancel, sub_zero]
      linarith

/-- Strict interior arm inequalities follow from the given curvature bounds. -/
theorem arms_strict_of_curvature {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound K) (hsecond : SecondCurvatureBound K) :
    ∀ t ∈ Ioo (0 : ℝ) (π / 2), 1 < fK K t ∧ 1 < gK K t := by
  have h1 := injCond1_of_curvature hfirst hsecond
  obtain ⟨_, _, hfc, hgc⟩ := proposition6_4_6_continuous hK h1
  have hseq := lowerSeq_le_of_integral_bounds hfc hgc
    (fun t _ => (inj_arm_nonneg hK.2.1 t).2.1)
    (fun t _ => (inj_arm_nonneg hK.2.1 t).2.2.1)
    (fun t ht => first_arm_integral_lower hK h1 hfirst ht)
    (fun t ht => second_arm_integral_lower hK h1 hsecond ht) 11
  intro t ht
  refine ⟨(lemma6_5_5 ⟨ht.1, ht.2.le⟩).trans_le (hseq.1 t ⟨ht.1.le, ht.2⟩), ?_⟩
  exact (lemma6_5_5 ⟨by linarith [ht.2], by linarith [ht.1]⟩).trans_le
    (hseq.2 t ⟨ht.1, ht.2.le⟩)

/-- Proposition 3: the specified cap satisfies all three injectivity conditions.
No global maximality or balancedness hypothesis is present. -/
theorem injectivity_of_curvature {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound K) (hsecond : SecondCurvatureBound K) :
    SatisfiesInjectivity K := by
  have h1 := injCond1_of_curvature hfirst hsecond
  obtain ⟨hx, _, hder⟩ := proposition6_4_6_deriv hK h1
  have harms := arms_strict_of_curvature hK hfirst hsecond
  refine ⟨h1, hx, fun t ht => ?_⟩
  have hd := (hder t ⟨ht.1.le, ht.2.le⟩).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [hd.deriv]
  simp only [dot_add_left, dot_smul_left, dot_uvec_self, dot_vvec_uvec,
    dot_uvec_vvec, dot_vvec_self]
  obtain ⟨hf, hg⟩ := harms t ht
  constructor <;> linarith

end MovingSofaUniqueness

end

/-!
## Integrated polygon curvature bounds with summable defects

The error need not be uniformly O(delta) at each facet. A nonnegative error
function on the grid is sufficient provided that its TOTAL tends to zero.
This is important for persistent sampled penalties: their coarse-angle and
endpoint weights need not shrink proportionally to the finest mesh.

The estimate includes normal zero and extends to open intervals starting below
zero. Thus passage to the limit can exclude an atom at zero rather than assume
that it is absent. No balancedness or polygon maximality occurs in the hypotheses.
-/

section

open Set Real MeasureTheory MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- One cell with an arbitrary additive local error. -/
theorem polygon_step_with_error {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C e : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D) {t : ℝ}
    (ht : t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ))
    (hlocal : sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e) :
    sigmaAt K t ≤ (∫ u in t..(t + stepSize k), k0 (gPlus K u)) +
      (C + D) * stepSize k ^ 2 + e := by
  have hδ : stepSize k ≠ 0 := (inj_stepSize_pos k).ne'
  have h := polygon_step_integral_bound hK hD hdiam ht
    (η := e / stepSize k) (by simpa only [div_mul_cancel₀ _ hδ] using hlocal)
  simpa only [div_mul_cancel₀ _ hδ] using h

/-- Sum of the nonnegative grid errors, including the zero normal. -/
def polygonGridError (k : ℕ) (e : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ (k + 1)), e ((j : ℝ) * stepSize k)

/-- Integrated estimate on an arbitrary half-open interval in the first
quadrant. The entire error sum appears once, not once for each cell. -/
theorem polygon_Ico_with_errors {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C B : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D)
    (hbound : ∀ u ∈ Icc (0 : ℝ) (π / 2), k0 (gPlus K u) ≤ B)
    (e : ℝ → ℝ)
    (he : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ), 0 ≤ e t)
    (hlocal : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ico a b)).toReal ≤ (∫ u in a..b, k0 (gPlus K u)) +
      (2 * B + π / 2 * (C + D)) * stepSize k + polygonGridError k e := by
  have hKc : IsConvexBody K := hK.1.2.1
  have hδ := inj_stepSize_pos k
  have hn : ((2 ^ (k + 1) : ℕ) : ℝ) * stepSize k = π / 2 := by
    push_cast
    exact inj_two_pow_mul_stepSize k
  set δ := stepSize k with hδdef
  set n := 2 ^ (k + 1) with hndef
  let E : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, e ((j : ℝ) * δ)
  have hint := inj_intervalIntegrable_k0_gPlus hKc
  have hgrid : ∀ j : ℕ, j < n →
      (j : ℝ) * δ ∈ insert 0 ((rightAngleSet k).angles : Set ℝ) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left
      simp
    · right
      exact inj_mem_angles.2 ⟨j, hj0, hj, rfl⟩
  have hEnonneg : ∀ m ≤ n, 0 ≤ E m := by
    intro m hm
    apply Finset.sum_nonneg
    intro j hj
    exact he _ (hgrid j ((Finset.mem_range.mp hj).trans_le hm))
  have hEmono : ∀ m ≤ n, E m ≤ E n := by
    intro m hm
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
    intro j hj _
    exact he _ (hgrid j (Finset.mem_range.mp hj))
  have hsum : ∀ p m : ℕ, p ≤ m → m ≤ n →
      (sigma K (Ico (p * δ) (m * δ))).toReal ≤
        (∫ u in (p * δ)..(m * δ), k0 (gPlus K u)) +
          ((m : ℝ) - p) * ((C + D) * δ ^ 2) + (E m - E p) := by
    intro p m hpm
    induction m, hpm using Nat.le_induction with
    | base =>
      intro _
      simp
    | succ m hpm ih =>
      intro hmn
      have ih := ih (by omega)
      have hmδ : (m : ℝ) * δ ≤ ((m + 1 : ℕ) : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) hδ.le
      have hpδ : (p : ℝ) * δ ≤ m * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hpm) hδ.le
      have e1 : Ico ((p : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) =
          Ico ((p : ℝ) * δ) (m * δ) ∪ Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ) :=
        (Ico_union_Ico_eq_Ico hpδ hmδ).symm
      have hm1 : (((m + 1 : ℕ) : ℝ) * δ) = m * δ + δ := by push_cast; ring
      have hmΘ := hgrid m (by omega)
      obtain ⟨_, hA1, _, hA3⟩ := inj_polygon_consecutive hK (m := m) (by omega) rfl
      have hIoo : sigma K (Ioo ((m : ℝ) * δ) (m * δ + δ)) = 0 := by
        apply inj_sigma_Ioo_eq_zero hKc (by linarith)
          (q := vint K (m * δ) (m * δ + δ))
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | h1
        · exact hA1
        · exact (hA3 s ⟨h1, hs.2⟩).2.1
      have hstep : (sigma K (Ico ((m : ℝ) * δ) (((m + 1 : ℕ) : ℝ) * δ))).toReal =
          sigmaAt K (m * δ) := by
        rw [hm1, ← Ioo_insert_left (by linarith), insert_eq,
          measure_union (disjoint_singleton_left.2 (fun h => lt_irrefl _ h.1)) measurableSet_Ioo,
          hIoo, add_zero, sigmaAt]
      have hs := polygon_step_with_error hK hD hdiam hmΘ (hlocal _ hmΘ)
      rw [← hδdef] at hs
      have hEs : E (m + 1) = E m + e ((m : ℝ) * δ) := by
        exact Finset.sum_range_succ _ m
      rw [e1, measure_union Ico_disjoint_Ico_same measurableSet_Ico,
        ENNReal.toReal_add measure_Ico_lt_top.ne measure_Ico_lt_top.ne, hstep,
        ← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ) * δ)
          (hint _ _) (hint _ _), hm1, hEs]
      push_cast
      nlinarith
  set p := ⌊a / δ⌋₊ with hp
  set q := ⌈b / δ⌉₊ with hq
  have hpa : (p : ℝ) * δ ≤ a := by
    have h := Nat.floor_le (div_nonneg ha hδ.le)
    rw [← hp] at h
    calc
      (p : ℝ) * δ ≤ a / δ * δ := by gcongr
      _ = a := div_mul_cancel₀ a hδ.ne'
  have hpa' : a < (p : ℝ) * δ + δ := by
    have h := Nat.lt_floor_add_one (a / δ)
    rw [← hp] at h
    calc
      a = a / δ * δ := (div_mul_cancel₀ a hδ.ne').symm
      _ < ((p : ℝ) + 1) * δ := by gcongr
      _ = p * δ + δ := by ring
  have hqb : b ≤ (q : ℝ) * δ := by
    have h := Nat.le_ceil (b / δ)
    rw [← hq] at h
    calc
      b = b / δ * δ := (div_mul_cancel₀ b hδ.ne').symm
      _ ≤ q * δ := by gcongr
  have hqb' : (q : ℝ) * δ < b + δ := by
    have h := Nat.ceil_lt_add_one (div_nonneg (ha.trans hab) hδ.le)
    rw [← hq] at h
    calc
      (q : ℝ) * δ < (b / δ + 1) * δ := by gcongr
      _ = b + δ := by rw [add_mul, div_mul_cancel₀ b hδ.ne', one_mul]
  have hqn : q ≤ n := by
    rw [hq]
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hδ, hn]
    exact hb
  have hpq : p ≤ q := by
    have h : (p : ℝ) * δ ≤ q * δ := hpa.trans (hab.trans hqb)
    exact_mod_cast le_of_mul_le_mul_right h hδ
  have hqπ : (q : ℝ) * δ ≤ π / 2 := by
    rw [← hn]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqn) hδ.le
  have hp0 : (0 : ℝ) ≤ p * δ := by positivity
  have hsumPQ := hsum p q hpq hqn
  have hleft : ∫ u in (p * δ)..a, k0 (gPlus K u) ≤ B * δ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hpa (hint _ _)
      (intervalIntegrable_const (c := B))
      (fun u hu => hbound u ⟨hp0.trans hu.1, by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    nlinarith
  have hright : ∫ u in b..(q * δ), k0 (gPlus K u) ≤ B * δ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hqb (hint _ _)
      (intervalIntegrable_const (c := B))
      (fun u hu => hbound u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    nlinarith
  have hsplit : ∫ u in (p * δ)..(q * δ), k0 (gPlus K u) =
      (∫ u in (p * δ)..a, k0 (gPlus K u)) + (∫ u in a..b, k0 (gPlus K u)) +
        ∫ u in b..(q * δ), k0 (gPlus K u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmono : (sigma K (Ico a b)).toReal ≤
      (sigma K (Ico ((p : ℝ) * δ) (q * δ))).toReal :=
    ENNReal.toReal_mono measure_Ico_lt_top.ne (measure_mono (Ico_subset_Ico hpa hqb))
  have hqp : ((q : ℝ) - p) * ((C + D) * δ ^ 2) ≤ π / 2 * (C + D) * δ := by
    have hqp' : ((q : ℝ) - p) ≤ n := by
      have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
      linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    calc
      ((q : ℝ) - p) * ((C + D) * δ ^ 2) ≤ n * ((C + D) * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hqp' (by positivity)
      _ = ((n : ℝ) * δ) * (C + D) * δ := by ring
      _ = π / 2 * (C + D) * δ := by rw [hn]
  have hE : E q - E p ≤ polygonGridError k e := by
    have h₁ := hEmono q hqn
    have h₂ := hEnonneg p (hpq.trans hqn)
    change E q - E p ≤ E n
    linarith
  linarith

/-- The same estimate on intervals beginning below zero. This deliberately
keeps zero INSIDE an open interval before taking the limiting measure. -/
theorem polygon_Ioo_with_errors {k : ℕ} {K : Set (ℝ × ℝ)}
    (hK : IsPolygonCap (rightAngleSet k) K) {D C B : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ D)
    (hbound : ∀ u ∈ Icc (0 : ℝ) (π / 2), k0 (gPlus K u) ≤ B)
    (e : ℝ → ℝ)
    (he : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ), 0 ≤ e t)
    (hlocal : ∀ t ∈ insert 0 ((rightAngleSet k).angles : Set ℝ),
      sigmaAt K t ≤ k0 (gPlus K t) * stepSize k + C * stepSize k ^ 2 + e t)
    {a b : ℝ} (ha : -(π / 2) ≤ a) (hab : max a 0 ≤ b) (hb : b ≤ π / 2) :
    (sigma K (Ioo a b)).toReal ≤ (∫ u in (max a 0)..b, k0 (gPlus K u)) +
      (2 * B + π / 2 * (C + D)) * stepSize k + polygonGridError k e := by
  have hcap : IsCap K (π / 2) := hK.1
  have hKc : IsConvexBody K := hcap.2.1
  obtain ⟨_, hc2, hc3⟩ := inj_cap_consecutive hcap
  have h0 : sigma K (Ioo (-(π / 2)) 0) = 0 := by
    apply inj_sigma_Ioo_eq_zero hKc (by linarith [pi_pos]) (q := (supp K 0, 0))
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | h1
    · exact hc2
    · exact hc3 s ⟨h1, hs.2⟩
  have hsub : Ioo a b ⊆ Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b := by
    intro x hx
    by_cases hx0 : x < 0
    · left
      exact ⟨by linarith [hx.1], hx0⟩
    · right
      exact ⟨max_le hx.1.le (not_lt.mp hx0), hx.2⟩
  have hle : sigma K (Ioo a b) ≤ sigma K (Ico (max a 0) b) := by
    calc
      sigma K (Ioo a b) ≤ sigma K (Ioo (-(π / 2)) 0 ∪ Ico (max a 0) b) := measure_mono hsub
      _ ≤ sigma K (Ioo (-(π / 2)) 0) + sigma K (Ico (max a 0) b) := measure_union_le _ _
      _ = sigma K (Ico (max a 0) b) := by rw [h0, zero_add]
  calc
    (sigma K (Ioo a b)).toReal ≤ (sigma K (Ico (max a 0) b)).toReal :=
      ENNReal.toReal_mono measure_Ico_lt_top.ne hle
    _ ≤ _ := polygon_Ico_with_errors hK hD hC hB hdiam hbound e he hlocal
      (le_max_right _ _) hab hb

end MovingSofaUniqueness

end

/-!
## Curvature domination from arbitrary polygon approximations

The hypotheses are convergence of polygon caps and an integrated inequality
with a vanishing total error. No maximum-polygon or balanced-cap predicate is
used. Supporting-line intersections furnish lower bounds on open-interval
curvature masses, so no absence of endpoint atoms is assumed in the passage
to the limit. The interval comparison then yields domination on [0,pi/2).
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

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

end MovingSofaUniqueness

end

/-!
## Curvature domination for the specified cap

Actual penalized stationarity, the geometric inner-ray bound, the cellwise arm
estimate, and the endpoint-safe limiting theorem are assembled here. Persistent
coarse sample weights need not be O(delta); their total is at most one, and the
new integrated estimate sums their errors just once.
-/

section

open Set Real Filter Topology MeasureTheory MovingSofaOptimality
open scoped BigOperators

namespace MovingSofaUniqueness

/-- Any injective finite list of normals collects at most all the sample mass. -/
theorem distinct_normalWeight_sum_le {Θ : AngleSet} (S : SupportSamples Θ)
    {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (hinj : Set.InjOn t (s : Set ι)) :
    (∑ j ∈ s, S.atNormal (t j)) ≤ S.totalWeight := by
  classical
  unfold SupportSamples.atNormal normalWeight SupportSamples.totalWeight
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hex : ∃ j ∈ s, S.normal i = t j
  · obtain ⟨j, hj, heq⟩ := hex
    rw [Finset.sum_eq_single j]
    · simp [heq]
    · intro k hk hkj
      have hne : S.normal i ≠ t k := by
        intro h
        have he : t k = t j := h.symm.trans heq
        exact hkj (hinj hk hj he)
      simp [hne]
    · exact fun hn => (hn hj).elim
  · have hne : ∀ j ∈ s, S.normal i ≠ t j := by
      intro j hj h
      exact hex ⟨j, hj, h⟩
    have hz : (∑ j ∈ s, if S.normal i = t j then S.weight i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hne j hj]
    rw [hz]
    exact S.weight_nonneg i

/-- In particular, the first-quadrant grid error is bounded by twice the
uniform support error, independently of the finest mesh. -/
theorem sampled_grid_error_le {k : ℕ} (S : SupportSamples (rightAngleSet k))
    {η : ℝ} (hη : 0 ≤ η) (hW : S.totalWeight ≤ 1) :
    polygonGridError k (fun t => 2 * η * S.atNormal t) ≤ 2 * η := by
  have hδ := inj_stepSize_pos k
  have hmass := distinct_normalWeight_sum_le S (Finset.range (2 ^ (k + 1)))
    (fun j : ℕ => (j : ℝ) * stepSize k) (by
      intro i hi j hj hij
      have he : (i : ℝ) = j := (mul_right_cancel₀ hδ.ne') hij
      exact_mod_cast he)
  unfold polygonGridError
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (hmass.trans hW) (show 0 ≤ 2 * η by positivity)
  simpa only [mul_one] using h

/-- A common coordinate box supplies the Euclidean diameter bound needed by
cellwise arm control. The ordinary product norm is not used as Euclidean norm. -/
theorem diameter_le_box {K : Set (ℝ × ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hbox : K ⊆ Icc (-R) R ×ˢ Icc 0 1) :
    ∀ p ∈ K, ∀ q ∈ K, norm2 (p - q) ≤ 2 * R + 2 := by
  intro p hp q hq
  obtain ⟨hpX, hpY⟩ := hbox hp
  obtain ⟨hqX, hqY⟩ := hbox hq
  have hx : |p.1 - q.1| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith [hpX.1, hpX.2, hqX.1, hqX.2]
  have hy : |p.2 - q.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hpY.1, hpY.2, hqY.1, hqY.2]
  rw [norm2, Real.sqrt_le_iff]
  constructor
  · positivity
  · simp only [dot, Prod.fst_sub, Prod.snd_sub]
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    nlinarith [sq_nonneg (2 * R - (p.1 - q.1)),
      sq_nonneg (2 * R + (p.1 - q.1)), sq_nonneg (1 - (p.2 - q.2)),
      sq_nonneg (1 + (p.2 - q.2))]

/-- Dyadic mesh sizes tend to zero along every strictly increasing subsequence. -/
theorem selected_stepSize_tendsto {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun n => stepSize (k n)) atTop (𝓝 0) := by
  have hmesh : Tendsto stepSize atTop (𝓝 0) := by
    unfold stepSize
    have hpow : Tendsto (fun m : ℕ => (2 : ℝ) ^ (m + 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.div_atTop hpow
  exact hmesh.comp hk.tendsto_atTop

/-- First-half curvature domination for every specified cap maximizing a
positive sofa-area value. Normal zero is included in the conclusion. -/
theorem firstCurvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    FirstCurvatureBound K := by
  classical
  obtain ⟨seq⟩ := exists_selectedCapSequence pi_div_two_mem_Ioc hK hpositive hmax
  let Ks := seq.cap
  let k := seq.index
  have hpoly : ∀ n, IsPolygonCap (rightAngleSet (k n)) (Ks n) := fun n => (seq.selected n).1
  have hc : ∀ n, IsConvexBody (Ks n) := fun n => (hpoly n).1.2.1
  let η : ℕ → ℝ := fun n => hausdorffDist (Ks n) K
  have hη : ∀ n, 0 ≤ η n := fun n => ang_hausdorffDist_nonneg (hc n) hK.2.1
  have hηlim : Tendsto η atTop (𝓝 0) := seq.tends
  let D := 2 * seq.radius + 2
  have hD : 0 ≤ D := by dsimp [D]; linarith [seq.radius_nonneg]
  have hdiam : ∀ n, ∀ p ∈ Ks n, ∀ q ∈ Ks n, norm2 (p - q) ≤ D :=
    fun n => diameter_le_box seq.radius_nonneg (seq.boxed n)
  have hsupp : ∀ n t, |supp (Ks n) t| ≤ seq.radius + 1 :=
    fun n t => abs_supp_le_box (hc n) (seq.boxed n) t
  have hgbound : ∀ n t, gPlus (Ks n) t ≤ D := by
    intro n t
    have h := inj_gPlus_le_width (hc n) t
    have h₀ := (abs_le.mp (hsupp n t)).2
    have h₁ := (abs_le.mp (hsupp n (t + π))).2
    dsimp [D]
    linarith
  have hkbound : ∀ n u, k0 (gPlus (Ks n) u) ≤ D + 1 := by
    intro n u
    have h := inj_k0_le (gPlus (Ks n) u)
    rw [abs_of_nonneg (inj_arm_nonneg (hc n) u).2.2.1] at h
    linarith [hgbound n u]
  let sample n := dyadicSamples (π / 2) pi_div_two_mem_Ioc (k n)
  let e (n : ℕ) (t : ℝ) := 2 * η n * (sample n).atNormal t
  have he : ∀ n t, 0 ≤ e n t := by
    intro n t
    have h₀ := hη n
    have h₁ := (sample n).atNormal_nonneg t
    dsimp [e]
    positivity
  have hlocal : ∀ n t, t ∈ insert 0 ((rightAngleSet (k n)).angles : Set ℝ) →
      sigmaAt (Ks n) t ≤ k0 (gPlus (Ks n) t) * stepSize (k n) +
        (D + 4) * stepSize (k n) ^ 2 + e n t := by
    intro n t ht
    rcases ht with rfl | ht
    · rw [inj_sigmaAt_eq_zero (hc n) (inj_polygon_vplus_zero (hpoly n))]
      have h₀ := inj_k0_nonneg (gPlus (Ks n) 0)
      have h₁ := inj_stepSize_pos (k n)
      have h₂ := he n 0
      positivity
    · have htI := (rightAngleSet (k n)).subset t ht
      have htL : t < π / 2 := htI.2
      have hdefect := floating_defect_le (sample n) (seq.selected n)
        (Or.inl (Or.inl ht)) (ne_of_lt htL) (ne_of_lt htL) (hη n)
        (fun i => ang_abs_supp_sub_le_hausdorffDist (hc n) hK.2.1 ((sample n).normal i))
      change sigmaAt (Ks n) t - tau (rightAngleSet (k n)) (Ks n) t ≤
        2 * η n * (sample n).atNormal t at hdefect
      apply polygon_curvature_with_defect (hpoly n) ht hD (hgbound n t) (he n t)
      dsimp [e]
      linarith
  have hsum : ∀ n, polygonGridError (k n) (e n) ≤ 2 * η n :=
    fun n => sampled_grid_error_le (sample n) (hη n)
      (dyadic_totalWeight_le_one (π / 2) pi_div_two_mem_Ioc (k n))
  let A := 2 * (D + 1) + π / 2 * ((D + 4) + D)
  let error : ℕ → ℝ := fun n => A * stepSize (k n) + 2 * η n
  have herr : Tendsto error atTop (𝓝 0) := by
    have h₀ := (selected_stepSize_tendsto seq.index_strict).const_mul A
    have h₁ := hηlim.const_mul 2
    simpa [error] using h₀.add h₁
  apply firstCurvature_of_polygon_errors hpoly hK seq.tends error herr
  intro n a b ha hab hab' hb
  have h := polygon_Ioo_with_errors (hpoly n) hD
    (show 0 ≤ D + 4 by linarith) (show 0 ≤ D + 1 by linarith) (hdiam n)
    (fun u _ => hkbound n u) (e n) (fun t _ => he n t) (hlocal n) ha hab' hb
  have hsum' := hsum n
  dsimp [error, A]
  linarith

end MovingSofaUniqueness

end

/-!
## Both curvature bounds for the specified maximizer

Reflection sends `[0, pi/2)` to `(pi/2, pi]`. The strict and non-strict
endpoints are preserved explicitly below. The arm identity exchanges plus
with minus, so no absence of atoms is assumed to prove absence of atoms. The
measure transport is written as equalities of restricted measures and lower
integrals.
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- The involution on normal angles induced by the right-angle cap mirror. -/
def normalReflection : ℝ ≃ᵐ ℝ where
  toFun t := π - t
  invFun t := π - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  measurable_toFun := measurable_const.sub measurable_id
  measurable_invFun := measurable_const.sub measurable_id

@[simp] theorem normalReflection_apply (t : ℝ) : normalReflection t = π - t := rfl

/-- Reflection of real normal angles preserves Lebesgue measure. -/
theorem normalReflection_measurePreserving :
    MeasurePreserving normalReflection (volume : Measure ℝ) volume := by
  refine ⟨normalReflection.measurable, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply normalReflection.measurable hA]
  have heq : normalReflection ⁻¹' A =
      (fun t : ℝ => (-1 : ℝ) * t) ⁻¹' ((fun t : ℝ => π + t) ⁻¹' A) := by
    ext t
    simp only [mem_preimage, normalReflection_apply, neg_one_mul, sub_eq_add_neg]
  rw [heq, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add]
  norm_num

/-- Curvature reflection, with the output cap identified as the original set. -/
theorem sigma_eq_map_mirror {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    sigma K = Measure.map normalReflection (sigma (mirrorCap K (π / 2))) := by
  have h := proposition2_5_4_sigma (proposition2_5_4_isCap hK)
  rw [mirrorCap_rightAngle_involutive] at h
  change sigma K = Measure.map (fun t : ℝ => π - t) (sigma (mirrorCap K (π / 2)))
  simpa only [show π / 2 + π / 2 = π by ring] using h

/-- Push the first-half bound for the reflected cap to the second half of K.
This lemma does not require either cap to maximize the area functional. -/
theorem secondCurvature_of_mirror_first {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2))
    (hfirst : FirstCurvatureBound (mirrorCap K (π / 2))) : SecondCurvatureBound K := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  let B := A ∩ Ioc (π / 2) π
  have hB : MeasurableSet B := hA.inter measurableSet_Ioc
  have hpre : MeasurableSet (normalReflection ⁻¹' B) := normalReflection.measurable hB
  have hsub : normalReflection ⁻¹' B ⊆ Ico 0 (π / 2) := by
    intro t ht
    have hb : π / 2 < π - t ∧ π - t ≤ π := ht.2
    constructor <;> linarith [hb.1, hb.2]
  have hmass : sigma K B =
      sigma (mirrorCap K (π / 2)) (normalReflection ⁻¹' B) := by
    rw [sigma_eq_map_mirror hK, Measure.map_apply normalReflection.measurable hB]
  have hb := Measure.le_iff'.mp hfirst (normalReflection ⁻¹' B)
  rw [Measure.restrict_apply hpre, inter_eq_left.mpr hsub,
    withDensity_apply _ hpre, Measure.restrict_restrict hpre,
    inter_eq_left.mpr hsub] at hb
  change sigma K B ≤ ∫⁻ t in B, ENNReal.ofReal (k0 (fMinus K (t - π / 2)))
  calc
    sigma K B = sigma (mirrorCap K (π / 2)) (normalReflection ⁻¹' B) := hmass
    _ ≤ ∫⁻ t in normalReflection ⁻¹' B,
        ENNReal.ofReal (k0 (gPlus (mirrorCap K (π / 2)) t)) := hb
    _ = ∫⁻ t in normalReflection ⁻¹' B,
        ENNReal.ofReal (k0 (fMinus K (normalReflection t - π / 2))) := by
      apply lintegral_congr
      intro t
      rw [gPlus_mirror_eq_fMinus, normalReflection_apply,
        show π - t - π / 2 = π / 2 - t by ring]
    _ = ∫⁻ t in B, ENNReal.ofReal (k0 (fMinus K (t - π / 2))) :=
      normalReflection_measurePreserving.setLIntegral_comp_preimage_emb
        normalReflection.measurableEmbedding
        (fun t => ENNReal.ofReal (k0 (fMinus K (t - π / 2)))) B

/-- The second curvature inequality includes the endpoint pi. -/
theorem secondCurvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    SecondCurvatureBound K := by
  apply secondCurvature_of_mirror_first hK
  apply firstCurvature_of_maximal_positive (proposition2_5_4_isCap hK)
  · simpa only [sofaArea_mirror] using hpositive
  · exact maximal_sofaArea_mirror hmax

/-- Both endpoint-safe inequalities for the same specified maximizing cap. -/
theorem curvature_of_maximal_positive {K : Set (ℝ × ℝ)}
    (hK : IsCap K (π / 2)) (hpositive : 0 < sofaArea (π / 2) K)
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    FirstCurvatureBound K ∧ SecondCurvatureBound K :=
  ⟨firstCurvature_of_maximal_positive hK hpositive hmax,
    secondCurvature_of_maximal_positive hK hpositive hmax⟩

end MovingSofaUniqueness

end
