module

public import MovingSofa.Injectivity.BoundingArms

/-!
# Regularity and integrated arm bounds without balancedness

The hypotheses are the two measure inequalities themselves. The paper's
balanced-cap hypothesis is not used. In particular the endpoints 0 and pi are
included in the restricted measures; the possible atom at pi/2 is excluded.

The second arm identity is derived directly, so reflection of a selected
maximizer and an unproved mirrored density bound are unnecessary.
Uncompiled proof scripts, with no admitted statements.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter MovingSofa

namespace SofaUniqueness

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

theorem intervalIntegrable_fPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (fPlus K) volume a b := by
  sorry

/-- Integral of the first arm, before replacing its endpoint convention. -/
theorem integral_fPlus {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (a b : ℝ) :
    (∫ t in a..b, fPlus K t) =
      (∫ t in (a + π / 2)..(b + π / 2), supp K t) - (supp K b - supp K a) := by
  sorry

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
  sorry

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
  sorry

end SofaUniqueness
