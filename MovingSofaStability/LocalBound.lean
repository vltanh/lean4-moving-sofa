module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import MovingSofaStability.Basic
public import MovingSofaStability.CapEstimate
public import MovingSofaStability.LocalGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The upper bound near Gerver's cap

For every right-angle cap close to Gerver's, `A(K) ≤ 𝒬(ξ_K) ≤ |G|` without the injectivity
condition, and the cap lies within `(2 / cos φ) √(|G| - A(K))` of Gerver's cap translated
horizontally (`nearby_cap_certificate`, `nearby_cap_distance`).

The corner path of a nearby cap need not be differentiable, but it has a bounded right velocity.
The proof of Theorem 8.2.4 is repeated with three changes: the curve area of the core is computed
from the right velocity, the area under the core from its graph by a change of variables, and the
injectivity condition is replaced by the separation of the core from the two cuts.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness GerverParams

namespace MovingSofaStability

/-! ## The right velocity of the corner path -/

/-- The right velocity of the corner path of a convex body is bounded. -/
theorem cornerRightVelocity_bound {K : Set Point} (hK : IsConvexBody K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, norm2 (cornerRightVelocity K t) ≤ B := by
  obtain ⟨R, hR⟩ := hK.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  have hradius : ∀ p ∈ K, norm2 p ≤ R := fun p hp => (le_norm_self _).trans (hR p hp)
  have hv : ∀ t, |dot (vplus K t) (vvec t)| ≤ R := fun t => le_trans
    (by simpa only [norm2_vvec, mul_one] using abs_dot_le_norm2_mul (vplus K t) (vvec t))
    (hradius _ (vplus_mem_edge hK t).1)
  have hf : ∀ t, |fPlus K t - 1| ≤ 2 * R + 1 := fun t => by
    have hs := abs_le.mp (support_abs_le_radius hK hradius (t + π / 2))
    have hd := abs_le.mp (hv t)
    rw [inj_fPlus_eq, abs_le]
    constructor <;> linarith
  have hg : ∀ t, |gPlus K t - 1| ≤ 2 * R + 1 := fun t => by
    have hs := abs_le.mp (support_abs_le_radius hK hradius t)
    have hd := abs_le.mp (hv (t + π / 2))
    rw [inj_gPlus_eq, abs_le]
    constructor <;> linarith
  have hB : ∀ t, norm2 (cornerRightVelocity K t) ≤ 4 * R + 2 := fun t => by
    have hh := norm2_add_le (-(fPlus K t - 1) • uvec t) ((gPlus K t - 1) • vvec t)
    rw [norm2_smul, norm2_smul, norm2_uvec, norm2_vvec, mul_one, mul_one, abs_neg] at hh
    exact hh.trans (by linarith [hf t, hg t])
  exact ⟨_, (norm2_nonneg _).trans (hB 0), hB⟩

/-- The right velocity is measurable and bounded, hence interval integrable. -/
theorem cornerRightVelocity_intervalIntegrable {K : Set Point} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (cornerRightVelocity K) volume a b := by
  obtain ⟨B, -, hB⟩ := cornerRightVelocity_bound hK
  have hf : Measurable (fPlus K) := by
    rw [funext (inj_fPlus_eq K)]
    exact (hK.continuous_supp.measurable.comp (measurable_add_const _)).sub (opt_g_measurable hK)
  have hg : Measurable (gPlus K) := by
    rw [funext (inj_gPlus_eq K)]
    exact hK.continuous_supp.measurable.add ((opt_g_measurable hK).comp (measurable_add_const _))
  have hm : Measurable (cornerRightVelocity K) :=
    ((hf.sub_const 1).neg.smul continuous_uvec.measurable).add
      ((hg.sub_const 1).smul continuous_vvec.measurable)
  have h1 := opt_intervalIntegrable_of_bound hm.fst
    (fun t => (abs_fst_le_norm2 _).trans (hB t)) a b
  have h2 := opt_intervalIntegrable_of_bound hm.snd
    (fun t => (abs_snd_le_norm2 _).trans (hB t)) a b
  exact ⟨h1.1.prodMk h2.1, h1.2.prodMk h2.2⟩

/-- The curve area of the corner path is the cross integral of its right velocity: the path is the
primitive of its bounded right velocity, so its vector measure has this density. -/
theorem corner_curveArea_integral {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    curveArea (innerCorner K) a b =
      (1 / 2) * ∫ t in a..b, cross (innerCorner K t) (cornerRightVelocity K t) := by
  have hc := opt_innerCorner_continuous hK.2.1
  have hi : IntegrableOn (cornerRightVelocity K) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      (cornerRightVelocity_intervalIntegrable hK.2.1 a b)
  obtain ⟨B, -, hB⟩ := cornerRightVelocity_bound hK.2.1
  have hb : ∀ t, ‖cornerRightVelocity K t‖ ≤ B.toNNReal := fun t =>
    ((product_norm_le_norm2 _).trans (hB t)).trans (le_coe_toNNReal B)
  have hx : ∀ t ∈ Icc a b,
      innerCorner K t = innerCorner K a + ∫ s in a..t, cornerRightVelocity K s := fun t ht => by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hc.continuousOn
      (fun s _ => corner_hasRightDeriv hK s) (cornerRightVelocity_intervalIntegrable hK.2.1 a t)]
    abel
  obtain ⟨hbv, hcont⟩ := cvx_bv_of_primitive hab hi (fun t _ => hb t) hx
  unfold curveArea curveBilin
  rw [cvx_lsMeasure_eq_withDensityᵥ hab hi hx hbv hcont,
    cvx_withDensityᵥ_restrict hi measurableSet_Icc, Measure.restrict_restrict_of_subset subset_rfl,
    cvx_integral_withDensityᵥ hi (ae_of_all _ hb) crossCLM
      (hc.continuousOn.integrableOn_compact isCompact_Icc),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp only [crossCLM_apply]

/-! ## The core as a Lipschitz graph -/

/-- Continuous extension of a Lipschitz function on an interval by constant end values. -/
theorem continuous_clamped_roof {a b L : ℝ} {γ : ℝ → ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|) :
    Continuous (fun x => γ (max a (min x b))) := by
  have hlip : LipschitzOnWith L.toNNReal γ (Icc a b) := .of_dist_le_mul fun x hx y hy => by
    simpa only [Real.dist_eq, coe_toNNReal _ hL] using hLip x hx y hy
  exact hlip.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)

/-- Uniform core-arm margins give a finite slope bound for every core chord: the height changes at
most at the speed bound, and the abscissa decreases at least at the margin. -/
theorem core_verticalSlopeBound {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (innerCorner K '' Icc a b) L := by
  obtain ⟨B, hB, hvel⟩ := cornerRightVelocity_bound hK.2.1
  have hY := (opt_innerCorner_continuous hK.2.1).snd
  have hdY : ∀ t, |(cornerRightVelocity K t).2| ≤ B := fun t =>
    (abs_snd_le_norm2 _).trans (hvel t)
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      |(innerCorner K u).2 - (innerCorner K v).2| ≤
        B / c * |(innerCorner K u).1 - (innerCorner K v).1| := by
    intro u hu v hv huv
    have hX := hmargin.horizontal_decrease hK hc.le ha hb hu hv huv
    have hup := right_derivative_increment_le huv hY.continuousOn
      (fun t _ => (corner_hasRightDeriv hK t).snd) (fun t _ => (abs_le.mp (hdY t)).2)
    have hlow := right_derivative_increment_ge huv hY.continuousOn
      (fun t _ => (corner_hasRightDeriv hK t).snd) (B := -B) (fun t _ => (abs_le.mp (hdY t)).1)
    have hdec : c * (v - u) ≤ (innerCorner K u).1 - (innerCorner K v).1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hdec (div_nonneg hB hc.le)
    rw [← mul_assoc, div_mul_cancel₀ _ hc.ne'] at hm
    rw [abs_of_nonneg ((mul_nonneg hc.le (sub_nonneg.mpr huv)).trans hdec)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨B / c, div_nonneg hB hc.le, ?_⟩
  rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
  rcases le_total u v with huv | hvu
  · exact ordered u hu v hv huv
  · simpa only [abs_sub_comm] using ordered v hv u hu hvu

/-- A continuous full-line graph function agreeing with the entire core. -/
theorem exists_core_graph {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hab : a < b) (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      (∀ t ∈ Icc a b, F (innerCorner K t).1 = (innerCorner K t).2) ∧
      (∀ y ∈ Icc (innerCorner K b).1 (innerCorner K a).1,
        ∃ t ∈ Icc a b, (innerCorner K t).1 = y) := by
  have hanti := (hmargin.strictAnti_core hK hc ha hb).antitoneOn
  have hcover : ∀ y ∈ Icc (innerCorner K b).1 (innerCorner K a).1,
      ∃ t ∈ Icc a b, (innerCorner K t).1 = y := fun y hy =>
    intermediate_value_Icc' hab.le (opt_innerCorner_continuous hK.2.1).fst.continuousOn hy
  have hrange : ∀ p ∈ innerCorner K '' Icc a b,
      p.1 ∈ Icc (innerCorner K b).1 (innerCorner K a).1 := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨hanti ht ⟨hab.le, le_rfl⟩ ht.2, hanti ⟨le_rfl, hab.le⟩ ht ht.1⟩
  obtain ⟨L, hL, hSlope⟩ := core_verticalSlopeBound hK hmargin hc ha hb
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function hrange (fun y hy =>
    let ⟨t, ht, he⟩ := hcover y hy; ⟨_, mem_image_of_mem _ ht, he⟩) hSlope
  refine ⟨_, continuous_clamped_roof (hrange _ (mem_image_of_mem _ ⟨le_rfl, hab.le⟩)).1 hL hLip,
    fun t ht => ?_, hcover⟩
  have hp := hrange _ (mem_image_of_mem _ ht)
  simp only [min_eq_left hp.2, max_eq_right hp.1]
  exact ((hgraph _).1 (mem_image_of_mem _ ht)).2.symm

/-! ## The area under the core -/

/-- Substitution `∫_a^b F(X t) X'(t) dt = ∫_{X a}^{X b} F` for a continuous `F` and a continuous
`X` with right derivative `X'`. -/
theorem integral_comp_mul_rightDerivative {X X' F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hF : Continuous F)
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt X (X' t) (Ioi t) t)
    (hi : IntervalIntegrable (fun t => F (X t) * X' t) volume a b) :
    (∫ t in a..b, F (X t) * X' t) = ∫ x in X a..X b, F x := by
  have hP : ∀ x, HasDerivAt (fun x => ∫ y in X a..x, F y) (F x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((continuous_iff_continuousAt.mpr fun x => (hP x).continuousAt).comp_continuousOn hX)
    (fun t ht => (hP (X t)).comp_hasDerivWithinAt t (hd t ht)) hi
  simpa only [Function.comp_apply, intervalIntegral.integral_same, sub_zero] using h

/-- The region under a strictly decreasing positive core is the region between the floor and the
graph of `exists_core_graph`; the change of variables gives its area. -/
theorem volume_under_core_graph {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hab : a < b) (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) (hY : ∀ t ∈ Icc a b, 0 < (innerCorner K t).2) :
    volume ((fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
      {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2}) =
      ENNReal.ofReal (∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2) := by
  obtain ⟨F, hF, hgraph, hcover⟩ := exists_core_graph hK hab hmargin hc ha hb
  have hanti := hmargin.strictAnti_core hK hc ha hb
  have ha' : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb' : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hset : (fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
      {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2} =
      regionBetween (fun _ => 0) F (Ioo (innerCorner K b).1 (innerCorner K a).1) := by
    ext p
    constructor
    · rintro ⟨⟨t, s⟩, ⟨ht, hs0, hsY⟩, rfl⟩
      have ht' := Ioo_subset_Icc_self ht
      exact ⟨⟨hanti ht' hb' ht.2, hanti ha' ht' ht.1⟩, show 0 < _ - s by linarith,
        show _ - s < F _ by linarith [hgraph t ht']⟩
    · rintro ⟨hp, hp0, hpF⟩
      obtain ⟨t, ht, htx⟩ := hcover p.1 (Ioo_subset_Icc_self hp)
      rw [← htx] at hp hpF
      rw [hgraph t ht] at hpF
      exact ⟨(t, (innerCorner K t).2 - p.2), ⟨⟨(hanti.lt_iff_gt ht ha').1 hp.2,
        (hanti.lt_iff_gt hb' ht).1 hp.1⟩, by simp only at hpF ⊢; linarith,
        by simp only at hp0 ⊢; linarith⟩, Prod.ext htx (sub_sub_cancel _ _)⟩
  have hheight : ∀ x ∈ Ioo (innerCorner K b).1 (innerCorner K a).1, (0 : ℝ) ≤ F x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hcover x (Ioo_subset_Icc_self hx)
    exact (hgraph t ht).symm ▸ (hY t ht).le
  rw [hset, Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo hheight,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (hanti.antitoneOn ha' hb' hab.le)]
  have hX := (opt_innerCorner_continuous hK.2.1).fst
  have hv := cornerRightVelocity_intervalIntegrable hK.2.1 a b
  have he := integral_comp_mul_rightDerivative hab.le hX.continuousOn hF
    (fun t _ => (corner_hasRightDeriv hK t).fst)
    (IntervalIntegrable.continuousOn_mul ⟨hv.1.fst, hv.2.fst⟩ (hF.comp hX).continuousOn)
  simp only [Pi.sub_apply, sub_zero]
  rw [intervalIntegral.integral_symm, ← he, ← intervalIntegral.integral_neg]
  refine congrArg _ (intervalIntegral.integral_congr fun t ht => ?_)
  rw [uIcc_of_le hab.le] at ht
  simp only [hgraph t ht]
  ring

/-- Integration by parts for the curve area of the core, through the right velocity only. -/
theorem core_curveArea_rightVelocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    curveArea (innerCorner K) a b =
      ((innerCorner K b).1 * (innerCorner K b).2 - (innerCorner K a).1 * (innerCorner K a).2) / 2 +
      ∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2 := by
  have hv := cornerRightVelocity_intervalIntegrable hK.2.1 a b
  have hc := opt_innerCorner_continuous hK.2.1
  have h1 : IntervalIntegrable (fun t => (cornerRightVelocity K t).1 * (innerCorner K t).2)
      volume a b := .mul_continuousOn ⟨hv.1.fst, hv.2.fst⟩ hc.snd.continuousOn
  have h2 : IntervalIntegrable (fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2)
      volume a b := .continuousOn_mul ⟨hv.1.snd, hv.2.snd⟩ hc.fst.continuousOn
  have hprod := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun t => (innerCorner K t).1 * (innerCorner K t).2) hab (hc.fst.mul hc.snd).continuousOn
    (fun t _ => HasDerivWithinAt.mul (corner_hasRightDeriv hK t).fst
      (corner_hasRightDeriv hK t).snd) (h1.add h2)
  have hcross : ∫ t in a..b, cross (innerCorner K t) (cornerRightVelocity K t) =
      (∫ t in a..b, (innerCorner K t).1 * (cornerRightVelocity K t).2) -
        ∫ t in a..b, (cornerRightVelocity K t).1 * (innerCorner K t).2 := by
    rw [← intervalIntegral.integral_sub h2 h1]
    exact intervalIntegral.integral_congr fun t _ => by simp only [cross]; ring
  rw [intervalIntegral.integral_add h1 h2] at hprod
  rw [corner_curveArea_integral hK hab, hcross]
  simp only [neg_mul, intervalIntegral.integral_neg]
  linarith

/-! ## Separation from the two cuts

Close to a cut the core moves away from it at a uniform rate; away from the cut the strict margin
of the reference cap persists. No derivative control near the ends `0` and `π/2` is assumed. -/

/-- The core stays off both cuts: `𝐱_K(t) ∉ H̆_K^R` for `t ∈ (φ, π/2]` and `𝐱_K(t) ∉ H̆_K^L` for
`t ∈ [0, π/2 - φ)`. -/
def CutSeparated (φ : ℝ) (K : Set Point) : Prop :=
  (∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1) ∧
  (∀ t ∈ Ico 0 (π / 2 - φ),
    dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1)

theorem innerCorner_projection_error {K K₀ : Set Point} {δ t : ℝ}
    (h : UpperSupportClose δ K K₀) (ht : t ∈ Icc (0 : ℝ) (π / 2)) (a : ℝ) :
    |dot (innerCorner K t) (uvec a) - dot (innerCorner K₀ t) (uvec a)| ≤ 2 * δ := by
  have hp := abs_dot_le_norm2_mul (innerCorner K t - innerCorner K₀ t) (uvec a)
  rw [dot_sub_left, norm2_uvec, mul_one] at hp
  exact hp.trans (innerCorner_support_error h ht)

/-- Separation from the right cut, up to times arbitrarily close to `π/2`. -/
theorem nearby_right_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1 := by
  have hpi := pi_pos
  obtain ⟨m, hφm, hmv⟩ := exists_between (show φ < π / 2 by linarith [hφ.2])
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ := core_arm_margin_near_reference hK₀ hφ.1 hφm.le hmv
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' (s := Icc m (π / 2))
    (f := fun t => supp K₀ φ - 1 - dot (innerCorner K₀ t) (uvec φ))
    (continuous_const.sub ((continuous_dot (uvec φ)).comp
      (opt_innerCorner_continuous hK₀.1.2.1))).continuousOn
    (fun t ht => sub_pos.mpr (opt_innerCorner_lt_right hφ hK₀ ⟨hφm.trans_le ht.1, ht.2⟩))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  by_cases htm : t ≤ m
  · have hinc := right_derivative_increment_le (f := fun s => dot (innerCorner K s) (uvec φ))
      ht.1.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn (uvec φ))
      (fun s _ => hasRightDeriv_dot_uvec (corner_hasRightDeriv hK s))
      (B := -c) (fun s hs => (hA K hK (hclose.mono (min_le_left _ _))).right_cut_velocity hK
        hc.le ⟨hs.1.le, hs.2.le.trans htm⟩ ⟨by linarith [hs.1], by linarith [hs.2, ht.2, hφ.1]⟩)
    rw [(cn_innerCorner_dot K φ).1] at hinc
    linarith [mul_pos hc (sub_pos.mpr ht.1)]
  · have he := innerCorner_projection_error hclose ⟨(hφ.1.trans ht.1).le, ht.2⟩ φ
    have hs := hclose φ ⟨hφ.1.le, by linarith [hφ.2]⟩
    linarith [(abs_le.mp he).2, (abs_le.mp hs).1, hgap t ⟨(not_le.mp htm).le, ht.2⟩,
      min_le_right δA (g / 4)]

/-- Separation from the left cut, without assuming that all left arm lengths of the competing cap
exceed one. -/
theorem nearby_left_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ico 0 (π / 2 - φ),
          dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  have hpi := pi_pos
  obtain ⟨m, hm0, hmb⟩ := exists_between (show 0 < π / 2 - φ by linarith [hφ.2])
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ :=
    core_arm_margin_near_reference hK₀ hm0 hmb.le (by linarith [hφ.1])
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' (s := Icc 0 m)
    (f := fun t => supp K₀ (π / 2 - φ + π / 2) - 1 - dot (innerCorner K₀ t) (vvec (π / 2 - φ)))
    (continuous_const.sub ((continuous_dot (vvec (π / 2 - φ))).comp
      (opt_innerCorner_continuous hK₀.1.2.1))).continuousOn
    (fun t ht => sub_pos.mpr (opt_innerCorner_lt_left hφ hK₀ ⟨ht.1, ht.2.trans_lt hmb⟩))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  by_cases hmt : m ≤ t
  · have hinc := right_derivative_increment_ge
      (f := fun s => dot (innerCorner K s) (vvec (π / 2 - φ)))
      ht.2.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn _)
      (fun s _ => by
        simpa only [uvec_add_pi_div_two] using
          hasRightDeriv_dot_uvec (d := π / 2 - φ + π / 2) (corner_hasRightDeriv hK s))
      (B := c) (fun s hs => by
        simpa only [uvec_add_pi_div_two] using
          (hA K hK (hclose.mono (min_le_left _ _))).left_cut_velocity hK hc.le
            ⟨hmt.trans hs.1.le, hs.2.le⟩ ⟨by linarith [hs.2], by linarith [hs.1, ht.1, hφ.1]⟩)
    rw [opt_innerCorner_dot_v] at hinc
    linarith [mul_pos hc (sub_pos.mpr ht.2)]
  · have he := innerCorner_projection_error hclose ⟨ht.1, by linarith [ht.2, hφ.1]⟩
      (π / 2 - φ + π / 2)
    rw [uvec_add_pi_div_two] at he
    have hs := hclose (π / 2 - φ + π / 2) ⟨by linarith, by linarith [hφ.1]⟩
    linarith [(abs_le.mp he).2, (abs_le.mp hs).1, hgap t ⟨ht.1, (not_le.mp hmt).le⟩,
      min_le_right δA (g / 4)]

/-- Both cuts are separated in one fixed neighborhood. -/
theorem nearby_cutSeparated {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → CutSeparated P.φ K := by
  have hφ := gm_φ_mem_Ioo hP hbox
  have hK₀ := theorem8_1_1_gerver hP hbox
  obtain ⟨δR, hR, hR1, hright⟩ := nearby_right_cut_separation hφ hK₀
  obtain ⟨δL, hL, hL1, hleft⟩ := nearby_left_cut_separation hφ hK₀
  exact ⟨min δR δL, lt_min hR hL, (min_le_left _ _).trans hR1,
    fun K hK hclose => ⟨hright K hK (hclose.mono (min_le_left _ _)),
      hleft K hK (hclose.mono (min_le_right _ _))⟩⟩

/-! ## The tail areas

Lemmas 8.1.6 and 8.2.2 under the cut separation, the canonical contacts and the finite niche area,
in place of the injectivity condition. -/

/-- Inside the right cut half-plane only one of the two wedge inequalities remains. -/
theorem separated_right_wedge {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t : ℝ} (ht : t ∈ Ioc φ (π / 2)) :
    hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t ∧
      hRight φ K ∩ wedge K (π / 2) t = (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K t := by
  have hlt := hsep.1 t ht
  have hpi := pi_pos
  have h2 : hRight φ K ∩ qMinus K t = hRight φ K \ halfB K t := by
    ext p
    simp only [hRight, halfB, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    refine ⟨fun ⟨hp, h1, _⟩ => ⟨hp, h1⟩, fun ⟨hp, h1⟩ => ⟨hp, h1, ?_⟩⟩
    by_contra hcon
    push Not at hcon
    have e1 := dot_uvec_eq_cos_add_sin p φ t
    have e2 := dot_uvec_eq_cos_add_sin (innerCorner K t) φ t
    rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
    have hc : 0 ≤ cos (φ - t) :=
      (cos_pos_of_mem_Ioo ⟨by linarith [ht.2, hφ.1], by linarith [ht.1]⟩).le
    have hs : sin (φ - t) ≤ 0 :=
      (sin_neg_of_neg_of_neg_pi_lt (by linarith [ht.1]) (by linarith [ht.2, hφ.1])).le
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc
        (by linarith : dot p (uvec t) - (supp K t - 1) ≤ 0),
      mul_nonpos_of_nonpos_of_nonneg hs
        (by linarith : 0 ≤ dot p (vvec t) - (supp K (t + π / 2) - 1))]
  refine ⟨h2, Set.ext fun p => ?_⟩
  have he := Set.ext_iff.mp h2 p
  simp only [wedge, fan, mem_inter_iff, mem_sdiff] at he ⊢
  tauto

/-- The corresponding reduction in the left cut half-plane. -/
theorem separated_left_wedge {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t : ℝ} (ht : t ∈ Ico 0 (π / 2 - φ)) :
    hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t ∧
      hLeft φ K ∩ wedge K (π / 2) t = (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K t := by
  have hlt := hsep.2 t ht
  have hpi := pi_pos
  have h2 : hLeft φ K ∩ qMinus K t = hLeft φ K \ halfD K t := by
    ext p
    simp only [hLeft, halfD, halfPlus, mem_inter_iff, mem_sdiff, mem_ofPred_eq,
      proposition2_2_2_qMinus, halfMinusOpen, not_le, uvec_add_pi_div_two]
    refine ⟨fun ⟨hp, _, h1⟩ => ⟨hp, h1⟩, fun ⟨hp, h1⟩ => ⟨hp, ?_, h1⟩⟩
    by_contra hcon
    push Not at hcon
    have e1 := opt_dot_frame_v p (π / 2 - φ) t
    have e2 := opt_dot_frame_v (innerCorner K t) (π / 2 - φ) t
    rw [(cn_innerCorner_dot K t).1, opt_innerCorner_dot_v] at e2
    have hc : 0 < cos (π / 2 - φ - t) :=
      cos_pos_of_mem_Ioo ⟨by linarith [ht.2], by linarith [ht.1, hφ.1]⟩
    have hs : 0 ≤ sin (π / 2 - φ - t) :=
      (sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1, hφ.1])).le
    nlinarith [mul_nonneg hs (by linarith : 0 ≤ dot p (uvec t) - (supp K t - 1)),
      mul_neg_of_pos_of_neg hc
        (by linarith : dot p (vvec t) - (supp K (t + π / 2) - 1) < 0)]
  refine ⟨h2, Set.ext fun p => ?_⟩
  have he := Set.ext_iff.mp h2 p
  simp only [wedge, fan, mem_inter_iff, mem_sdiff] at he ⊢
  tauto

/-- The tail-area inequalities of Lemma 8.2.2 under the cut separation. -/
theorem separated_tail_areas {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2)) (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (htriple : InWideL φ K (rightBody φ K) (leftBody φ K)) (hsep : CutSeparated φ K) :
    segArea (xB φ (rightBody φ K)) (wRight φ K) -
        convexCurveArea (rightBody φ K) (π + φ) (3 * π / 2) ≤
      area (niche K (π / 2) ∩ hRight φ K) ∧
    segArea (zLeft φ K) (yD φ (leftBody φ K)) -
        convexCurveArea (leftBody φ K) (3 * π / 2) (3 * π / 2 + (π / 2 - φ)) ≤
      area (niche K (π / 2) ∩ hLeft φ K) := by
  obtain ⟨hφ0, hφ4, -, -, -⟩ := opt_phi_bounds hφ
  have hpi := two_le_pi
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp htriple
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  have hfin : ∀ A ⊆ niche K (π / 2), volume A ≠ ⊤ := fun A hA =>
    volume_ne_top_of_subset hA (nef_niche_isBounded hK).measure_lt_top.ne
  constructor
  · have hvint := opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
    have hsub : ∀ p ∈ K, p ∉ rightBody φ K →
        p ∈ suppHalf (rightBody φ K) (π + φ) ∩ suppHalf (rightBody φ K) (3 * π / 2) →
        p ∈ niche K (π / 2) ∩ hRight φ K := by
      intro p hpK hpB ⟨hpR', hp2⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hBa] at hpR'
      rw [show π + φ = φ + π by ring, dot_uvec_add_pi] at hpR'
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hB3, dot_uvec_three_pi_div_two] at hp2
      have hpR : p ∈ hRight φ K := by
        simp only [hRight, halfB, halfPlus, mem_ofPred_eq]; linarith
      obtain ⟨s, hs, hps⟩ := not_forall₂.mp fun h => hpB ⟨hpK, mem_iInter₂.mpr h⟩
      have hsφ : φ < s := lt_of_le_of_ne hs.1 (by rintro rfl; exact hps hpR)
      have hsv : s < π / 2 := lt_of_le_of_ne hs.2 (by
        rintro rfl
        apply hps
        simp only [halfB, halfPlus, mem_ofPred_eq, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hpw : p ∈ (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K s := by
        refine ⟨⟨hpR, ?_⟩, hps⟩
        simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
      rw [← (separated_right_wedge ⟨hφ0, hφ4⟩ hsep ⟨hsφ, hsv.le⟩).2] at hpw
      exact ⟨⟨hpw.2.1, mem_iUnion₂.mpr ⟨s, ⟨by linarith, hsv⟩, hpw.2.2⟩⟩, hpR⟩
    have he := opt_tail_area_le htriple.2.1 (by linarith) (by linarith) inter_subset_left
      hK.2.1.2.2 (by rw [hvint]; exact hW.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero rfl (opt_snd_vminus_three_pi_div_two hB3), add_zero] at he
  · have hvint := opt_vint_left_eq hD3 hDb
    have hsub : ∀ p ∈ K, p ∉ leftBody φ K →
        p ∈ suppHalf (leftBody φ K) (3 * π / 2) ∩
          suppHalf (leftBody φ K) (3 * π / 2 + (π / 2 - φ)) →
        p ∈ niche K (π / 2) ∩ hLeft φ K := by
      intro p hpK hpD ⟨hp2, hpL'⟩
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hD3, dot_uvec_three_pi_div_two] at hp2
      simp only [suppHalf, halfMinus, mem_ofPred_eq, hDb] at hpL'
      rw [show 3 * π / 2 + (π / 2 - φ) = (π - φ) + π by ring, dot_uvec_add_pi] at hpL'
      have hpL : p ∈ hLeft φ K := by
        simp only [hLeft, halfD, halfPlus, mem_ofPred_eq,
          show π / 2 - φ + π / 2 = π - φ by ring]
        linarith
      obtain ⟨s, hs, hps⟩ := not_forall₂.mp fun h => hpD ⟨hpK, mem_iInter₂.mpr h⟩
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by
        rintro rfl
        apply hps
        simp only [halfD, halfPlus, mem_ofPred_eq, zero_add, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hsψ : s < π / 2 - φ := lt_of_le_of_ne hs.2 (by rintro rfl; exact hps hpL)
      have hpw : p ∈ (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K s := by
        refine ⟨⟨hpL, ?_⟩, hps⟩
        simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
      rw [← (separated_left_wedge ⟨hφ0, hφ4⟩ hsep ⟨hs0.le, hsψ⟩).2] at hpw
      exact ⟨⟨hpw.2.1, mem_iUnion₂.mpr ⟨s, ⟨hs0, by linarith⟩, hpw.2.2⟩⟩, hpL⟩
    have he := opt_tail_area_le htriple.2.2.1 (by linarith) (by linarith) inter_subset_left
      hK.2.1.2.2 (by rw [hvint]; exact hZ.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3)
      (by rw [opt_zLeft_eq]), zero_add] at he

/-! ## The core area

Gerver's core lies strictly above the floor, and so does the core of every nearby cap. The region
under the core and the two triangles at its ends are then disjoint subsets of the middle part of the
niche, and their areas give the bound of Lemma 8.2.3 without the auxiliary trapezoid. -/

/-- Core height stays uniformly positive in a neighborhood of Gerver's cap. -/
theorem nearby_core_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      UpperSupportClose δ K P.cap → ∀ t ∈ Icc P.φ (π / 2 - P.φ),
        0 < (innerCorner K t).2 := by
  have hφ := gm_φ_mem_Ioo hP hbox
  have hsub : Icc P.φ (π / 2 - P.φ) ⊆ Icc 0 (π / 2) := Icc_subset_Icc hφ.1.le (by linarith [hφ.1])
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le'
    (opt_innerCorner_continuous (gm_isConvexBody_cap hP hbox)).snd.continuousOn
    (fun t ht => by
      rw [((theorem8_4_1_monotone hP hbox).2 t (hsub ht)).2.2]
      exact (gn_envHyp hP (romik_bounds hP hbox)).x_pos t ht)
  refine ⟨min 1 (m / 4), lt_min one_pos (by linarith), min_le_left _ _, fun K hclose t ht => ?_⟩
  have hd := (abs_le.mp ((abs_snd_le_norm2 _).trans
    (innerCorner_support_error hclose (hsub ht)))).1
  simp only [Prod.snd_sub] at hd
  linarith [hmin t ht, min_le_right 1 (m / 4)]

/-- Every point strictly below an interior core point belongs to its forbidden
quadrant and lies outside both cuts. -/
theorem separated_core_below {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t s : ℝ}
    (ht : t ∈ Ioo φ (π / 2 - φ)) (hs : 0 < s) :
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hRight φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hLeft φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∈ qMinus K t := by
  have hpi := pi_pos
  have ht' : t ∈ Ioo 0 (π / 2) := ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1]⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht'.1 (by linarith [ht'.2])
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht'.1], ht'.2⟩
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have e1 := hsep.1 t ⟨ht.1, ht'.2.le⟩
  have e2 := hsep.2 t ⟨ht'.1.le, ht.2⟩
  have e3 := (cn_innerCorner_dot K t).1
  have e4 := opt_innerCorner_dot_v K t
  simp only [dot, uvec, vvec] at e1 e2 e3 e4
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at e2
  refine ⟨?_, ?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos hs hs0]
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two,
      dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos hs hs0]
  · rw [proposition2_2_2_qMinus]
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, dot, uvec, cos_add_pi_div_two,
      sin_add_pi_div_two]
    constructor <;> nlinarith [mul_pos hs hst, mul_pos hs hct]

/-- The small right triangular region is inside a cut-endpoint wedge. -/
theorem separated_right_triangle {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {p : Point}
    (h1 : (innerCorner K φ).1 < p.1) (h2 : p.2 < (innerCorner K φ).2)
    (h3 : p ∉ hRight φ K) : p ∉ hLeft φ K ∧ p ∈ qMinus K φ := by
  have hpi := pi_pos
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e2 := hsep.2 φ ⟨hφ.1.le, by linarith [hφ.2]⟩
  have e4 := opt_innerCorner_dot_v K φ
  simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e2 e4
  refine ⟨?_, ?_⟩
  · simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le, uvec_add_pi_div_two,
      dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hc, mul_pos (sub_pos.mpr h2) hs]
  · rw [proposition2_2_2_qMinus]
    simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq, uvec_add_pi_div_two]
    refine ⟨h3, ?_⟩
    simp only [dot, vvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hs, mul_pos (sub_pos.mpr h2) hc]

/-- The matching left triangular region. -/
theorem separated_left_triangle {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {p : Point}
    (h1 : p.1 < (innerCorner K (π / 2 - φ)).1)
    (h2 : p.2 < (innerCorner K (π / 2 - φ)).2)
    (h3 : p ∉ hLeft φ K) : p ∉ hRight φ K ∧ p ∈ qMinus K (π / 2 - φ) := by
  have hpi := pi_pos
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2])
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have e1 := hsep.1 (π / 2 - φ) ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  have e3 := (cn_innerCorner_dot K (π / 2 - φ)).1
  simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at e1 e3
  refine ⟨?_, ?_⟩
  · simp only [hRight, halfB, halfPlus, mem_ofPred_eq, not_le, dot, uvec]
    nlinarith [mul_pos (sub_pos.mpr h1) hc, mul_pos (sub_pos.mpr h2) hs]
  · rw [proposition2_2_2_qMinus]
    simp only [hLeft, halfD, halfPlus, mem_ofPred_eq, not_le] at h3
    simp only [mem_inter_iff, halfMinusOpen, mem_ofPred_eq]
    refine ⟨?_, h3⟩
    simp only [dot, uvec, sin_pi_div_two_sub, cos_pi_div_two_sub]
    nlinarith [mul_pos (sub_pos.mpr h1) hs, mul_pos (sub_pos.mpr h2) hc]

/-- Core-area lower bound under the geometric hypotheses available near Gerver's cap. -/
theorem positive_core_area_le {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hK : IsCap K (π / 2))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
      segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  obtain ⟨hφ0, hφ4⟩ := hφ
  have hpi := pi_pos
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hab : φ < π / 2 - φ := by linarith
  have hbv : π / 2 - φ < π / 2 := by linarith
  have hw : (supp K φ - 1) / cos φ =
      (innerCorner K φ).1 + (innerCorner K φ).2 * (sin φ / cos φ) := by
    have he := (cn_innerCorner_dot K φ).1
    simp only [dot, uvec] at he
    rw [div_eq_iff hcos.ne', add_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  have hz : (1 - supp K (π - φ)) / cos φ =
      (innerCorner K (π / 2 - φ)).1 - (innerCorner K (π / 2 - φ)).2 * (sin φ / cos φ) := by
    have he := opt_innerCorner_dot_v K (π / 2 - φ)
    rw [show π / 2 - φ + π / 2 = π - φ by ring] at he
    simp only [dot, vvec, sin_pi_div_two_sub, cos_pi_div_two_sub] at he
    rw [div_eq_iff hcos.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  set b := π / 2 - φ
  set τ := sin φ / cos φ
  set w := (supp K φ - 1) / cos φ
  set z := (1 - supp K (π - φ)) / cos φ
  set XR := (innerCorner K φ).1
  set YR := (innerCorner K φ).2
  set XL := (innerCorner K b).1
  set YL := (innerCorner K b).2
  have hτ : 0 < τ := div_pos hsin hcos
  have hYR : 0 < YR := hheight φ ⟨le_rfl, hab.le⟩
  have hYL : 0 < YL := hheight b ⟨hab.le, le_rfl⟩
  have hanti := hcore.strictAnti_core hK hc hφ0.le hbv.le
  have hX : XL < XR := hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  -- the region under the core and the two end triangles
  let C : Set Point := (fun q : Point => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
    {q : Point | q.1 ∈ Ioo φ b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2}
  let R : Set Point := {p | 0 < p.2 ∧ p.2 < YR ∧ XR + 0 * p.2 < p.1 ∧ p.1 < w + -τ * p.2}
  let L : Set Point := {p | 0 < p.2 ∧ p.2 < YL ∧ z + τ * p.2 < p.1 ∧ p.1 < XL + 0 * p.2}
  let I : ℝ := ∫ t in φ..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hab.le fun t ht => mul_nonneg
    (by linarith [hcore.velocity_fst_le hK hc.le ht ⟨hφ0.le.trans ht.1, ht.2.trans hbv.le⟩])
    (hheight t ht).le
  have vC : volume C = ENNReal.ofReal I :=
    volume_under_core_graph hK hab hcore hc hφ0.le hbv.le hheight
  have vR : volume R = ENNReal.ofReal (τ * YR ^ 2 / 2) := by
    rw [opt_volume_hregion hYR.le fun y hy => by
      rw [hw]; nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)], hw]
    congr 1
    ring
  have vL : volume L = ENNReal.ofReal (τ * YL ^ 2 / 2) := by
    rw [opt_volume_hregion hYL.le fun y hy => by
      rw [hz]; nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)], hz]
    congr 1
    ring
  have hCfst : ∀ p ∈ C, XL < p.1 ∧ p.1 < XR := by
    rintro p ⟨⟨t, s⟩, ⟨ht, -, -⟩, rfl⟩
    exact ⟨hanti (Ioo_subset_Icc_self ht) ⟨hab.le, le_rfl⟩ ht.2,
      hanti ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self ht) ht.1⟩
  have hdisjR : Disjoint C R := Set.disjoint_left.mpr fun p hp hq => by
    linarith [(hCfst p hp).2, hq.2.2.1]
  have hdisjL : Disjoint (C ∪ R) L := Set.disjoint_left.mpr fun p hp hq => by
    rcases hp with hp | hp
    · linarith [(hCfst p hp).1, hq.2.2.2]
    · linarith [hp.2.2.1, hq.2.2.2]
  have hopen : ∀ a b A B D E : ℝ,
      IsOpen {p : Point | a < p.2 ∧ p.2 < b ∧ A + B * p.2 < p.1 ∧ p.1 < D + E * p.2} :=
    fun a b A B D E => (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_fst).inter (isOpen_lt continuous_fst (by fun_prop))))
  have hsub : C ∪ R ∪ L ⊆ (niche K (π / 2) \ hRight φ K) \ hLeft φ K := by
    intro p hp
    have key : 0 ≤ p.2 ∧ p ∉ hRight φ K ∧ p ∉ hLeft φ K ∧
        ∃ t ∈ Ioo (0 : ℝ) (π / 2), p ∈ qMinus K t := by
      rcases hp with (hp | hp) | hp
      · obtain ⟨⟨t, s⟩, ⟨ht, hs0, hsY⟩, rfl⟩ := hp
        obtain ⟨hR, hL, hq⟩ := separated_core_below ⟨hφ0, hφ4⟩ hsep ht hs0
        exact ⟨by dsimp only; linarith, hR, hL, t, ⟨hφ0.trans ht.1, ht.2.trans hbv⟩, hq⟩
      · obtain ⟨hy0, hyR, hxR, hxw⟩ := hp
        have hR : p ∉ hRight φ K := (opt_notMem_hRight_iff hcos K p).2 (by linarith)
        obtain ⟨hL, hq⟩ := separated_right_triangle ⟨hφ0, hφ4⟩ hsep (by linarith) hyR hR
        exact ⟨hy0.le, hR, hL, φ, ⟨hφ0, by linarith⟩, hq⟩
      · obtain ⟨hy0, hyL, hxz, hxL⟩ := hp
        have hL : p ∉ hLeft φ K := (opt_notMem_hLeft_iff hcos K p).2 (by linarith)
        obtain ⟨hR, hq⟩ := separated_left_triangle ⟨hφ0, hφ4⟩ hsep (by linarith) hyL hL
        exact ⟨hy0.le, hR, hL, b, ⟨by linarith, hbv⟩, hq⟩
    obtain ⟨hy0, hR, hL, t, ht, hq⟩ := key
    refine ⟨⟨⟨?_, mem_iUnion₂.mpr ⟨t, ht, hq⟩⟩, hR⟩, hL⟩
    simpa [fan, halfPlus, dot_uvec_pi_div_two] using hy0
  have harea := area_mono_of_finite hsub (volume_ne_top_of_subset (sdiff_subset.trans sdiff_subset)
    (nef_niche_isBounded hK).measure_lt_top.ne)
  have aUnion : area (C ∪ R ∪ L) = I + τ * YR ^ 2 / 2 + τ * YL ^ 2 / 2 := by
    unfold area
    rw [measure_union hdisjL (hopen 0 YL z τ XL 0).measurableSet,
      measure_union hdisjR (hopen 0 YR XR 0 w (-τ)).measurableSet, vC, vR, vL,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
  have hsegR : segArea (wRight φ K) (xRight φ K) = w * YR / 2 := by
    simp only [opt_wRight_eq, xRight, segArea, cross]
    ring
  have hsegL : segArea (xLeft φ K) (zLeft φ K) = -YL * z / 2 := by
    simp only [opt_zLeft_eq, xLeft, segArea, cross]
    ring
  rw [hsegR, hsegL, core_curveArea_rightVelocity hK hab.le]
  calc w * YR / 2 + ((XL * YL - XR * YR) / 2 + I) + -YL * z / 2
      = area (C ∪ R ∪ L) := by rw [aUnion, hw, hz]; ring
    _ ≤ _ := harea

/-! ## The local upper bound

Canonical tails, cut separation, positive core height and niche containment hold on a common
neighborhood of Gerver's cap, where the three-region argument gives `A(K) ≤ 𝒬(ξ_K)`. The
coercive certificate (`coercive_certificate`) at the canonical triple then gives `𝒬(ξ_K) ≤ |G|`
and the cap distance. -/

/-- The geometric certificate on a cap with separated, positive, monotone core. -/
theorem separated_upperQ_bound {φ c : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set Point} (hK : IsCap K (π / 2))
    (hwidth : (21 / 10 : ℝ) ≤ bottomWidth K)
    (htriple : InWideL φ K (rightBody φ K) (leftBody φ K))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2)
    (hNK : niche K (π / 2) ⊆ K) :
    sofaArea (π / 2) K ≤ upperQ φ K (rightBody φ K) (leftBody φ K) := by
  obtain ⟨hφ0, hφ4, -, hc9, -⟩ := opt_phi_bounds hφ
  have hcos : 0 < cos φ := by linarith
  have hfin : volume (niche K (π / 2)) ≠ ⊤ := (nef_niche_isBounded hK).measure_lt_top.ne
  have hdisj := cut_regions_disjoint_of_width hφ hK hwidth
  have he3 : (niche K (π / 2) \ hRight φ K) ∩ hLeft φ K = niche K (π / 2) ∩ hLeft φ K :=
    Set.ext fun p => ⟨fun ⟨⟨hp, _⟩, hL⟩ => ⟨hp, hL⟩, fun ⟨hp, hL⟩ =>
      ⟨⟨hp, fun hR => Set.disjoint_left.mp hdisj ⟨hNK hp, hR⟩ ⟨hNK hp, hL⟩⟩, hL⟩⟩
  have e1 := area_inter_add_sdiff (S := niche K (π / 2)) (T := hRight φ K)
    (isClosed_halfPlus _ _).measurableSet hfin
  have e2 := area_inter_add_sdiff (S := niche K (π / 2) \ hRight φ K) (T := hLeft φ K)
    (isClosed_halfPlus _ _).measurableSet (volume_ne_top_of_subset sdiff_subset hfin)
  rw [he3] at e2
  obtain ⟨htR, htL⟩ := separated_tail_areas hφ hK hwidth htriple hsep
  have hco := positive_core_area_le ⟨hφ0, hφ4⟩ hK hcore hc hsep hheight
  obtain ⟨-, -, hBa, hDb⟩ := inWideL_supp htriple
  obtain ⟨hXB, hW, hxR⟩ := opt_right_mem_line hcos.ne' hBa
  obtain ⟨hYD, hZ, hxL⟩ := opt_left_mem_line hcos.ne' hDb
  have c1 := segArea_add_of_mem_line hXB hW hxR
  have c2 := segArea_add_of_mem_line hxL hZ hYD
  have s1 := segArea_swap (xRight φ K) (xB φ (rightBody φ K))
  have s2 := segArea_swap (yD φ (leftBody φ K)) (xLeft φ K)
  unfold sofaArea upperQ
  linarith

/-- Near Gerver's cap, a right-angle cap has its canonical triple in the wide domain, contains its
niche, and satisfies `A(K) ≤ 𝒬(ξ_K) ≤ |G|`. The injectivity condition is not assumed, and the
radius of the neighborhood does not depend on `K`. -/
theorem nearby_cap_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        niche K (π / 2) ⊆ K ∧
        sofaArea (π / 2) K ≤ upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ area (gerverSofa P) := by
  have hφ := gm_φ_mem_Ioo hP hbox
  obtain ⟨δT, hδT, hδT1, hT⟩ := nearby_canonical_inWideL hP hbox
  obtain ⟨δS, hδS, -, hS⟩ := nearby_cutSeparated hP hbox
  obtain ⟨δH, hδH, -, hH⟩ := nearby_core_height_pos hP hbox
  obtain ⟨δN, hδN, -, hN⟩ := nearby_niche_subset_cap hP hbox
  obtain ⟨c, δA, hc, hδA, -, hA⟩ := core_arm_margin_near_reference
    (theorem8_1_1_gerver hP hbox) hφ.1 (b := π / 2 - P.φ) (by linarith [hφ.2]) (by linarith [hφ.1])
  refine ⟨min δT (min δS (min δH (min δN (min δA (1 / 20))))), by positivity,
    (min_le_left _ _).trans hδT1, fun K hK hclose => ?_⟩
  have ht := hT K hK (hclose.mono (by simp))
  have hn := hN K hK (hclose.mono (by simp))
  exact ⟨ht, hn, separated_upperQ_bound hbox.1 hK (nearby_bottomWidth hP hbox
      (hclose.mono (by simp))) ht (hA K hK (hclose.mono (by simp))) hc
      (hS K hK (hclose.mono (by simp))) (hH K (hclose.mono (by simp))) hn,
    (coercive_certificate hP hbox (canonicalWideTriple ht)).1⟩

/-- Near Gerver's cap, a right-angle cap contains its niche, has sofa area at most `|G|`, and
lies within `(2 / cos φ) √(|G| - A(K))` of Gerver's cap translated horizontally: the coercive
certificate at its canonical triple, with `A(K) ≤ 𝒬(ξ_K)`. The injectivity condition is not
assumed. -/
theorem nearby_cap_distance {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        niche K (π / 2) ⊆ K ∧ sofaArea (π / 2) K ≤ area (gerverSofa P) ∧
        EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
          K (shiftedReferenceCap P.cap K) := by
  obtain ⟨δ, hδ, hδ1, hcert⟩ := nearby_cap_certificate hP hbox
  refine ⟨δ, hδ, hδ1, fun K hK hclose => ?_⟩
  obtain ⟨ht, hn, ha, hq⟩ := hcert K hK hclose
  have hc : 0 ≤ 2 / cos P.φ :=
    div_nonneg zero_le_two (cap_angle_parameters (gm_φ_mem_Ioo hP hbox)).1.le
  exact ⟨hn, ha.trans hq, (coercive_certificate hP hbox (canonicalWideTriple ht)).2.mono
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (sub_le_sub_left ha _)) hc)⟩

end MovingSofaStability
