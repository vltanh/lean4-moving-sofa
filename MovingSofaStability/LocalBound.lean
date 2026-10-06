module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import MovingSofaStability.Basic
public import MovingSofaStability.CapEstimate
public import MovingSofaStability.LocalGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The upper bound near Gerver's cap

For every right-angle cap close to Gerver's, `A(K) ≤ 𝒬(ξ_K) ≤ |G|` without the injectivity condition, and
the cap lies within `(2 / cos φ) √(|G| - A(K))` of Gerver's cap translated horizontally
(`nearby_cap_certificate`, `nearby_cap_distance`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Analysis of nonsmooth corner paths

The corner velocity is expressed through the measurable right derivative of a
convex support. It is bounded and integrable. The right-derivative fundamental
theorem then identifies the curve's vector measure with its density, without a
C1 assumption on the cap.
-/

section CornerAnalysis

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem cornerRightVelocity_measurable {K : Set Point} (hK : IsConvexBody K) :
    Measurable (cornerRightVelocity K) := by
  have hf : Measurable (fPlus K) := by
    have he : fPlus K = fun t => supp K (t + π / 2) - opt_g K t :=
      funext fun t => inj_fPlus_eq K t
    rw [he]
    exact (hK.continuous_supp.measurable.comp (measurable_id.add_const _)).sub (opt_g_measurable hK)
  have hg : Measurable (gPlus K) := by
    have he : gPlus K = fun t => supp K t + opt_g K (t + π / 2) :=
      funext fun t => inj_gPlus_eq K t
    rw [he]
    exact hK.continuous_supp.measurable.add ((opt_g_measurable hK).comp (measurable_id.add_const _))
  exact ((hf.sub_const 1).neg.smul continuous_uvec.measurable).add
    ((hg.sub_const 1).smul continuous_vvec.measurable)

theorem cornerRightVelocity_bound {K : Set Point} (hK : IsConvexBody K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, norm2 (cornerRightVelocity K t) ≤ B := by
  obtain ⟨R, hR⟩ := hK.2.1.exists_bound_of_continuousOn continuous_norm2.continuousOn
  obtain ⟨p, hp⟩ := hK.1
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR p hp)
  have hradius : ∀ p ∈ K, norm2 p ≤ R := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm2_nonneg p)] using hR p hp
  have hg : ∀ t, |opt_g K t| ≤ R := by
    intro t
    have hb := hradius (vplus K t) (vplus_mem_edge hK t).1
    have he := abs_dot_le_norm2_mul (vplus K t) (vvec t)
    rw [norm2_vvec, mul_one] at he
    exact he.trans hb
  have hfplus : ∀ t, |fPlus K t - 1| ≤ 2 * R + 1 := by
    intro t
    rw [inj_fPlus_eq]
    change |supp K (t + π / 2) - opt_g K t - 1| ≤ 2 * R + 1
    have h1 := abs_sub (supp K (t + π / 2)) (opt_g K t)
    have h2 := abs_sub (supp K (t + π / 2) - opt_g K t) 1
    have hs := support_abs_le_radius hK hradius (t + π / 2)
    have hd := hg t
    norm_num at h2
    linarith
  have hgplus : ∀ t, |gPlus K t - 1| ≤ 2 * R + 1 := by
    intro t
    rw [inj_gPlus_eq]
    change |supp K t + opt_g K (t + π / 2) - 1| ≤ 2 * R + 1
    have h1 := abs_add_le (supp K t) (opt_g K (t + π / 2))
    have h2 := abs_sub (supp K t + opt_g K (t + π / 2)) 1
    have hs := support_abs_le_radius hK hradius t
    have hd := hg (t + π / 2)
    norm_num at h2
    linarith
  refine ⟨4 * R + 2, by linarith, ?_⟩
  intro t
  have hh := norm2_add_le (-(fPlus K t - 1) • uvec t) ((gPlus K t - 1) • vvec t)
  rw [norm2_smul, norm2_smul, norm2_uvec, norm2_vvec, mul_one, mul_one, abs_neg] at hh
  exact hh.trans (by linarith [hfplus t, hgplus t])

theorem cornerRightVelocity_intervalIntegrable {K : Set Point} (hK : IsConvexBody K) (a b : ℝ) :
    IntervalIntegrable (cornerRightVelocity K) volume a b := by
  obtain ⟨B, hB, hbound⟩ := cornerRightVelocity_bound hK
  have hm := cornerRightVelocity_measurable hK
  have hi1 := opt_intervalIntegrable_of_bound hm.fst
    (fun t => (abs_fst_le_norm2 _).trans (hbound t)) a b
  have hi2 := opt_intervalIntegrable_of_bound hm.snd
    (fun t => (abs_snd_le_norm2 _).trans (hbound t)) a b
  exact ⟨hi1.1.prodMk hi2.1, hi1.2.prodMk hi2.2⟩

/-- A corner path is the primitive of its right velocity on every compact interval. -/
theorem corner_primitive {K : Set Point} (hK : IsCap K (π / 2))
    {a t : ℝ} (hat : a ≤ t) :
    innerCorner K t = innerCorner K a + ∫ s in a..t, cornerRightVelocity K s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hat
    (opt_innerCorner_continuous hK.2.1).continuousOn
    (fun s hs => corner_hasRightDeriv hK s) (cornerRightVelocity_intervalIntegrable hK.2.1 a t)
  rw [hi]
  abel

/-- The vector measure of the nonsmooth corner path has its bounded right-velocity density. -/
theorem corner_lsMeasure_density {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    lsMeasure (innerCorner K) a b =
      (volume.restrict (Icc a b)).withDensityᵥ (cornerRightVelocity K) := by
  have hi : IntegrableOn (cornerRightVelocity K) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      (cornerRightVelocity_intervalIntegrable hK.2.1 a b)
  have hx : ∀ t ∈ Icc a b, innerCorner K t = innerCorner K a +
      ∫ s in a..t, cornerRightVelocity K s := fun t ht => corner_primitive hK ht.1
  obtain ⟨B, hB, hbound⟩ := cornerRightVelocity_bound hK.2.1
  have hb : ∀ t ∈ Icc a b, ‖cornerRightVelocity K t‖ ≤ B.toNNReal := by
    intro t ht
    exact ((product_norm_le_norm2 _).trans (hbound t)).trans (Real.le_coe_toNNReal B)
  obtain ⟨hbv, hcont⟩ := cvx_bv_of_primitive hab hi hb hx
  exact cvx_lsMeasure_eq_withDensityᵥ hab hi hx hbv hcont

/-- The original curve-area functional equals the right-velocity cross integral. -/
theorem corner_curveArea_integral {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    curveArea (innerCorner K) a b =
      (1 / 2) * ∫ t in a..b, cross (innerCorner K t) (cornerRightVelocity K t) := by
  have hi : IntegrableOn (cornerRightVelocity K) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      (cornerRightVelocity_intervalIntegrable hK.2.1 a b)
  obtain ⟨B, hB, hbound⟩ := cornerRightVelocity_bound hK.2.1
  have hb : ∀ᵐ t ∂volume.restrict (Icc a b), ‖cornerRightVelocity K t‖ ≤ B.toNNReal :=
    Eventually.of_forall fun t =>
      ((product_norm_le_norm2 _).trans (hbound t)).trans (Real.le_coe_toNNReal B)
  have hx : IntegrableOn (innerCorner K) (Icc a b) volume :=
    (opt_innerCorner_continuous hK.2.1).continuousOn.integrableOn_compact isCompact_Icc
  unfold curveArea curveBilin
  rw [corner_lsMeasure_density hK hab,
    cvx_withDensityᵥ_restrict hi measurableSet_Icc,
    Measure.restrict_restrict_of_subset subset_rfl,
    cvx_integral_withDensityᵥ hi hb crossCLM hx,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp only [crossCLM_apply]

/-- A uniform right-velocity bound gives a chord bound for each coordinate. -/
theorem corner_coordinate_chord_bound {K : Set Point} (hK : IsCap K (π / 2))
    {B : ℝ} (hB : ∀ t, norm2 (cornerRightVelocity K t) ≤ B) (u v : ℝ) :
    |(innerCorner K u).2 - (innerCorner K v).2| ≤ B * |u - v| := by
  have ordered : ∀ u v, u ≤ v →
      |(innerCorner K u).2 - (innerCorner K v).2| ≤ B * (v - u) := by
    intro u v huv
    have upper := right_derivative_increment_le huv
      (opt_innerCorner_continuous hK.2.1).snd.continuousOn
      (fun t ht => (corner_hasRightDeriv hK t).snd)
      (fun t ht => (le_abs_self _).trans ((abs_snd_le_norm2 _).trans (hB t)))
    have lower := right_derivative_increment_ge huv
      (opt_innerCorner_continuous hK.2.1).snd.continuousOn
      (fun t ht => (corner_hasRightDeriv hK t).snd)
      (B := -B) (fun t ht => by
        have hh := (abs_snd_le_norm2 _).trans (hB t)
        exact (abs_le.mp hh).1)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    have h := ordered u v huv
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_sub_comm]
    exact ordered v u hvu

end MovingSofaStability

end CornerAnalysis

/-!
## The nonsmooth core as a Lipschitz graph

A uniform horizontal-decrease estimate and a bounded right velocity imply a
finite chord slope. The graph is extended continuously outside its horizontal
interval by clamping, for use in an elementary right-derivative
change-of-variables argument.
-/

section CoreGraph

open Real Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Continuous extension of a Lipschitz function on an interval by constant end values. -/
theorem continuous_clamped_roof {a b L : ℝ} {γ : ℝ → ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |γ x - γ y| ≤ L * |x - y|) :
    Continuous (fun x => γ (max a (min x b))) := by
  have hlip : LipschitzOnWith L.toNNReal γ (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip x hx y hy
  exact hlip.continuousOn.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun x => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)

/-- Uniform core-arm margins give a finite slope bound for every core chord. -/
theorem core_verticalSlopeBound {K : Set Point} (hK : IsCap K (π / 2))
    {a b c : ℝ} (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2) :
    ∃ L : ℝ, 0 ≤ L ∧ VerticalSlopeBound (innerCorner K '' Icc a b) L := by
  obtain ⟨B, hB, hvel⟩ := cornerRightVelocity_bound hK.2.1
  let L := B / c
  have hL : 0 ≤ L := div_nonneg hB hc.le
  have hLc : L * c = B := div_mul_cancel₀ _ hc.ne'
  have ordered : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      |(innerCorner K u).2 - (innerCorner K v).2| ≤
        L * |(innerCorner K u).1 - (innerCorner K v).1| := by
    intro u hu v hv huv
    have hX := hmargin.horizontal_decrease hK hc.le ha hb hu hv huv
    have hY := corner_coordinate_chord_bound hK hvel u v
    rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hY
    have hXorder : (innerCorner K v).1 ≤ (innerCorner K u).1 := by
      have hnon : -c * (v - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sub_nonneg.mpr huv)
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hXorder)]
    have hbound : c * (v - u) ≤ (innerCorner K u).1 - (innerCorner K v).1 := by linarith
    have hm := mul_le_mul_of_nonneg_left hbound hL
    rw [← mul_assoc, hLc] at hm
    nlinarith
  refine ⟨L, hL, ?_⟩
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
  have hanti := hmargin.strictAnti_core hK hc ha hb
  have hcX : ContinuousOn (fun t => (innerCorner K t).1) (Icc a b) :=
    (opt_innerCorner_continuous hK.2.1).fst.continuousOn
  have horder : (innerCorner K b).1 < (innerCorner K a).1 :=
    hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  obtain ⟨L, hL, hSlope⟩ := core_verticalSlopeBound hK hmargin hc ha hb
  have hrange : ∀ p ∈ innerCorner K '' Icc a b,
      p.1 ∈ Icc (innerCorner K b).1 (innerCorner K a).1 := by
    rintro p ⟨t, ht, rfl⟩
    exact ⟨hanti.antitoneOn ht ⟨hab.le, le_rfl⟩ ht.2,
      hanti.antitoneOn ⟨le_rfl, hab.le⟩ ht ht.1⟩
  have hcover : ∀ y ∈ Icc (innerCorner K b).1 (innerCorner K a).1,
      ∃ t ∈ Icc a b, (innerCorner K t).1 = y := by
    intro y hy
    exact intermediate_value_Icc' hab.le hcX hy
  obtain ⟨γ, hgraph, hLip⟩ := exists_roof_function hrange (by
    intro y hy
    obtain ⟨t, ht, he⟩ := hcover y hy
    exact ⟨innerCorner K t, mem_image_of_mem _ ht, he⟩) hSlope
  let F := fun y => γ (max (innerCorner K b).1 (min y (innerCorner K a).1))
  have hF : Continuous F := continuous_clamped_roof horder.le hL hLip
  refine ⟨F, hF, ?_, hcover⟩
  intro t ht
  have hp := hrange _ (mem_image_of_mem _ ht)
  have hy := ((hgraph _).1 (mem_image_of_mem _ ht)).2
  dsimp [F]
  rw [min_eq_left hp.2, max_eq_right hp.1]
  exact hy.symm

end MovingSofaStability

end CoreGraph

/-!
## Change of variables and signed area for the nonsmooth core

A continuous primitive of the roof function is composed with the horizontal
coordinate. The right-derivative fundamental theorem then gives change of
variables without assuming a C1 competing cap.
-/

section CoreIntegral

open Real Set MeasureTheory Filter Topology
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- One-dimensional substitution using right derivatives and a continuous integrand. -/
theorem integral_comp_mul_rightDerivative {X X' F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hX : ContinuousOn X (Icc a b)) (hF : Continuous F)
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt X (X' t) (Ioi t) t)
    (hi : IntervalIntegrable (fun t => F (X t) * X' t) volume a b) :
    (∫ t in a..b, F (X t) * X' t) = ∫ x in X a..X b, F x := by
  let P : ℝ → ℝ := fun x => ∫ y in X a..x, F y
  have hP : ∀ x, HasDerivAt P (F x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun x => (hP x).continuousAt
  have hcomp : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun t => P (X t)) (F (X t) * X' t) (Ioi t) t := by
    intro t ht
    exact (hP (X t)).comp_hasDerivWithinAt t (hd t ht)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hPc.comp_continuousOn hX) hcomp hi
  simpa only [P, Function.comp_apply, intervalIntegral.integral_same, sub_zero] using h

/-- The first coordinate of an interval-integrable plane curve is interval integrable. -/
private theorem intervalIntegrable_fst {f : ℝ → Point} {a b : ℝ}
    (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => (f t).1) volume a b :=
  ⟨h.1.fst, h.2.fst⟩

/-- The second coordinate of an interval-integrable plane curve is interval integrable. -/
private theorem intervalIntegrable_snd {f : ℝ → Point} {a b : ℝ}
    (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => (f t).2) volume a b :=
  ⟨h.1.snd, h.2.snd⟩

/-- The horizontal coordinate of the corner has the first velocity coordinate as right
derivative. -/
private theorem corner_fst_hasRightDeriv {K : Set Point} (hK : IsCap K (π / 2)) (t : ℝ) :
    HasDerivWithinAt (fun s => (innerCorner K s).1) (cornerRightVelocity K t).1 (Ioi t) t :=
  (corner_hasRightDeriv hK t).fst

/-- The vertical coordinate of the corner has the second velocity coordinate as right
derivative. -/
private theorem corner_snd_hasRightDeriv {K : Set Point} (hK : IsCap K (π / 2)) (t : ℝ) :
    HasDerivWithinAt (fun s => (innerCorner K s).2) (cornerRightVelocity K t).2 (Ioi t) t :=
  (corner_hasRightDeriv hK t).snd

/-- Multiplying a coordinate by a coordinate of the right velocity is integrable. -/
theorem corner_coordinate_velocity_integrable {K : Set Point}
    (hK : IsCap K (π / 2)) (a b : ℝ) :
    IntervalIntegrable (fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2) volume a b ∧
    IntervalIntegrable (fun t => (innerCorner K t).2 * (cornerRightVelocity K t).1) volume a b := by
  have hv := cornerRightVelocity_intervalIntegrable hK.2.1 a b
  have hc := opt_innerCorner_continuous hK.2.1
  exact ⟨(intervalIntegrable_snd hv).continuousOn_mul hc.fst.continuousOn,
    (intervalIntegrable_fst hv).continuousOn_mul hc.snd.continuousOn⟩

/-- Integration by parts using the right derivative of the coordinate product. -/
theorem corner_coordinate_product_integral {K : Set Point}
    (hK : IsCap K (π / 2)) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (innerCorner K t).1 * (cornerRightVelocity K t).2) +
      (∫ t in a..b, (innerCorner K t).2 * (cornerRightVelocity K t).1) =
      (innerCorner K b).1 * (innerCorner K b).2 -
        (innerCorner K a).1 * (innerCorner K a).2 := by
  obtain ⟨hi1, hi2⟩ := corner_coordinate_velocity_integrable hK a b
  have hc := opt_innerCorner_continuous hK.2.1
  have hd : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun t => (innerCorner K t).1 * (innerCorner K t).2)
        ((innerCorner K t).1 * (cornerRightVelocity K t).2 +
          (innerCorner K t).2 * (cornerRightVelocity K t).1) (Ioi t) t := by
    intro t _
    convert (corner_fst_hasRightDeriv hK t).mul (corner_snd_hasRightDeriv hK t) using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hc.fst.mul hc.snd).continuousOn hd (hi1.add hi2)
  rwa [intervalIntegral.integral_add hi1 hi2] at h

/-- The region under a strictly decreasing nonsmooth core is an ordinary region
between continuous graphs. The change of variables uses the previous lemma. -/
theorem volume_under_core_graph {K : Set Point} (hK : IsCap K (π / 2))
    {a b c H : ℝ} (hab : a < b) (hmargin : CoreArmMargin K a b c) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : b ≤ π / 2)
    (hH : ∀ t ∈ Icc a b, 0 < (innerCorner K t).2 + H) :
    volume ((fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
      {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2 + H}) =
      ENNReal.ofReal (∫ t in a..b, -(cornerRightVelocity K t).1 * ((innerCorner K t).2 + H)) := by
  obtain ⟨F, hF, hgraph, hcover⟩ := exists_core_graph hK hab hmargin hc ha hb
  have hanti := hmargin.strictAnti_core hK hc ha hb
  have horder : (innerCorner K b).1 < (innerCorner K a).1 :=
    hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hset : ((fun q : ℝ × ℝ => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
      {q : ℝ × ℝ | q.1 ∈ Ioo a b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2 + H}) =
      regionBetween (fun _ => -H) F (Ioo (innerCorner K b).1 (innerCorner K a).1) := by
    ext p
    constructor
    · rintro ⟨⟨t, s⟩, ⟨ht, hs0, hsH⟩, rfl⟩
      have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      refine ⟨⟨hanti ht' ⟨hab.le, le_rfl⟩ ht.2,
        hanti ⟨le_rfl, hab.le⟩ ht' ht.1⟩, ?_, ?_⟩
      · dsimp; linarith
      · rw [hgraph t ht']; dsimp; linarith
    · rintro ⟨hp, hp0, hpF⟩
      obtain ⟨t, ht, htx⟩ := hcover p.1 ⟨hp.1.le, hp.2.le⟩
      have hta : a < t := lt_of_le_of_ne ht.1 (by
        intro he; subst t; rw [htx] at hp; exact (lt_irrefl _ hp.2))
      have htb : t < b := lt_of_le_of_ne ht.2 (by
        intro he; subst t; rw [htx] at hp; exact (lt_irrefl _ hp.1))
      have hy : F p.1 = (innerCorner K t).2 := by rw [← htx, hgraph t ht]
      refine ⟨(t, (innerCorner K t).2 - p.2), ⟨⟨hta, htb⟩, ?_, ?_⟩, ?_⟩
      · dsimp; linarith
      · dsimp; linarith
      · ext <;> dsimp <;> linarith
  have hheight : ∀ x ∈ Ioo (innerCorner K b).1 (innerCorner K a).1, -H ≤ F x := by
    intro x hx
    obtain ⟨t, ht, he⟩ := hcover x ⟨hx.1.le, hx.2.le⟩
    rw [← he, hgraph t ht]
    linarith [hH t ht]
  rw [hset, Measure.volume_eq_prod, volume_regionBetween_eq_integral
    (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo hheight,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le horder.le]
  congr 1
  have hv := intervalIntegrable_fst (cornerRightVelocity_intervalIntegrable hK.2.1 a b)
  have hcY : ContinuousOn (fun t => (innerCorner K t).2 + H) (uIcc a b) :=
    ((opt_innerCorner_continuous hK.2.1).snd.add continuous_const).continuousOn
  have hi : IntervalIntegrable
      (fun t => (F (innerCorner K t).1 + H) * (cornerRightVelocity K t).1) volume a b := by
    apply (hv.continuousOn_mul hcY).congr
    intro t ht
    rw [uIoc_of_le hab.le] at ht
    simp only [hgraph t (Ioc_subset_Icc_self ht)]
  have he := integral_comp_mul_rightDerivative hab.le
    (opt_innerCorner_continuous hK.2.1).fst.continuousOn (hF.add continuous_const)
    (fun t _ => corner_fst_hasRightDeriv hK t) hi
  rw [intervalIntegral.integral_symm (innerCorner K b).1 (innerCorner K a).1] at he
  calc
    (∫ x in (innerCorner K b).1..(innerCorner K a).1, F x - -H)
        = -(∫ t in a..b, (F (innerCorner K t).1 + H) * (cornerRightVelocity K t).1) := by
          simpa only [sub_neg_eq_add, Pi.add_apply] using (neg_eq_iff_eq_neg.mpr he).symm
    _ = ∫ t in a..b, -(cornerRightVelocity K t).1 * ((innerCorner K t).2 + H) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab.le] at ht
      simp only [hgraph t ht]
      ring

end MovingSofaStability

end CoreIntegral

/-!
## Stable separation from the two niche cuts

Close to a cut, a uniform right-velocity margin is used. Away from it, a strict
compact reference margin is used. No derivative control near the ends 0 and pi/2
is assumed for the competing cap.
-/

section CutSeparation

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The two inequalities used in the three-region niche decomposition. -/
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

/-- Separation on the right includes times arbitrarily close to pi/2. -/
theorem nearby_right_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ioc φ (π / 2), dot (innerCorner K t) (uvec φ) < supp K φ - 1 := by
  have hpi := pi_pos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (φ + π / 2) / 2 := ⟨_, rfl⟩
  have hφm : φ < m := by rw [hm]; linarith [hφ.2]
  have hmv : m < π / 2 := by rw [hm]; linarith [hφ.2]
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ :=
    core_arm_margin_near_reference hK₀ hφ.1 hφm.le hmv
  have hgapcont : Continuous (fun t => supp K₀ φ - 1 - dot (innerCorner K₀ t) (uvec φ)) :=
    continuous_const.sub ((continuous_dot (uvec φ)).comp (opt_innerCorner_continuous hK₀.1.2.1))
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' hgapcont.continuousOn
    (s := Icc m (π / 2)) (fun t ht => sub_pos.mpr
      (opt_innerCorner_lt_right hφ hK₀ ⟨hφm.trans_le ht.1, ht.2⟩))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  have hδA' : min δA (g / 4) ≤ δA := min_le_left _ _
  have hδg : min δA (g / 4) ≤ g / 4 := min_le_right _ _
  by_cases htm : t ≤ m
  · have hcore := hA K hK (hclose.mono hδA')
    have hinc := right_derivative_increment_le (f := fun s => dot (innerCorner K s) (uvec φ))
      ht.1.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn (uvec φ))
      (fun s _ => hasRightDeriv_dot_uvec (d := φ) (corner_hasRightDeriv hK s))
      (B := -c) (fun s hs => hcore.right_cut_velocity hK hc.le
        ⟨hs.1.le, hs.2.le.trans htm⟩
        ⟨by linarith [hs.1], by linarith [hs.2, ht.2, hφ.1]⟩)
    rw [(cn_innerCorner_dot K φ).1] at hinc
    have hneg : -c * (t - φ) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (sub_pos.mpr ht.1)
    linarith
  · have hr := hgap t ⟨(not_le.mp htm).le, ht.2⟩
    have he := innerCorner_projection_error hclose ⟨(hφ.1.trans ht.1).le, ht.2⟩ φ
    have hs := hclose φ ⟨hφ.1.le, by linarith [hφ.2]⟩
    have hu := (abs_le.mp he).2
    have hl := (abs_le.mp hs).1
    linarith

/-- The left separation is obtained by the same local/compact split, without
assuming that all left arm lengths of the competing cap exceed one. -/
theorem nearby_left_cut_separation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₀ : Set Point} (hK₀ : IsKi K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K K₀ →
        ∀ t ∈ Ico 0 (π / 2 - φ),
          dot (innerCorner K t) (vvec (π / 2 - φ)) < supp K (π / 2 - φ + π / 2) - 1 := by
  have hpi := pi_pos
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = π / 2 - φ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = b / 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; linarith [hφ.2]
  have hmv : 0 < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  have hbv : b < π / 2 := by rw [hb]; linarith [hφ.1]
  rw [← hb]
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ :=
    core_arm_margin_near_reference hK₀ hmv hmb.le hbv
  have hgapcont :
      Continuous (fun t => supp K₀ (b + π / 2) - 1 - dot (innerCorner K₀ t) (vvec b)) :=
    continuous_const.sub ((continuous_dot (vvec b)).comp (opt_innerCorner_continuous hK₀.1.2.1))
  obtain ⟨g, hg, hgap⟩ := isCompact_Icc.exists_forall_le' hgapcont.continuousOn
    (s := Icc (0 : ℝ) m) (fun t ht => sub_pos.mpr (by
      have h := opt_innerCorner_lt_left hφ hK₀ (t := t) ⟨ht.1, hb ▸ ht.2.trans_lt hmb⟩
      rwa [← hb] at h))
  refine ⟨min δA (g / 4), lt_min hδA (by linarith), (min_le_left _ _).trans hδA1, ?_⟩
  intro K hK hclose t ht
  have hδA' : min δA (g / 4) ≤ δA := min_le_left _ _
  have hδg : min δA (g / 4) ≤ g / 4 := min_le_right _ _
  by_cases hmt : m ≤ t
  · have hcore := hA K hK (hclose.mono hδA')
    have hinc := right_derivative_increment_ge (f := fun s => dot (innerCorner K s) (vvec b))
      ht.2.le (continuousOn_dot (opt_innerCorner_continuous hK.2.1).continuousOn (vvec b))
      (fun s _ => by
        simpa only [uvec_add_pi_div_two] using
          hasRightDeriv_dot_uvec (d := b + π / 2) (corner_hasRightDeriv hK s))
      (B := c) (fun s hs => by
        simpa only [uvec_add_pi_div_two] using hcore.left_cut_velocity hK hc.le
          ⟨hmt.trans hs.1.le, hs.2.le⟩
          ⟨by linarith [hs.2], by linarith [hs.1, ht.1]⟩)
    rw [opt_innerCorner_dot_v] at hinc
    have hpos : 0 < c * (b - t) := mul_pos hc (sub_pos.mpr ht.2)
    linarith
  · have hr := hgap t ⟨ht.1, (not_le.mp hmt).le⟩
    have he := innerCorner_projection_error hclose ⟨ht.1, ht.2.le.trans hbv.le⟩ (b + π / 2)
    rw [uvec_add_pi_div_two] at he
    have hs := hclose (b + π / 2) ⟨by linarith, by linarith [hφ.1]⟩
    have hu := (abs_le.mp he).2
    have hl := (abs_le.mp hs).1
    linarith

/-- Both cuts are simultaneously separated in one fixed neighborhood. -/
theorem nearby_cutSeparated {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap → CutSeparated P.φ K := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hK₀ := theorem8_1_1_gerver hP hbox
  obtain ⟨δR, hR, hR1, hright⟩ := nearby_right_cut_separation hφ hK₀
  obtain ⟨δL, hL, hL1, hleft⟩ := nearby_left_cut_separation hφ hK₀
  exact ⟨min δR δL, lt_min hR hL, (min_le_left _ _).trans hR1,
    fun K hK hclose => ⟨hright K hK (hclose.mono (min_le_left _ _)),
      hleft K hK (hclose.mono (min_le_right _ _))⟩⟩

end MovingSofaStability

end CutSeparation

/-!
## Wedges and tail areas under the weaker cut-separation hypothesis

These are the geometric parts of source Lemmas 8.1.6 and 8.2.2. Their actual
hypotheses are separated cut corners, canonical endpoint contacts, and finite
niche area; no global injectivity is required.
-/

section SeparatedWedges

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

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
    constructor
    · rintro ⟨hp, h1, -⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, h1, ?_⟩
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
  refine ⟨h2, ?_⟩
  ext p
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
    constructor
    · rintro ⟨hp, -, h1⟩; exact ⟨hp, h1⟩
    · rintro ⟨hp, h1⟩
      refine ⟨hp, ?_, h1⟩
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
  refine ⟨h2, ?_⟩
  ext p
  have he := Set.ext_iff.mp h2 p
  simp only [wedge, fan, mem_inter_iff, mem_sdiff] at he ⊢
  tauto

/-- The tail-area inequality with the precise weaker hypotheses needed locally. -/
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
  have hφ' : φ ∈ Ioo 0 (π / 4) := ⟨hφ0, hφ4⟩
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp htriple
  have hBcb := htriple.2.1
  have hDcb := htriple.2.2.1
  obtain ⟨hW, hZ⟩ := cut_feet_mem_of_width hφ hK hwidth
  have hfin : ∀ A ⊆ niche K (π / 2), volume A ≠ ⊤ := fun A hA =>
    ne_top_of_le_ne_top (nef_niche_isBounded hK).measure_lt_top.ne (measure_mono hA)
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
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc φ (π / 2), p ∉ halfB K s := by
        by_contra hcon
        push Not at hcon
        exact hpB ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hsφ : φ < s := lt_of_le_of_ne hs.1 (by rintro rfl; exact hps hpR)
      have hsv : s < π / 2 := lt_of_le_of_ne hs.2 (by
        rintro rfl
        apply hps
        simp only [halfB, halfPlus, mem_ofPred_eq, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hpw : p ∈ wedge K (π / 2) s := by
        have he : p ∈ (hRight φ K ∩ halfPlus (π / 2) 0) \ halfB K s := by
          refine ⟨⟨hpR, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (separated_right_wedge hφ' hsep ⟨hsφ, hsv.le⟩).2] at he
        exact he.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨by linarith, hsv⟩, hpw.2⟩⟩, hpR⟩
    have he := opt_tail_area_le hBcb (by linarith) (by linarith) inter_subset_left hK.2.1.2.2
      (by rw [hvint]; exact hW.1.1) (hfin _ inter_subset_left) hsub
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
      obtain ⟨s, hs, hps⟩ : ∃ s ∈ Icc 0 (π / 2 - φ), p ∉ halfD K s := by
        by_contra hcon
        push Not at hcon
        exact hpD ⟨hpK, mem_iInter₂.mpr hcon⟩
      have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by
        rintro rfl
        apply hps
        simp only [halfD, halfPlus, mem_ofPred_eq, zero_add, hK.2.2.2.1, dot_uvec_pi_div_two]
        linarith)
      have hsψ : s < π / 2 - φ := lt_of_le_of_ne hs.2 (by rintro rfl; exact hps hpL)
      have hpw : p ∈ wedge K (π / 2) s := by
        have he : p ∈ (hLeft φ K ∩ halfPlus (π / 2) 0) \ halfD K s := by
          refine ⟨⟨hpL, ?_⟩, hps⟩
          simp only [halfPlus, mem_ofPred_eq, dot_uvec_pi_div_two]; linarith
        rw [← (separated_left_wedge hφ' hsep ⟨hs0.le, hsψ⟩).2] at he
        exact he.2
      exact ⟨⟨hpw.1, mem_iUnion₂.mpr ⟨s, ⟨hs0, by linarith⟩, hpw.2⟩⟩, hpL⟩
    have he := opt_tail_area_le hDcb (by linarith) (by linarith) inter_subset_left hK.2.1.2.2
      (by rw [hvint]; exact hZ.1.1) (hfin _ inter_subset_left) hsub
    rwa [hvint, segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3)
      (by rw [opt_zLeft_eq]), zero_add] at he

end MovingSofaStability

end SeparatedWedges

/-!
## Positive local core regions

Gerver's core lies strictly above the floor. This persists in a fixed support
neighborhood and lets the local upper bound use three positive-area regions,
rather than subtract an auxiliary trapezoid.
-/

section CoreRegionGeometry

open Real Set
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- Core height stays uniformly positive in a neighborhood of Gerver's cap. -/
theorem nearby_core_height_pos {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      UpperSupportClose δ K P.cap → ∀ t ∈ Icc P.φ (π / 2 - P.φ),
        0 < (innerCorner K t).2 := by
  have henv := gn_envHyp hP (romik_bounds hP hbox)
  have hφ := gm_φ_mem_Ioo hP hbox
  have hc : Continuous (fun t => (innerCorner P.cap t).2) :=
    (opt_innerCorner_continuous (gm_isConvexBody_cap hP hbox)).snd
  have hp : ∀ t ∈ Icc P.φ (π / 2 - P.φ), 0 < (innerCorner P.cap t).2 := by
    intro t ht
    have htv : t ∈ Icc (0 : ℝ) (π / 2) :=
      ⟨hφ.1.le.trans ht.1, by linarith [ht.2, hφ.1]⟩
    rw [((theorem8_4_1_monotone hP hbox).2 t htv).2.2]
    exact henv.x_pos t ht
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le' hc.continuousOn hp
  let δ := min 1 (m / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδm : δ ≤ m / 4 := min_le_right _ _
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro K hclose t ht
  have htv : t ∈ Icc (0 : ℝ) (π / 2) :=
    ⟨hφ.1.le.trans ht.1, by linarith [ht.2, hφ.1]⟩
  have hd := (abs_snd_le_norm2 (innerCorner K t - innerCorner P.cap t)).trans
    (innerCorner_support_error hclose htv)
  have hlo := (abs_le.mp hd).1
  have href := hmin t ht
  dsimp only [Prod.snd_sub] at hlo
  linarith

/-- Every point strictly below an interior core point belongs to its forbidden
quadrant and lies outside both cuts. -/
theorem separated_core_below {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hsep : CutSeparated φ K) {t s : ℝ}
    (ht : t ∈ Ioo φ (π / 2 - φ)) (hs : 0 < s) :
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hRight φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∉ hLeft φ K ∧
    ((innerCorner K t).1, (innerCorner K t).2 - s) ∈ qMinus K t := by
  have hpi := pi_pos
  have ht' : t ∈ Ioo 0 (π / 2) :=
    ⟨by linarith [ht.1, hφ.1], by linarith [ht.2, hφ.1]⟩
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

/-- Integration by parts expressed only through the right velocity. -/
theorem core_curveArea_rightVelocity {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) :
    curveArea (innerCorner K) a b =
      ((innerCorner K b).1 * (innerCorner K b).2 - (innerCorner K a).1 * (innerCorner K a).2) / 2 +
      ∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2 := by
  obtain ⟨hi1, hi2⟩ := corner_coordinate_velocity_integrable hK a b
  have hprod := corner_coordinate_product_integral hK hab
  rw [corner_curveArea_integral hK hab]
  have hcross : (fun t => cross (innerCorner K t) (cornerRightVelocity K t)) =
      fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2 -
        (innerCorner K t).2 * (cornerRightVelocity K t).1 := rfl
  have hneg : (∫ t in a..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2) =
      -(∫ t in a..b, (innerCorner K t).2 * (cornerRightVelocity K t).1) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hcross, intervalIntegral.integral_sub hi1 hi2, hneg]
  linarith

end MovingSofaStability

end CoreRegionGeometry

/-!
## The local core-area inequality

The core is a continuous Lipschitz graph with a strictly positive height. Its
under-graph region and two endpoint triangles are disjoint subsets of the middle
niche. Their areas give the same signed curve bound as Baek's smooth proof.
-/

section CoreAreaBound

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Core-area lower bound under the exact geometric hypotheses used locally. -/
theorem positive_core_area_le {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set Point} (hK : IsCap K (π / 2))
    (hcore : CoreArmMargin K φ (π / 2 - φ) c) (hc : 0 < c)
    (hsep : CutSeparated φ K)
    (hheight : ∀ t ∈ Icc φ (π / 2 - φ), 0 < (innerCorner K t).2) :
    segArea (wRight φ K) (xRight φ K) + curveArea (innerCorner K) φ (π / 2 - φ) +
      segArea (xLeft φ K) (zLeft φ K) ≤
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hab : φ < π / 2 - φ := by linarith
  have hbv : π / 2 - φ < π / 2 := by linarith
  set b := π / 2 - φ with hb
  set τ := sin φ / cos φ with hτ_def
  set w := (supp K φ - 1) / cos φ with hw_def
  set z := (1 - supp K (π - φ)) / cos φ with hz_def
  set XR := (innerCorner K φ).1
  set YR := (innerCorner K φ).2
  set XL := (innerCorner K b).1
  set YL := (innerCorner K b).2
  have hτ : 0 < τ := div_pos hsin hcos
  have hYR : 0 < YR := hheight φ ⟨le_rfl, hab.le⟩
  have hYL : 0 < YL := hheight b ⟨hab.le, le_rfl⟩
  have hanti := hcore.strictAnti_core hK hc hφ0.le hbv.le
  have hX : XL < XR := hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hw : w = XR + YR * τ := by
    have he := (cn_innerCorner_dot K φ).1
    simp only [dot, uvec] at he
    rw [hw_def, hτ_def, div_eq_iff hcos.ne', add_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  have hz : z = XL - YL * τ := by
    have he := opt_innerCorner_dot_v K b
    have hsb : sin b = cos φ := by rw [hb, sin_pi_div_two_sub]
    have hcb : cos b = sin φ := by rw [hb, cos_pi_div_two_sub]
    rw [show b + π / 2 = π - φ by rw [hb]; ring] at he
    simp only [dot, vvec, hsb, hcb] at he
    rw [hz_def, hτ_def, div_eq_iff hcos.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hcos.ne']
    linarith
  let C : Set Point := (fun q : Point => ((innerCorner K q.1).1, (innerCorner K q.1).2 - q.2)) ''
    {q : Point | q.1 ∈ Ioo φ b ∧ 0 < q.2 ∧ q.2 < (innerCorner K q.1).2}
  let R : Set Point := {p | 0 < p.2 ∧ p.2 < YR ∧ XR + 0 * p.2 < p.1 ∧ p.1 < w + -τ * p.2}
  let L : Set Point := {p | 0 < p.2 ∧ p.2 < YL ∧ z + τ * p.2 < p.1 ∧ p.1 < XL + 0 * p.2}
  let I : ℝ := ∫ t in φ..b, -(cornerRightVelocity K t).1 * (innerCorner K t).2
  have hI : 0 ≤ I := by
    dsimp only [I]
    rw [intervalIntegral.integral_of_le hab.le]
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Icc φ b := ⟨ht.1.le, ht.2⟩
    have hv := hcore.velocity_fst_le hK hc.le ht'
      ⟨hφ0.le.trans ht.1.le, ht.2.trans hbv.le⟩
    exact mul_nonneg (by linarith) (hheight t ht').le
  have vC : volume C = ENNReal.ofReal I := by
    simpa only [add_zero] using volume_under_core_graph hK hab hcore hc hφ0.le hbv.le
      (H := 0) (by simpa only [add_zero] using hheight)
  have vR : volume R = ENNReal.ofReal (τ * YR ^ 2 / 2) := by
    have hn : ∀ y ∈ Ioo (0 : ℝ) YR, XR + 0 * y ≤ w + -τ * y := by
      intro y hy
      rw [hw]
      nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)]
    rw [opt_volume_hregion hYR.le hn, hw]
    congr 1
    ring
  have vL : volume L = ENNReal.ofReal (τ * YL ^ 2 / 2) := by
    have hn : ∀ y ∈ Ioo (0 : ℝ) YL, z + τ * y ≤ XL + 0 * y := by
      intro y hy
      rw [hz]
      nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hy.2.le)]
    rw [opt_volume_hregion hYL.le hn, hz]
    congr 1
    ring
  have hCfst : ∀ p ∈ C, XL < p.1 ∧ p.1 < XR := by
    rintro p ⟨⟨t, s⟩, ⟨ht, -, -⟩, rfl⟩
    exact ⟨hanti ⟨ht.1.le, ht.2.le⟩ ⟨hab.le, le_rfl⟩ ht.2,
      hanti ⟨le_rfl, hab.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1⟩
  have hdisjR : Disjoint C R := Set.disjoint_left.mpr fun p hp hq => by
    have hx := hCfst p hp
    have hr := hq.2.2.1
    linarith
  have hdisjL : Disjoint (C ∪ R) L := Set.disjoint_left.mpr fun p hp hq => by
    have hl := hq.2.2.2
    rcases hp with hp | hp
    · have hx := hCfst p hp; linarith
    · have hr := hp.2.2.1; linarith
  have hopen : ∀ a b A B D E : ℝ,
      IsOpen {p : Point | a < p.2 ∧ p.2 < b ∧ A + B * p.2 < p.1 ∧ p.1 < D + E * p.2} := by
    intro a b A B D E
    exact (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_fst).inter (isOpen_lt continuous_fst (by fun_prop))))
  have vUnion : volume (C ∪ R ∪ L) = volume C + volume R + volume L := by
    rw [measure_union hdisjL (hopen 0 YL z τ XL 0).measurableSet,
      measure_union hdisjR (hopen 0 YR XR 0 w (-τ)).measurableSet]
  have hsub : C ∪ R ∪ L ⊆ (niche K (π / 2) \ hRight φ K) \ hLeft φ K := by
    intro p hp
    have key : 0 ≤ p.2 ∧ p ∉ hRight φ K ∧ p ∉ hLeft φ K ∧
        ∃ t ∈ Ioo (0 : ℝ) (π / 2), p ∈ qMinus K t := by
      rcases hp with (hp | hp) | hp
      · obtain ⟨⟨t, s⟩, ⟨ht, hs0, hsY⟩, rfl⟩ := hp
        obtain ⟨hR, hL, hq⟩ := separated_core_below hφ hsep ht hs0
        exact ⟨by dsimp only; linarith, hR, hL,
          t, ⟨hφ0.trans ht.1, ht.2.trans hbv⟩, hq⟩
      · obtain ⟨hy0, hyR, hxR, hxw⟩ := hp
        have hR : p ∉ hRight φ K := (opt_notMem_hRight_iff hcos K p).2 (by linarith)
        obtain ⟨hL, hq⟩ := separated_right_triangle hφ hsep (by linarith) hyR hR
        exact ⟨hy0.le, hR, hL, φ, ⟨hφ0, by linarith⟩, hq⟩
      · obtain ⟨hy0, hyL, hxz, hxL⟩ := hp
        have hL : p ∉ hLeft φ K := (opt_notMem_hLeft_iff hcos K p).2 (by linarith)
        obtain ⟨hR, hq⟩ := separated_left_triangle hφ hsep (by linarith) hyL hL
        exact ⟨hy0.le, hR, hL, b, ⟨by linarith, hbv⟩, hq⟩
    obtain ⟨hy0, hR, hL, t, ht, hq⟩ := key
    refine ⟨⟨⟨?_, mem_iUnion₂.mpr ⟨t, ht, hq⟩⟩, hR⟩, hL⟩
    simpa [fan, halfPlus, dot_uvec_pi_div_two] using hy0
  have hfinite : volume ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) ≠ ⊤ :=
    volume_ne_top_of_subset (sdiff_subset.trans sdiff_subset)
      (nef_niche_isBounded hK).measure_lt_top.ne
  have harea := area_mono_of_finite hsub hfinite
  have aUnion : area (C ∪ R ∪ L) = I + τ * YR ^ 2 / 2 + τ * YL ^ 2 / 2 := by
    unfold area
    rw [vUnion, vC, vR, vL,
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
  have hCA := core_curveArea_rightVelocity hK hab.le
  have hsegR : segArea (wRight φ K) (xRight φ K) = w * YR / 2 := by
    simp only [opt_wRight_eq, xRight, segArea, cross]
    ring
  have hsegL : segArea (xLeft φ K) (zLeft φ K) = -YL * z / 2 := by
    simp only [opt_zLeft_eq, xLeft, segArea, cross]
    ring
  rw [hsegR, hsegL, hCA]
  have he : w * YR / 2 + ((XL * YL - XR * YR) / 2 + I) + -YL * z / 2 = area (C ∪ R ∪ L) := by
    rw [aUnion, hw, hz]
    ring
  rw [he]
  exact harea

end MovingSofaStability

end CoreAreaBound

/-!
## The local upper bound without Ki

Canonical-tail feasibility, cut separation, positive core height, and niche
containment are proved on a common neighborhood of Gerver. The original
three-region argument then gives A <= Q there.

Both remaining bounds come from the coercive certificate (`coercive_certificate`):
`𝒬 ≤ |G|` at the canonical triple, and the cap distance with coefficient
`2 / cos φ` (`nearby_cap_distance`).
-/

section LocalUpperBound

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

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
  have hRm : MeasurableSet (hRight φ K) := (isClosed_halfPlus _ _).measurableSet
  have hLm : MeasurableSet (hLeft φ K) := (isClosed_halfPlus _ _).measurableSet
  have hfin : volume (niche K (π / 2)) ≠ ⊤ := (nef_niche_isBounded hK).measure_lt_top.ne
  have hdisj := cut_regions_disjoint_of_width hφ hK hwidth
  have he3 : (niche K (π / 2) \ hRight φ K) ∩ hLeft φ K =
      niche K (π / 2) ∩ hLeft φ K := by
    ext p
    constructor
    · rintro ⟨⟨hp, -⟩, hL⟩; exact ⟨hp, hL⟩
    · rintro ⟨hp, hL⟩
      refine ⟨⟨hp, ?_⟩, hL⟩
      intro hR
      exact Set.disjoint_left.mp hdisj ⟨hNK hp, hR⟩ ⟨hNK hp, hL⟩
  have e1 := area_inter_add_sdiff (S := niche K (π / 2)) hRm hfin
  have e2 := area_inter_add_sdiff (S := niche K (π / 2) \ hRight φ K) hLm
    (volume_ne_top_of_subset sdiff_subset hfin)
  rw [he3] at e2
  have hdecomp : area (niche K (π / 2)) =
      area (niche K (π / 2) ∩ hRight φ K) + area (niche K (π / 2) ∩ hLeft φ K) +
      area ((niche K (π / 2) \ hRight φ K) \ hLeft φ K) := by linarith
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

/-- All local geometric hypotheses hold together, not as assumptions on an
arbitrary near-maximizer. The certificate's radius is independent of K. -/
theorem nearby_cap_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ K : Set Point,
      IsCap K (π / 2) → UpperSupportClose δ K P.cap →
        InWideL P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        niche K (π / 2) ⊆ K ∧
        sofaArea (π / 2) K ≤ upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ∧
        upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ area (gerverSofa P) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hKi := theorem8_1_1_gerver hP hbox
  obtain ⟨δT, hδT, hδT1, hT⟩ := nearby_canonical_inWideL hP hbox
  obtain ⟨δS, hδS, hδS1, hS⟩ := nearby_cutSeparated hP hbox
  obtain ⟨δH, hδH, hδH1, hH⟩ := nearby_core_height_pos hP hbox
  obtain ⟨δN, hδN, hδN1, hN⟩ := nearby_niche_subset_cap hP hbox
  obtain ⟨c, δA, hc, hδA, hδA1, hA⟩ := core_arm_margin_near_reference hKi hφ.1
    (b := π / 2 - P.φ) (by linarith [hφ.2]) (by linarith [hφ.1])
  let δ := min δT (min δS (min δH (min δN (min δA (1 / 20)))))
  have hδ : 0 < δ := lt_min hδT (lt_min hδS (lt_min hδH (lt_min hδN (lt_min hδA (by norm_num)))))
  have dT : δ ≤ δT := min_le_left _ _
  have dS : δ ≤ δS := (min_le_right _ _).trans (min_le_left _ _)
  have dH : δ ≤ δH := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have dN : δ ≤ δN := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have dA : δ ≤ δA := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have dW : δ ≤ (1 / 20 : ℝ) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨δ, hδ, dT.trans hδT1, ?_⟩
  intro K hK hclose
  have ht := hT K hK (hclose.mono dT)
  have hn := hN K hK (hclose.mono dN)
  have ha := separated_upperQ_bound hbox.1 hK (nearby_bottomWidth hP hbox (hclose.mono dW)) ht
    (hA K hK (hclose.mono dA)) hc (hS K hK (hclose.mono dS)) (hH K (hclose.mono dH)) hn
  have hq := (coercive_certificate hP hbox (canonicalWideTriple ht)).1
  exact ⟨ht, hn, ha, hq⟩

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
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K hK hclose
  obtain ⟨ht, hn, ha, hq⟩ := hcert K hK hclose
  have hd := (coercive_certificate hP hbox (canonicalWideTriple ht)).2
  have hc : 0 ≤ 2 / cos P.φ :=
    div_nonneg (by norm_num) (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  have hrad : (2 / cos P.φ) *
        sqrt (area (gerverSofa P) - upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K)) ≤
      (2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_left ha _)) hc
  exact ⟨hn, ha.trans hq, hd.mono hrad⟩

end MovingSofaStability

end LocalUpperBound
