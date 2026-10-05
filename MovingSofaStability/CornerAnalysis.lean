module

public import MovingSofaStability.CanonicalTriple
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Analysis of nonsmooth corner paths

Uncompiled proof source. The corner velocity is expressed through the
measurable right derivative of a convex support. It is bounded and integrable.
The right-derivative fundamental theorem then identifies the curve's vector
measure with its density, without a C1 assumption on the cap.
-/

@[expose] public section
noncomputable section

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
    have h1 := abs_sub (supp K (t + π / 2)) (opt_g K t)
    have h2 := abs_sub (supp K (t + π / 2) - opt_g K t) 1
    have hs := support_abs_le_radius hK hradius (t + π / 2)
    have hd := hg t
    norm_num at h2
    linarith
  have hgplus : ∀ t, |gPlus K t - 1| ≤ 2 * R + 1 := by
    intro t
    rw [inj_gPlus_eq]
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
  exact hi1.prodMk hi2

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
