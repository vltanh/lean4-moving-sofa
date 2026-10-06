module

public import MovingSofaStability.CoreGraph
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Change of variables and signed area for the nonsmooth core

A continuous primitive of the roof function is composed with the horizontal
coordinate. The right-derivative fundamental theorem then gives change of
variables without assuming a C1 competing cap.
-/

@[expose] public section
noncomputable section

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

/-- The signed core area is its graph integral and the usual endpoint term. -/
theorem core_curveArea_graph_integral {K : Set Point} (hK : IsCap K (π / 2))
    {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℝ} (hF : Continuous F)
    (hgraph : ∀ t ∈ Icc a b, F (innerCorner K t).1 = (innerCorner K t).2) :
    curveArea (innerCorner K) a b =
      (∫ x in (innerCorner K b).1..(innerCorner K a).1, F x) +
      (1 / 2) * ((innerCorner K b).1 * (innerCorner K b).2 -
        (innerCorner K a).1 * (innerCorner K a).2) := by
  obtain ⟨hi1, hi2⟩ := corner_coordinate_velocity_integrable hK a b
  have hiF : IntervalIntegrable
      (fun t => F (innerCorner K t).1 * (cornerRightVelocity K t).1) volume a b := by
    apply hi2.congr
    intro t ht
    rw [uIoc_of_le hab] at ht
    simp only [hgraph t (Ioc_subset_Icc_self ht)]
  have hsub := integral_comp_mul_rightDerivative hab
    (opt_innerCorner_continuous hK.2.1).fst.continuousOn hF
    (fun t _ => corner_fst_hasRightDeriv hK t) hiF
  have heq : (∫ t in a..b, F (innerCorner K t).1 * (cornerRightVelocity K t).1) =
      ∫ t in a..b, (innerCorner K t).2 * (cornerRightVelocity K t).1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp only [hgraph t ht]
  rw [heq] at hsub
  have hprod := corner_coordinate_product_integral hK hab
  rw [corner_curveArea_integral hK hab]
  have hcross : (fun t => cross (innerCorner K t) (cornerRightVelocity K t)) =
      fun t => (innerCorner K t).1 * (cornerRightVelocity K t).2 -
        (innerCorner K t).2 * (cornerRightVelocity K t).1 := rfl
  rw [hcross, intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_symm (f := F) (innerCorner K b).1 (innerCorner K a).1] at hsub
  linarith

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
