module

public import MovingSofaStability.Basic
public import MovingSofaStability.Deficit

/-!
# From the energies to the cap; the coercive certificate

The support function of a cap is reconstructed from the residuals on the four arcs of Gerver's cap; the
energies bound its distance to Gerver's support function with coefficient `2 sec φ`, by the exact kernel
integrals, and bounds on support functions become Euclidean distances between caps
(`sharp_wide_cap_distance_bound`, `sharp_ki_cap_distance_bound`). With the maximum of `𝒬`, this is the
coercive certificate (`coercive_certificate`).

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Integrating the residual equations without classical differentiability

Convex supports have right derivatives even at normal angles carrying atoms. The
reconstruction uses the right-derivative fundamental theorem on compact
intervals avoiding the integrating factor's singularity. Integrability of the
weighted residual is an explicit hypothesis, not inferred from the totalized
value of an integral.
-/

section ODEReconstruction

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Right-derivative version of the tangent integrating-factor identity. -/
theorem hasDerivWithinAt_tangentQuotient {f df : ℝ → ℝ} {T t : ℝ}
    (hd : HasDerivWithinAt f (df t) (Ioi t) t) (hs : sin (T - t) ≠ 0) :
    HasDerivWithinAt (tangentQuotient T f)
      (-tangentResidual T f df t / sin (T - t)) (Ioi t) t := by
  have hu : HasDerivWithinAt (fun s : ℝ => T - s) (-1) (Ioi t) t := by
    simpa using ((hasDerivAt_id t).const_sub T).hasDerivWithinAt
  have hquot := (hd.sub (hu.cos.const_mul (f T))).div hu.sin hs
  convert hquot using 1
  · rfl
  · dsimp only [tangentResidual]
    have hweighted : f T * (sin (T - t) ^ 2 + cos (T - t) ^ 2) = f T := by
      rw [sin_sq_add_cos_sq, mul_one]
    simp only [Pi.sub_apply]
    field_simp
    linear_combination hweighted

/-- The integral of a weighted residual is the difference of the quotient values. -/
theorem tangent_quotient_integral {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    (∫ t in a..b, tangentResidual T f df t / sin (T - t)) =
      tangentQuotient T f a - tangentQuotient T f b := by
  have hcos : Continuous (fun t : ℝ => cos (T - t)) := by fun_prop
  have hsin : Continuous (fun t : ℝ => sin (T - t)) := by fun_prop
  have hcont : ContinuousOn (tangentQuotient T f) (Icc a b) :=
    (hf.sub (hcos.continuousOn.const_mul (f T))).div hsin.continuousOn hs
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (tangentQuotient T f)
        (-(tangentResidual T f df t / sin (T - t))) (Ioi t) t := by
    intro t ht
    simpa only [neg_div] using
      hasDerivWithinAt_tangentQuotient (hd t ht) (hs t ⟨ht.1.le, ht.2.le⟩)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- Solve backwards from the right endpoint on a nonsingular interval. -/
theorem tangent_reconstruct_left {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f a = f T * cos (T - a) + sin (T - a) *
      (tangentQuotient T f b + ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  have h := tangent_quotient_integral hab hf hd hs hi
  have hsa := hs a ⟨le_rfl, hab⟩
  rw [h]
  unfold tangentQuotient
  field_simp [hsa]
  ring

/-- Solve forwards from the left endpoint on a nonsingular interval. -/
theorem tangent_reconstruct_right {f df : ℝ → ℝ} {a b T : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0)
    (hi : IntervalIntegrable (fun t => tangentResidual T f df t / sin (T - t)) volume a b) :
    f b = f T * cos (T - b) + sin (T - b) *
      (tangentQuotient T f a - ∫ t in a..b, tangentResidual T f df t / sin (T - t)) := by
  have h := tangent_quotient_integral hab hf hd hs hi
  have hsb := hs b ⟨hab, le_rfl⟩
  rw [h]
  unfold tangentQuotient
  field_simp [hsb]
  ring

/-- The middle residual has no integrating-factor denominator. -/
theorem corner_reconstruct {f df : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt f (df t) (Ioi t) t)
    (hdf : IntervalIntegrable df volume a b)
    (hshift : IntervalIntegrable (fun t => f (t + π / 2)) volume a b) :
    f a = f b - (∫ t in a..b, f (t + π / 2)) +
      ∫ t in a..b, cornerResidual f df t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hf hd hdf
  unfold cornerResidual
  rw [intervalIntegral.integral_sub hshift hdf, h]
  ring

/-- Support differences have a right derivative at every normal, not just away from atoms. -/
theorem support_difference_rightDerivative {K₀ K₁ : Set (ℝ × ℝ)}
    (h₀ : IsConvexBody K₀) (h₁ : IsConvexBody K₁) (t : ℝ) :
    HasDerivWithinAt (fun u => supp K₁ u - supp K₀ u)
      (opt_g K₁ t - opt_g K₀ t) (Ioi t) t := by
  exact ((hasDerivWithinAt_supp_right h₁ t).sub
    (hasDerivWithinAt_supp_right h₀ t)).mono Ioi_subset_Ici_self

/-- The pinned support difference still has right derivatives at all normals. -/
theorem pinned_support_rightDerivative {K₀ K₁ : Set (ℝ × ℝ)}
    (h₀ : IsConvexBody K₀) (h₁ : IsConvexBody K₁) (t : ℝ) :
    HasDerivWithinAt (pinnedDifference (fun u => supp K₁ u - supp K₀ u))
      (pinnedDerivative (fun u => supp K₁ u - supp K₀ u)
        (fun u => opt_g K₁ u - opt_g K₀ u) t) (Ioi t) t := by
  have hd := support_difference_rightDerivative h₀ h₁ t
  have hcos := ((hasDerivAt_cos t).const_mul (supp K₁ π - supp K₀ π)).hasDerivWithinAt
    (s := Ioi t)
  have he : pinnedDerivative (fun u => supp K₁ u - supp K₀ u)
      (fun u => opt_g K₁ u - opt_g K₀ u) t =
      opt_g K₁ t - opt_g K₀ t + (supp K₁ π - supp K₀ π) * -sin t := by
    simp only [pinnedDerivative]; ring
  rw [he]
  exact hd.add hcos

end MovingSofaStability

end ODEReconstruction

/-!
## Integrability of the actual cap residuals

Mamikon's boundedness theorem supplies both first and second integrability.
Endpoint values of a tangent quotient are not identified with its geometric
displacement at a singular endpoint: the identification is made on the open
interval, then transferred across the two null singletons.
-/

section ResidualIntegrability

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Differences of Mamikon displacements have finite first and second moments. -/
theorem displacement_difference_integrable {a b : ℝ} (hab : a < b) (hb : b < a + π)
    (z : ConvexBodySet → ℝ → ℝ × ℝ)
    (hz : ∀ K, IsCBV (z K) a b)
    (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
    (K₀ K₁ : ConvexBodySet) :
    IntegrableOn (fun t => displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t)
        (Icc a b) volume ∧
      IntegrableOn (fun t => (displacement K₁.1 (z K₁) t -
        displacement K₀.1 (z K₀) t) ^ 2) (Icc a b) volume := by
  have hM := fun K : ConvexBodySet => theorem7_4_1 K.2 hab hb (hz K) (hzl K)
  obtain ⟨C₀, hC₀⟩ := (hM K₀).2.1
  obtain ⟨C₁, hC₁⟩ := (hM K₁).2.1
  let f : ℝ → ℝ := fun t => displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t
  have hbound : ∀ t ∈ Icc a b, |f t| ≤ C₁ + C₀ := by
    intro t ht
    exact (abs_sub _ _).trans (add_le_add (hC₁ t ht) (hC₀ t ht))
  have hC : 0 ≤ C₁ + C₀ := (abs_nonneg (f a)).trans (hbound a ⟨le_rfl, hab.le⟩)
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hm : AEStronglyMeasurable f (volume.restrict (Icc a b)) :=
    ((hM K₁).1.sub (hM K₀).1).aestronglyMeasurable
  have hi : IntegrableOn f (Icc a b) volume := by
    apply Integrable.of_bound hm (C₁ + C₀)
    exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht => by
      simpa only [Real.norm_eq_abs] using hbound t ht
  have hi2 : IntegrableOn (fun t => f t * f t) (Icc a b) volume := by
    apply Integrable.of_bound (hm.mul hm) ((C₁ + C₀) * (C₁ + C₀))
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    exact mul_le_mul (hbound t ht) (hbound t ht) (abs_nonneg _) hC
  exact ⟨hi, hi2.congr (Eventually.of_forall fun t => (pow_two (f t)).symm)⟩

/-- Move an identity valid on the open interval across its measure-zero endpoints. -/
theorem integrableOn_Icc_of_eqOn_Ioo {a b : ℝ} {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b) volume) (he : EqOn f g (Ioo a b)) :
    IntegrableOn g (Icc a b) volume := by
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact (hf.mono_set Ioo_subset_Icc_self).congr
    (ae_restrict_of_forall_mem measurableSet_Ioo he)

/-- A uniform notation for the pinned difference of two convex supports. -/
def capDifference (K₀ K₁ : Set (ℝ × ℝ)) : ℝ → ℝ :=
  pinnedDifference (fun t => supp K₁ t - supp K₀ t)

def capDifferenceDeriv (K₀ K₁ : Set (ℝ × ℝ)) : ℝ → ℝ :=
  pinnedDerivative (fun t => supp K₁ t - supp K₀ t)
    (fun t => opt_g K₁ t - opt_g K₀ t)

theorem capDifference_continuous {K₀ K₁ : Set (ℝ × ℝ)}
    (h₀ : IsConvexBody K₀) (h₁ : IsConvexBody K₁) : Continuous (capDifference K₀ K₁) := by
  exact (h₁.continuous_supp.sub h₀.continuous_supp).add
    (continuous_cos.const_mul (supp K₁ π - supp K₀ π))

/-- Tangent residuals of pinned support differences are genuinely integrable,
including when the competing bodies have curvature atoms. -/
theorem tangent_capDifference_integrable {a b T : ℝ}
    (hab : a < b) (hb : b < a + π) (haT : T - π < a) (hbT : b ≤ T)
    (K₀ K₁ : ConvexBodySet) :
    IntegrableOn (tangentResidual T (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1)) (Icc a b) volume ∧
      IntegrableOn (fun t => (tangentResidual T (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1) t) ^ 2) (Icc a b) volume := by
  let z := fun K : ConvexBodySet => tangentParam K.1 T
  have hz : ∀ K, IsCBV (z K) a b := fun K => (theorem8_3_1 K.2 haT hab.le hbT).1
  have hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t := by
    intro K t ht
    by_cases h : t < T
    · simp only [z, tangentParam, h, ↓reduceIte]
      exact vint_mem_line_left K.1 t T
    · have he : t = T := le_antisymm (ht.2.trans hbT) (not_lt.mp h)
      subst t
      simp only [z, tangentParam, lt_irrefl, ↓reduceIte]
      exact dot_vminus_uvec K.1 T
  obtain ⟨hi, hi2⟩ := displacement_difference_integrable hab hb z hz hzl K₀ K₁
  have he : ∀ t ∈ Ioo a b,
      displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t =
      tangentResidual T (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t := by
    intro t ht
    have htT : t < T := ht.2.trans_le hbT
    have hs : sin (T - t) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1])).ne'
    rw [capDifference, capDifferenceDeriv, tangentResidual_pinned _ _ _ _ hs]
    exact tangent_displacement_sub htT
  refine ⟨integrableOn_Icc_of_eqOn_Ioo hi he, ?_⟩
  exact integrableOn_Icc_of_eqOn_Ioo hi2 fun t ht => congrArg (fun u : ℝ => u ^ 2) (he t ht)

/-- The middle, outer-corner residual has the same first/second integrability. -/
theorem corner_capDifference_integrable {a b : ℝ} (hab : a < b) (hb : b < a + π)
    (K₀ K₁ : ConvexBodySet) :
    IntegrableOn (cornerResidual (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1)) (Icc a b) volume ∧
      IntegrableOn (fun t => (cornerResidual (capDifference K₀.1 K₁.1)
        (capDifferenceDeriv K₀.1 K₁.1) t) ^ 2) (Icc a b) volume := by
  let z := fun K : ConvexBodySet => outerCorner K.1
  obtain ⟨hi, hi2⟩ := displacement_difference_integrable hab hb z
    (fun K => opt_outerCorner_cbv K.2 a b)
    (fun K t _ => inj_dot_outerCorner_uvec K.1 t) K₀ K₁
  have he : ∀ t,
      displacement K₁.1 (z K₁) t - displacement K₀.1 (z K₀) t =
      cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t := by
    intro t
    rw [capDifference, capDifferenceDeriv, cornerResidual_pinned]
    exact outer_displacement_sub K₀.1 K₁.1 t
  exact ⟨hi.congr (Eventually.of_forall he),
    hi2.congr (Eventually.of_forall fun t => congrArg (fun u : ℝ => u ^ 2) (he t))⟩

end MovingSofaStability

end ResidualIntegrability

/-!
## First-moment bounds for residual reconstruction

These estimates give a deliberately non-sharp route from the four residual
equations to cap stability. They avoid the double integral calculation needed to
identify the sharp Green norm.
-/

section ResidualMass

open Real Set MeasureTheory Filter

namespace MovingSofaStability

def arcSquare (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t ^ 2

theorem arcSquare_nonneg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : 0 ≤ arcSquare a b f :=
  intervalIntegral.integral_nonneg_of_forall hab fun _ => sq_nonneg _


end MovingSofaStability

end ResidualMass

/-!
## Stable propagation of the support residual equations

The last-arc integrating factor has an apparent singularity at pi. Its
evaluation kernel is a contraction: sin(t)/sin(u) <= 1 for pi/2 <= u <= t < pi.
Thus its first moment is enough for a uniform bound; no exchange of two improper
integrals or claimed sharp kernel norm is needed.
-/

section ResidualPropagation

open Real Set MeasureTheory

namespace MovingSofaStability

/-- Restrict an interval-integrable function to an ordered subinterval. -/
theorem intervalIntegrable_subinterval {a b c d : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    IntervalIntegrable f volume c d := by
  apply hf.mono_set
  rw [uIcc_of_le hcd, uIcc_of_le (hac.trans (hcd.trans hdb))]
  exact Icc_subset_Icc hac hdb

/-- A continuous reciprocal can multiply a residual on any nonsingular compact arc. -/
theorem residual_div_sin_integrable {a b T : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hr : IntervalIntegrable r volume a b)
    (hs : ∀ t ∈ Icc a b, sin (T - t) ≠ 0) :
    IntervalIntegrable (fun t => r t / sin (T - t)) volume a b := by
  have hc : ContinuousOn (fun t => 1 / sin (T - t)) (Icc a b) :=
    continuousOn_const.div (continuous_sin.comp (continuous_const.sub continuous_id)).continuousOn
      hs
  simpa only [one_div, div_eq_mul_inv] using
    hr.mul_continuousOn (by simpa only [uIcc_of_le hab, one_div] using hc)


end MovingSofaStability

end ResidualPropagation

/-!
## Four-arc coercivity with an explicit non-sharp constant

This proves a complete analytic estimate with constant 80. Unlike the separate
sharp Green-norm formulas, it needs neither Fubini nor an unproved
kernel-integral identification. The hypotheses describe continuity, right
derivatives and integrability, not a stability estimate in disguise.
-/

section FourArcCoercivity

open Real Set MeasureTheory

namespace MovingSofaStability

structure FourResidualData (φ : ℝ) (f df : ℝ → ℝ) : Prop where
  continuous : Continuous f
  rightDeriv : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivWithinAt f (df t) (Ioi t) t
  top_zero : f (π / 2) = 0
  left_zero : f π = 0
  first : IntervalIntegrable (tangentResidual (π / 2) f df) volume 0 φ
  middle : IntervalIntegrable (cornerResidual f df) volume φ (π / 2 - φ)
  third : IntervalIntegrable (tangentResidual (π - φ) f df) volume (π / 2 - φ) (π / 2)
  last : IntervalIntegrable (tangentResidual π f df) volume (π / 2) π
  first_sq : IntervalIntegrable (fun t => tangentResidual (π / 2) f df t ^ 2) volume 0 φ
  middle_sq : IntervalIntegrable (fun t => cornerResidual f df t ^ 2) volume φ (π / 2 - φ)
  third_sq : IntervalIntegrable (fun t => tangentResidual (π - φ) f df t ^ 2)
    volume (π / 2 - φ) (π / 2)
  last_sq : IntervalIntegrable (fun t => tangentResidual π f df t ^ 2) volume (π / 2) π

def fourResidualEnergy (φ : ℝ) (f df : ℝ → ℝ) : ℝ :=
  (arcSquare 0 φ (tangentResidual (π / 2) f df) +
   arcSquare φ (π / 2 - φ) (cornerResidual f df) +
   arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
   arcSquare (π / 2) π (tangentResidual π f df)) / 2

/-- The short first and third arcs have no small denominator. -/
theorem cos_ge_half_of_small {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) : (1 / 2 : ℝ) ≤ cos t := by
  have hφ1 : φ < 1 := by linarith [hφ.2, pi_lt_four]
  have h := one_sub_sq_div_two_le_cos (x := t)
  nlinarith [ht.1, ht.2]


end MovingSofaStability

end FourArcCoercivity

/-!
## Cap support coercivity from the actual Mamikon deficit

The analytic hypotheses are discharged for convex supports and the four square
integrals are identified with the existing cap energy. The resulting coefficient
80 is deliberately non-sharp; it suffices for the unrestricted theorem's
existence of a square-root constant.

This is not the separate sharp 2 sec(phi) result. No kernel norm identity,
residual integrability, or squared support bound is assumed in the final lemmas.
-/

section CapCoercivity

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Convex support differences satisfy every analytic hypothesis of coercivity. -/
theorem capDifference_data {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2)) :
    FourResidualData φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) := by
  have hp := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  obtain ⟨i₁, s₁⟩ := tangent_capDifference_integrable (T := π / 2) (a := 0) (b := φ)
    hp0 (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₂, s₂⟩ := corner_capDifference_integrable (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₃, s₃⟩ := tangent_capDifference_integrable (T := π - φ)
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁
  obtain ⟨i₄, s₄⟩ := tangent_capDifference_integrable (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁
  refine ⟨capDifference_continuous K₀.2 K₁.2, ?_, ?_, ?_,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hp0.le).2 i₁,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₂,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₃,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 i₄,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hp0.le).2 s₁,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₂,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₃,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 s₄⟩
  · intro t ht
    exact pinned_support_rightDerivative K₀.2 K₁.2 t
  · change pinnedDifference (fun t => supp K₁.1 t - supp K₀.1 t) (π / 2) = 0
    rw [pinnedDifference_top, h₁.2.2.2.1, h₀.2.2.2.1, sub_self]
  · exact pinnedDifference_pi _

/-- The tangent residual square integral is twice the geometric difference energy. -/
theorem tangent_arcSquare_eq_energy {a b T : ℝ}
    (hab : a < b) (haT : T - π < a) (hbT : b ≤ T) (K₀ K₁ : ConvexBodySet) :
    arcSquare a b (tangentResidual T (capDifference K₀.1 K₁.1)
      (capDifferenceDeriv K₀.1 K₁.1)) =
      2 * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  unfold arcSquare displacementEnergy halfSquareIntegral
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have he : (∫ t in Ioo a b,
      tangentResidual T (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) =
      ∫ t in Ioo a b, (displacement K₀.1 (tangentParam K₀.1 T) t -
        displacement K₁.1 (tangentParam K₁.1 T) t) ^ 2 := by
    apply integral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    have htT : t < T := ht.2.trans_le hbT
    have hs : sin (T - t) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1])).ne'
    dsimp only
    rw [capDifference, capDifferenceDeriv, tangentResidual_pinned _ _ _ _ hs]
    simp only [opt_g]
    rw [← tangent_displacement_sub htT]
    ring
  rw [he]
  ring

/-- The corresponding middle-arc identity has no singular tangent endpoint. -/
theorem corner_arcSquare_eq_energy {a b : ℝ} (hab : a ≤ b) (K₀ K₁ : ConvexBodySet) :
    arcSquare a b (cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1)) =
      2 * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ := by
  unfold arcSquare displacementEnergy halfSquareIntegral
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  have he : (∫ t in Ioo a b,
      cornerResidual (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) t ^ 2) =
      ∫ t in Ioo a b, (displacement K₀.1 (outerCorner K₀.1) t -
        displacement K₁.1 (outerCorner K₁.1) t) ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [capDifference, capDifferenceDeriv, cornerResidual_pinned]
      simp only [opt_g]
      rw [← outer_displacement_sub K₀.1 K₁.1 t]
      ring
  rw [he]
  ring

/-- The analytic residual energy and the four Mamikon integrals are identical. -/
theorem fourResidualEnergy_eq_capEnergy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) :
    fourResidualEnergy φ (capDifference K₀.1 K₁.1) (capDifferenceDeriv K₀.1 K₁.1) =
      capResidualEnergy φ K₀ K₁ := by
  have hp := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  have e₁ := tangent_arcSquare_eq_energy (a := 0) (b := φ) (T := π / 2)
    hp0 (by linarith) (by linarith) K₀ K₁
  have e₂ := corner_arcSquare_eq_energy (a := φ) (b := π / 2 - φ) (by linarith) K₀ K₁
  have e₃ := tangent_arcSquare_eq_energy (a := π / 2 - φ) (b := π / 2) (T := π - φ)
    (by linarith) (by linarith) (by linarith) K₀ K₁
  have e₄ := tangent_arcSquare_eq_energy (a := π / 2) (b := π) (T := π)
    (by linarith) (by linarith) le_rfl K₀ K₁
  unfold fourResidualEnergy capResidualEnergy
  rw [e₁, e₂, e₃, e₄, show π / 2 + (π / 2 - φ) = π - φ by ring]
  ring


end MovingSofaStability

end CapCoercivity

/-!
## From convex support bounds to actual Euclidean distance

The proof uses the Euclidean parallel body K + rB, whose support is h_K + r. It
supplies witnesses in the actual convex set and does not equate support distance
with Hausdorff distance for nonconvex sofas.
-/

section SupportDistance

open Real Set
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

theorem continuous_norm2 : Continuous (norm2 : Point → ℝ) := by
  unfold norm2 dot
  fun_prop

theorem norm2_smul (a : ℝ) (p : Point) : norm2 (a • p) = |a| * norm2 p := by
  have hsq : norm2 (a • p) ^ 2 = (|a| * norm2 p) ^ 2 := by
    rw [norm2_sq, mul_pow, sq_abs, norm2_sq, dot_smul_left, dot_smul_right]
    ring
  have h₁ := norm2_nonneg (a • p)
  have h₂ := mul_nonneg (abs_nonneg a) (norm2_nonneg p)
  nlinarith

theorem abs_fst_le_norm2 (p : Point) : |p.1| ≤ norm2 p := by
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, abs_nonneg p.1, sq_abs p.1, sq_nonneg p.2]

theorem abs_snd_le_norm2 (p : Point) : |p.2| ≤ norm2 p := by
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, abs_nonneg p.2, sq_abs p.2, sq_nonneg p.1]

/-- Comparison with the product norm is used only for topology and compactness. -/
theorem product_norm_le_norm2 (p : Point) : ‖p‖ ≤ norm2 p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_fst_le_norm2 p) (abs_snd_le_norm2 p)

theorem norm2_le_two_product_norm (p : Point) : norm2 p ≤ 2 * ‖p‖ := by
  have h₁ := norm_fst_le p
  have h₂ := norm_snd_le p
  rw [Real.norm_eq_abs] at h₁ h₂
  have hs := norm2_sq p
  simp only [dot] at hs
  nlinarith [norm2_nonneg p, norm_nonneg p, abs_nonneg p.1, abs_nonneg p.2,
    sq_abs p.1, sq_abs p.2]

def euclideanDisk (r : ℝ) : Set Point := {p | norm2 p ≤ r}

theorem euclideanDisk_isConvexBody {r : ℝ} (hr : 0 ≤ r) : IsConvexBody (euclideanDisk r) := by
  have hclosed : IsClosed (euclideanDisk r) := isClosed_le continuous_norm2 continuous_const
  have hsub : euclideanDisk r ⊆ Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    exact ⟨abs_le.mp ((abs_fst_le_norm2 p).trans hp),
      abs_le.mp ((abs_snd_le_norm2 p).trans hp)⟩
  refine ⟨⟨0, by simpa only [euclideanDisk, mem_ofPred_eq, norm2_zero] using hr⟩,
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub, ?_⟩
  intro p hp q hq a b ha hb hab
  change norm2 (a • p + b • q) ≤ r
  have h := norm2_add_le (a • p) (b • q)
  rw [norm2_smul, norm2_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h
  have hpa := mul_le_mul_of_nonneg_left hp ha
  have hqb := mul_le_mul_of_nonneg_left hq hb
  have he : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  linarith

/-- Minkowski sums of nonempty compact convex sets stay in the same class. -/
theorem convexBody_add {K L : Set Point} (hK : IsConvexBody K) (hL : IsConvexBody L) :
    IsConvexBody (K + L) := by
  obtain ⟨p, hp⟩ := hK.1
  obtain ⟨q, hq⟩ := hL.1
  exact ⟨⟨p + q, ⟨p, hp, q, hq, rfl⟩⟩, hK.2.1.add hL.2.1, hK.2.2.add hL.2.2⟩

/-- Euclidean parallel bodies add exactly r to every support value. -/
theorem supp_add_euclideanDisk {K : Set Point} (hK : IsConvexBody K)
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : supp (K + euclideanDisk r) t = supp K t + r := by
  have hD := euclideanDisk_isConvexBody hr
  have hsum := convexBody_add hK hD
  obtain ⟨p, hp, hps⟩ := exists_dot_eq_supp hK.2.1 hK.1 t
  have hrad : r • uvec t ∈ euclideanDisk r := by
    change norm2 (r • uvec t) ≤ r
    rw [norm2_smul, norm2_uvec, mul_one, abs_of_nonneg hr]
  apply supp_eq_of_mem hsum.2.1
  · rintro _ ⟨q, hq, z, hz, rfl⟩
    rw [dot_add_left]
    exact add_le_add (dot_le_supp hK.2.1 hq t) ((dot_uvec_le_norm2 z t).trans hz)
  · exact ⟨p, hp, r • uvec t, hrad, rfl⟩
  · rw [dot_add_left, hps, dot_smul_left, dot_uvec_self, mul_one]

/-- Support containment supplies an actual point of the target within Euclidean radius r. -/
theorem directedClose_of_support_le {S T : Set Point} (hS : IsCompact S)
    (hT : IsConvexBody T) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, supp S t ≤ supp T t + r) : DirectedClose r S T := by
  intro p hp
  have hsum := convexBody_add hT (euclideanDisk_isConvexBody hr)
  have hm : p ∈ T + euclideanDisk r := by
    apply (mem_iff_forall_dot_le_supp hsum p).2
    intro t
    rw [supp_add_euclideanDisk hT hr]
    exact (dot_le_supp hS hp t).trans (h t)
  obtain ⟨q, hq, z, hz, hqz⟩ := hm
  refine ⟨q, hq, ?_⟩
  rw [← hqz]
  change norm2 (q + z - q) ≤ r
  rw [add_sub_cancel_left]
  exact hz

/-- The support criterion for Euclidean Hausdorff distance between convex bodies. -/
theorem euclideanClose_of_support_bound {K L : Set Point}
    (hK : IsConvexBody K) (hL : IsConvexBody L) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ t, |supp K t - supp L t| ≤ r) : EuclideanClose r K L := by
  constructor
  · apply directedClose_of_support_le hK.2.1 hL hr
    intro t
    have ht := (abs_le.mp (h t)).2
    linarith
  · apply directedClose_of_support_le hL.2.1 hK hr
    intro t
    have ht := (abs_le.mp (h t)).1
    linarith

/-- A translation preserves compact convexity. -/
theorem convexBody_translate {K : Set Point} (hK : IsConvexBody K) (v : Point) :
    IsConvexBody ((fun p => p + v) '' K) := by
  refine ⟨hK.1.image _, hK.2.1.image (continuous_id.add continuous_const), ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hK.2.2 hp hq ha hb hab, ?_⟩
  have hv : (a + b) • v = v := by rw [hab, one_smul]
  calc
    (a • p + b • q) + v = (a • p + b • q) + (a + b) • v := by rw [hv]
    _ = a • (p + v) + b • (q + v) := by
      simp only [add_smul, smul_add]
      abel

end MovingSofaStability

end SupportDistance

/-!
## Euclidean cap-distance certificate

The upper-semicircle coercivity estimate is extended to all directions using the
cap's two bottom endpoints, then converted to actual Euclidean Hausdorff
witnesses. The coefficient 80 is non-sharp.
-/

section CapDistance

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- On the lower-right semicircle a cap is supported by its right bottom endpoint. -/
theorem cap_lower_right_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : 0 ≤ cos t) : supp K t = supp K 0 * cos t := by
  apply supp_eq_of_mem hK.2.1.2.1
  · intro p hp
    have hx := (opt_cap_fst_le hK hp).2
    have hy := (inj_cap_strip hK hp).1
    have hxc := mul_le_mul_of_nonneg_right hx hc
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hs
    simp only [dot, uvec]
    linarith
  · exact opt_cap_A_mem hK
  · simp [dot, uvec]

/-- The lower-left counterpart uses the left bottom endpoint. -/
theorem cap_lower_left_support {K : Set Point} (hK : IsCap K (π / 2)) {t : ℝ}
    (hs : sin t ≤ 0) (hc : cos t ≤ 0) : supp K t = -supp K π * cos t := by
  apply supp_eq_of_mem hK.2.1.2.1
  · intro p hp
    have hx := (opt_cap_fst_le hK hp).1
    have hy := (inj_cap_strip hK hp).1
    have hxc := mul_le_mul_of_nonpos_right hx hc
    have hys : p.2 * sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hs
    simp only [dot, uvec]
    linarith
  · exact opt_cap_C_mem hK
  · simp [dot, uvec]

/-- Every unit normal with nonnegative ordinate has a representative in [0,pi]. -/
theorem upper_normal_representative (t : ℝ) (hs : 0 ≤ sin t) :
    ∃ s ∈ Icc (0 : ℝ) π, uvec s = uvec t ∧ cos s = cos t := by
  let s := arccos (cos t)
  have hsc : cos s = cos t := cos_arccos (neg_one_le_cos t) (cos_le_one t)
  have hsi : s ∈ Icc (0 : ℝ) π := ⟨arccos_nonneg _, arccos_le_pi _⟩
  have hss : sin s = sin t := by
    have hs0 := sin_nonneg_of_nonneg_of_le_pi hsi.1 hsi.2
    have h1 := sin_sq_add_cos_sq s
    have h2 := sin_sq_add_cos_sq t
    rw [hsc] at h1
    nlinarith
  refine ⟨s, hsi, ?_, hsc⟩
  ext <;> simp only [uvec, hsc, hss]

/-- No periodic-supremum assumption is needed to extend the cap support bound. -/
theorem capDifference_bound_all {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) :
    ∀ t, |capDifference K₀ K₁ t| ≤ R := by
  intro t
  by_cases hs : 0 ≤ sin t
  · obtain ⟨s, hsi, hu, hc⟩ := upper_normal_representative t hs
    have h0 : supp K₀ s = supp K₀ t := by simp only [supp, hu]
    have h1 : supp K₁ s = supp K₁ t := by simp only [supp, hu]
    have hd : capDifference K₀ K₁ s = capDifference K₀ K₁ t := by
      simp only [capDifference, pinnedDifference, h0, h1, hc]
    rw [← hd]
    exact hupper s hsi
  have hs' : sin t ≤ 0 := (not_le.mp hs).le
  by_cases hc : 0 ≤ cos t
  · have he : capDifference K₀ K₁ t = capDifference K₀ K₁ 0 * cos t := by
      simp only [capDifference, pinnedDifference,
        cap_lower_right_support h₀ hs' hc, cap_lower_right_support h₁ hs' hc, cos_zero]
      ring
    rw [he, abs_mul]
    have h0 := hupper 0 ⟨le_rfl, pi_pos.le⟩
    exact (mul_le_mul h0 (abs_cos_le_one t) (abs_nonneg _) hR).trans_eq (mul_one R)
  · have he : capDifference K₀ K₁ t = 0 := by
      simp only [capDifference, pinnedDifference,
        cap_lower_left_support h₀ hs' (not_le.mp hc).le,
        cap_lower_left_support h₁ hs' (not_le.mp hc).le]
      ring
    simpa only [he, abs_zero] using hR

/-- The reference is shifted left by the competing cap's left-support error. -/
def capReferenceShift (K₀ K₁ : Set Point) : Point := (-(supp K₁ π - supp K₀ π), 0)

def shiftedReferenceCap (K₀ K₁ : Set Point) : Set Point :=
  (fun p => p + capReferenceShift K₀ K₁) '' K₀

theorem capDifference_eq_shifted_support {K₀ K₁ : Set Point}
    (h₀ : IsConvexBody K₀) (t : ℝ) :
    capDifference K₀ K₁ t = supp K₁ t - supp (shiftedReferenceCap K₀ K₁) t := by
  unfold shiftedReferenceCap
  rw [supp_translate K₀ _ t h₀.2.1 h₀.1]
  simp only [capDifference, pinnedDifference, capReferenceShift, dot, uvec]
  ring

/-- Upper support control yields Euclidean Hausdorff control after the explicit translation. -/
theorem cap_euclideanClose_of_upper_support {K₀ K₁ : Set Point}
    (h₀ : IsCap K₀ (π / 2)) (h₁ : IsCap K₁ (π / 2)) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ t ∈ Icc (0 : ℝ) π, |capDifference K₀ K₁ t| ≤ R) :
    EuclideanClose R K₁ (shiftedReferenceCap K₀ K₁) := by
  apply euclideanClose_of_support_bound h₁.2.1
    (convexBody_translate h₀.2.1 (capReferenceShift K₀ K₁)) hR
  intro t
  change |supp K₁ t - supp (shiftedReferenceCap K₀ K₁) t| ≤ R
  rw [← capDifference_eq_shifted_support h₀.2.1 t]
  exact capDifference_bound_all h₀ h₁ hR hupper t

/-- No translation remains when the reference and competitor have the same left support. -/
theorem shiftedReferenceCap_eq_of_left_support {K₀ K₁ : Set Point}
    (h : supp K₁ π = supp K₀ π) : shiftedReferenceCap K₀ K₁ = K₀ := by
  simp [shiftedReferenceCap, capReferenceShift, h, Prod.mk_zero_zero]

end MovingSofaStability

end CapDistance

/-!
## Algebraic bound for the four-piece Green evaluation norm

The four formulas here are the squared evaluation norms calculated in stability
note 01. This file bounds them and proves the rational numerical constant.
Identifying them with the square integrals of the reconstruction kernels is a
distinct analytic obligation.
-/

section GreenNorm

open Real Set

namespace MovingSofaStability

/-- The four candidate squared norms of the Green evaluation kernels. -/
def greenNormSquared (φ t : ℝ) : ℝ :=
  if t ≤ φ then cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t)
  else if t ≤ π / 2 - φ then cos t * (2 / cos φ - sin t)
  else if t ≤ π / 2 then sin t * cos t + 2 * tan φ * cos t ^ 2
  else -sin t * cos t

/-- Trigonometric quantities in the cap argument, without decimal approximation. -/
theorem cap_angle_parameters {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    0 < cos φ ∧ 1 ≤ 1 / cos φ ∧ 0 ≤ tan φ ∧
      (1 / cos φ) ^ 2 = 1 + tan φ ^ 2 := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  have hA : 1 ≤ 1 / cos φ := by
    apply (le_div_iff₀ hc).2
    simpa using cos_le_one φ
  have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi hφ.1.le (by linarith [hφ.2])
  have hu : 0 ≤ tan φ := by rw [tan_eq_sin_div_cos]; exact div_nonneg hs hc.le
  refine ⟨hc, hA, hu, ?_⟩
  rw [tan_eq_sin_div_cos]
  have he := sin_sq_add_cos_sq φ
  field_simp [hc.ne']
  nlinarith

/-- The closed-form evaluation norm never exceeds its value at zero. -/
theorem greenNormSquared_le {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 π) : greenNormSquared φ t ≤ 2 * (1 / cos φ) ^ 2 := by
  obtain ⟨hcφ, hA, htanφ, hAid⟩ := cap_angle_parameters hφ
  have hAA : 1 ≤ (1 / cos φ) ^ 2 := by nlinarith
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have hcost : cos t ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t)]
  have hprod : sin t * cos t ≤ 1 / 2 := by
    nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t)]
  unfold greenNormSquared
  split_ifs with h1 h2 h3
  · have hct : 0 < cos t := cos_pos_of_mem_Ioo
      ⟨by linarith [pi_pos, ht.1], by linarith [hφ.2, pi_pos]⟩
    have htnt : 0 ≤ tan t := by rw [tan_eq_sin_div_cos]; exact div_nonneg hs hct.le
    have hmul : 0 ≤ cos t ^ 2 * tan t := mul_nonneg (sq_nonneg _) htnt
    have hscale := mul_le_mul_of_nonneg_right hcost
      (show 0 ≤ 2 * (1 / cos φ) ^ 2 by positivity)
    nlinarith
  · have hct : 0 ≤ cos t := (cos_pos_of_mem_Ioo
      ⟨by linarith [pi_pos, ht.1], by linarith [hφ.1]⟩).le
    have hterm : 0 ≤ cos t * sin t := mul_nonneg hct hs
    have hscale := mul_le_mul_of_nonneg_right (cos_le_one t)
      (show 0 ≤ 2 * (1 / cos φ) by positivity)
    have hrewrite : 2 / cos φ = 2 * (1 / cos φ) := by ring
    rw [hrewrite]
    nlinarith
  · have hscale := mul_le_mul_of_nonneg_left hcost
      (show 0 ≤ 2 * tan φ by positivity)
    nlinarith [sq_nonneg (tan φ - 1 / 2)]
  · have hnegprod : -sin t * cos t ≤ 1 / 2 := by
      nlinarith [sin_sq_add_cos_sq t, sq_nonneg (sin t + cos t)]
    linarith

/-- A purely rational upper bound for the explicit cap constant in the source box. -/
theorem cap_constant_lt_2002 {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04) :
    2 / cos φ ≤ 2500 / 1249 ∧ 2 / cos φ < 1001 / 500 := by
  have hc0 := one_sub_sq_div_two_le_cos (x := φ)
  have hclower : (1249 / 1250 : ℝ) ≤ cos φ := by nlinarith [hφ.1, hφ.2]
  have hc : 0 < cos φ := by linarith
  have hbound : 2 / cos φ ≤ (2500 / 1249 : ℝ) := by
    apply (div_le_iff₀ hc).2
    nlinarith
  refine ⟨hbound, hbound.trans_lt ?_⟩
  norm_num

/-- Convert a verified squared evaluation bound to the explicit cap scale.
The analytic premise is kept visible until the kernel integrals are identified. -/
theorem green_evaluation_from_squared {φ value E : ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4))
    (he : value ^ 2 ≤ 4 * (1 / cos φ) ^ 2 * E) :
    |value| ≤ (2 / cos φ) * sqrt E := by
  have hc : 0 < cos φ := (cap_angle_parameters hφ).1
  apply abs_le_mul_sqrt_of_sq_le (show 0 ≤ 2 / cos φ by positivity)
  convert he using 1
  ring

end MovingSofaStability

end GreenNorm

/-!
## Quadratic control of linear residual functionals

Combining independent residual intervals adds the squared kernel norms, rather
than adding their square roots. This is the Cauchy--Schwarz step lost in the
earlier coefficient-80 proof.
-/

section SharpIntegralControl

open Real Set MeasureTheory

namespace MovingSofaStability

/-- A scalar evaluation with kernel square norm k and residual square norm e. -/
structure SquareControl (value k e : ℝ) : Prop where
  kernel_nonneg : 0 ≤ k
  energy_nonneg : 0 ≤ e
  bound : value ^ 2 ≤ k * e

theorem SquareControl.zero {e : ℝ} (he : 0 ≤ e) : SquareControl 0 0 e :=
  ⟨le_rfl, he, by simp⟩

theorem SquareControl.abs_bound {v k e : ℝ} (h : SquareControl v k e) :
    |v| ≤ sqrt k * sqrt e := by
  have hs := sqrt_le_sqrt h.bound
  simpa only [sqrt_sq_eq_abs, sqrt_mul h.kernel_nonneg] using hs

/-- Independent square norms add without a factor of two. -/
theorem SquareControl.add {v w k l e f : ℝ}
    (h : SquareControl v k e) (h' : SquareControl w l f) :
    SquareControl (v + w) (k + l) (e + f) := by
  refine ⟨add_nonneg h.kernel_nonneg h'.kernel_nonneg,
    add_nonneg h.energy_nonneg h'.energy_nonneg, ?_⟩
  have hc := four_term_sq_le (sqrt k) (sqrt l) 0 0 (sqrt e) (sqrt f) 0 0
  simp only [sq_sqrt h.kernel_nonneg, sq_sqrt h'.kernel_nonneg,
    sq_sqrt h.energy_nonneg, sq_sqrt h'.energy_nonneg,
    zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hc
  have hv := (abs_add_le v w).trans (add_le_add h.abs_bound h'.abs_bound)
  have hn : 0 ≤ sqrt k * sqrt e + sqrt l * sqrt f := by positivity
  nlinarith [abs_nonneg (v + w), sq_abs (v + w)]

theorem SquareControl.smul {v k e : ℝ} (h : SquareControl v k e) (a : ℝ) :
    SquareControl (a * v) (a ^ 2 * k) e := by
  refine ⟨mul_nonneg (sq_nonneg a) h.kernel_nonneg, h.energy_nonneg, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left h.bound (sq_nonneg a)
  nlinarith

theorem SquareControl.mono_energy {v k e E : ℝ} (h : SquareControl v k e)
    (he : e ≤ E) : SquareControl v k E :=
  ⟨h.kernel_nonneg, h.energy_nonneg.trans he,
    h.bound.trans (mul_le_mul_of_nonneg_left he h.kernel_nonneg)⟩

theorem SquareControl.mono_kernel {v k K e : ℝ} (h : SquareControl v k e)
    (hk : k ≤ K) : SquareControl v K e :=
  ⟨h.kernel_nonneg.trans hk, h.energy_nonneg,
    h.bound.trans (mul_le_mul_of_nonneg_right hk h.energy_nonneg)⟩

/-- The actual weighted integral has its actual squared kernel norm. -/
theorem integral_square_control {a b : ℝ} (hab : a ≤ b) {k r : ℝ → ℝ}
    (hk : ContinuousOn k (Icc a b))
    (hr : IntervalIntegrable r volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b) :
    SquareControl (∫ t in a..b, k t * r t)
      (∫ t in a..b, k t ^ 2) (arcSquare a b r) := by
  have hk2 : IntervalIntegrable (fun t => k t ^ 2) volume a b :=
    (hk.pow 2).intervalIntegrable_of_Icc hab
  have hkr : IntervalIntegrable (fun t => k t * r t) volume a b :=
    hr.continuousOn_mul (by rwa [uIcc_of_le hab])
  have ki := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hk2
  have ri := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hr2
  have kri := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hkr
  refine ⟨intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg (k t)),
    arcSquare_nonneg hab r, ?_⟩
  unfold arcSquare
  simp only [intervalIntegral.integral_of_le hab]
  exact integral_mul_sq_le (volume.restrict (Ioc a b)) ki ri kri

/-- The energy over a subinterval is bounded by the full arc energy. -/
theorem arcSquare_mono {a b c d : ℝ} {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) : arcSquare c d r ≤ arcSquare a b r := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  have haci := intervalIntegrable_subinterval hr2 le_rfl hac (hcd.trans hdb)
  have hcdi := intervalIntegrable_subinterval hr2 hac hcd hdb
  have hdbi := intervalIntegrable_subinterval hr2 (hac.trans hcd) hdb le_rfl
  have hsum : arcSquare a b r = arcSquare a c r + arcSquare c d r + arcSquare d b r := by
    unfold arcSquare
    rw [intervalIntegral.integral_add_adjacent_intervals haci hcdi,
      intervalIntegral.integral_add_adjacent_intervals (haci.trans hcdi) hdbi]
  rw [hsum]
  linarith [arcSquare_nonneg hac r, arcSquare_nonneg hdb r]

/-- Split energy at an interior point without counting the same residual twice. -/
theorem arcSquare_split {a b c : ℝ} {r : ℝ → ℝ}
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b)
    (hac : a ≤ c) (hcb : c ≤ b) :
    arcSquare a c r + arcSquare c b r = arcSquare a b r := by
  unfold arcSquare
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_subinterval hr2 le_rfl hac hcb)
    (intervalIntegrable_subinterval hr2 hac hcb le_rfl)

/-- The unweighted evaluation is useful on the middle residual interval. -/
theorem integral_unit_square_control {a b : ℝ} (hab : a ≤ b) {r : ℝ → ℝ}
    (hr : IntervalIntegrable r volume a b)
    (hr2 : IntervalIntegrable (fun t => r t ^ 2) volume a b) :
    SquareControl (∫ t in a..b, r t) (b - a) (arcSquare a b r) := by
  have h := integral_square_control hab (k := fun _ => 1) continuousOn_const hr hr2
  simpa using h

end MovingSofaStability

end SharpIntegralControl

/-!
## Exact square integrals of the trigonometric evaluation kernels

All integrations take place on compact intervals where the displayed
denominators are nonzero. No improper integral is silently used at pi; that
endpoint is handled separately by the pinned support value.
-/

section TrigKernelIntegrals

open Real Set MeasureTheory

namespace MovingSofaStability

def cotangent (u : ℝ) : ℝ := cos u / sin u

def tailKernel (A u : ℝ) : ℝ := (A + cos u) / sin u

def tailKernelPrimitive (A u : ℝ) : ℝ :=
  -(A ^ 2 + 1) * cotangent u - 2 * A * (1 / sin u) - u

theorem hasDerivAt_cotangent {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt cotangent (-(1 / sin u) ^ 2) u := by
  convert (hasDerivAt_cos u).div (hasDerivAt_sin u) hs using 1
  · rfl
  · field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem hasDerivAt_cosecant {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (fun u => 1 / sin u) (-cos u / sin u ^ 2) u := by
  convert (hasDerivAt_const u (1 : ℝ)).div (hasDerivAt_sin u) hs using 1
  ring

theorem hasDerivAt_tailKernel (A : ℝ) {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (tailKernel A) (-(1 + A * cos u) / sin u ^ 2) u := by
  convert ((hasDerivAt_cos u).const_add A).div (hasDerivAt_sin u) hs using 1
  · rfl
  · field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem hasDerivAt_tailKernelPrimitive (A : ℝ) {u : ℝ} (hs : sin u ≠ 0) :
    HasDerivAt (tailKernelPrimitive A) (tailKernel A u ^ 2) u := by
  have hd := (((hasDerivAt_cotangent hs).const_mul (-(A ^ 2 + 1))).sub
    ((hasDerivAt_cosecant hs).const_mul (2 * A))).sub (hasDerivAt_id u)
  convert hd using 1
  · rfl
  · unfold tailKernel
    field_simp [hs]
    nlinarith [sin_sq_add_cos_sq u]

theorem cosecant_sq_integral {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, (1 / sin u) ^ 2) = cotangent a - cotangent b := by
  have hi : IntervalIntegrable (fun u => (1 / sin u) ^ 2) volume a b :=
    ((continuousOn_const.div continuous_sin.continuousOn hs).pow 2).intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => -cotangent u) (f' := fun u => (1 / sin u) ^ 2)
    (fun u hu => by
      rw [uIcc_of_le hab] at hu
      have hd := (hasDerivAt_cotangent (hs u hu)).neg
      rw [neg_neg] at hd
      exact hd) hi
  linarith

theorem secant_sq_integral {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ u ∈ Icc a b, cos u ≠ 0) :
    (∫ u in a..b, (1 / cos u) ^ 2) = tan b - tan a := by
  have hi : IntervalIntegrable (fun u => (1 / cos u) ^ 2) volume a b :=
    ((continuousOn_const.div continuous_cos.continuousOn hc).pow 2).intervalIntegrable_of_Icc hab
  have hd : ∀ u ∈ Icc a b, HasDerivAt tan ((1 / cos u) ^ 2) u := by
    intro u hu
    convert (hasDerivAt_sin u).div (hasDerivAt_cos u) (hc u hu) using 1
    · exact funext fun x => tan_eq_sin_div_cos x
    · field_simp [hc u hu]
      nlinarith [sin_sq_add_cos_sq u]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by simpa only [uIcc_of_le hab] using hu)) hi

theorem shifted_cosecant_sq_integral {a b T : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin (T - u) ≠ 0) :
    (∫ u in a..b, (1 / sin (T - u)) ^ 2) = cotangent (T - b) - cotangent (T - a) := by
  have hsin : ContinuousOn (fun u => sin (T - u)) (Icc a b) := by fun_prop
  have hi : IntervalIntegrable (fun u => (1 / sin (T - u)) ^ 2) volume a b :=
    ((continuousOn_const.div hsin hs).pow 2).intervalIntegrable_of_Icc hab
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro u hu
  rw [uIcc_of_le hab] at hu
  convert (hasDerivAt_cotangent (hs u hu)).comp u ((hasDerivAt_id u).const_sub T) using 1
  · rfl
  · ring

theorem tailKernel_sq_integral (A : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ u ∈ Icc a b, sin u ≠ 0) :
    (∫ u in a..b, tailKernel A u ^ 2) = tailKernelPrimitive A b - tailKernelPrimitive A a := by
  have hk : ContinuousOn (tailKernel A) (Icc a b) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn hs
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_tailKernelPrimitive A (hs u (by simpa only [uIcc_of_le hab] using hu)))
    ((hk.pow 2).intervalIntegrable_of_Icc hab)

/-- The fourth-arc weight integrated only as far as the evaluation point. -/
theorem last_kernel_norm {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    sin t ^ 2 * (∫ u in (π / 2)..t, (1 / sin u) ^ 2) = -sin t * cos t := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  rw [cosecant_sq_integral ht.1 hs]
  simp only [cotangent, cos_pi_div_two, sin_pi_div_two, zero_div, zero_sub]
  field_simp [hs t ⟨ht.1, le_rfl⟩]

end MovingSofaStability

end TrigKernelIntegrals

/-!
## Exact four-arc reconstruction

The middle interval is coupled to the last interval. A product derivative
combines these contributions before estimating them. This avoids both Fubini and
the loss from estimating the two occurrences of f(T) separately.
-/

section SharpReconstruction

open Real Set MeasureTheory

namespace MovingSofaStability

section Reconstruction

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (h : FourResidualData φ f df)
-- The statements below do not mention these hypotheses, so each theorem includes the ones
-- it uses explicitly.

include h in
theorem sharp_last_formula {t : ℝ} (ht : t ∈ Ico (π / 2) π) :
    f t = -sin t * (∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u) := by
  have hs : ∀ u ∈ Icc (π / 2) t, sin (π - u) ≠ 0 := by
    intro u hu
    rw [sin_pi_sub]
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt ht.2)).ne'
  have hr := intervalIntegrable_subinterval h.last le_rfl ht.1 ht.2.le
  have hi := residual_div_sin_integrable ht.1 hr hs
  have he := tangent_reconstruct_right ht.1 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans ht.2⟩) hs hi
  have hq : tangentQuotient π f (π / 2) = 0 := by
    simp [tangentQuotient, h.top_zero, h.left_zero]
  rw [h.left_zero, zero_mul, zero_add, hq, zero_sub, sin_pi_sub] at he
  have hI : (∫ u in (π / 2)..t, tangentResidual π f df u / sin (π - u)) =
      ∫ u in (π / 2)..t, (1 / sin u) * tangentResidual π f df u := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [sin_pi_sub]
    ring
  rw [hI] at he
  linear_combination he

include hφ h in
theorem sharp_third_formula {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    f t = -(cos t / cos φ) * f (π - φ) + sin (π - φ - t) *
      (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
  have hpi := pi_pos
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hc : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1, ht.1])).ne'
  have hr := intervalIntegrable_subinterval h.third ht.1 ht.2 le_rfl
  have hi := residual_div_sin_integrable ht.2 hr hs
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hs hi
  have hq : tangentQuotient (π - φ) f (π / 2) = -f (π - φ) * sin φ / cos φ := by
    simp only [tangentQuotient, h.top_zero, zero_sub,
      show π - φ - π / 2 = π / 2 - φ by ring, cos_pi_div_two_sub, sin_pi_div_two_sub]
    ring
  have hcoef : cos (π - φ - t) - sin (π - φ - t) * (sin φ / cos φ) = -cos t / cos φ := by
    have hh : cos (π - φ - t) * cos φ - sin (π - φ - t) * sin φ = -cos t := by
      rw [← cos_add, show π - φ - t + φ = π - t by ring, cos_pi_sub]
    field_simp [hc]
    linear_combination hh
  have hI : (∫ u in t..(π / 2), tangentResidual (π - φ) f df u / sin (π - φ - u)) =
      ∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u := by
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [hq, hI] at he
  calc
    f t = f (π - φ) * (cos (π - φ - t) - sin (π - φ - t) * (sin φ / cos φ)) +
        sin (π - φ - t) *
          (∫ u in t..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) := by
      rw [he]
      ring
    _ = _ := by rw [hcoef]; ring

include hφ h in
theorem sharp_first_formula {t : ℝ} (ht : t ∈ Icc 0 φ) :
    f t = cos t * ((1 / cos φ) * f φ +
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hs : ∀ u ∈ Icc t φ, sin (π / 2 - u) ≠ 0 := by
    intro u hu
    rw [sin_pi_div_two_sub]
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1, pi_pos], by linarith [hu.2, pi_pos]⟩).ne'
  have hr := intervalIntegrable_subinterval h.first ht.1 ht.2 le_rfl
  have he := tangent_reconstruct_left ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2, pi_pos]⟩)
    hs (residual_div_sin_integrable ht.2 hr hs)
  simp only [tangentQuotient, h.top_zero, zero_mul, zero_add, sub_zero, sin_pi_div_two_sub] at he
  have hI : (∫ u in t..φ, tangentResidual (π / 2) f df u / cos u) =
      ∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u := by
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [hI] at he
  rw [he]
  ring

include h in
/-- Product integration replaces a double integral. The reference endpoint
f(pi) is zero, so its tangent residual is cot(u)*f(u)-f'(u). -/
theorem tail_product_integral (A : ℝ) {a b : ℝ}
    (ha : π / 2 ≤ a) (hab : a ≤ b) (hb : b < π) :
    (∫ u in a..b, f u) = tailKernel A a * f a - tailKernel A b * f b -
      ∫ u in a..b, tailKernel A u * tangentResidual π f df u := by
  have hs : ∀ u ∈ Icc a b, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt hb)).ne'
  have hk : ContinuousOn (tailKernel A) (Icc a b) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn hs
  have hr := intervalIntegrable_subinterval h.last ha hab hb.le
  have hkr : IntervalIntegrable (fun u => tailKernel A u * tangentResidual π f df u) volume a b :=
    hr.continuousOn_mul (by simpa only [uIcc_of_le hab] using hk)
  have hf : IntervalIntegrable f volume a b := h.continuous.intervalIntegrable a b
  have hd : ∀ u ∈ Ioo a b, HasDerivWithinAt (fun u => tailKernel A u * f u)
      (-f u - tailKernel A u * tangentResidual π f df u) (Ioi u) u := by
    intro u hu
    have hsu := hs u ⟨hu.1.le, hu.2.le⟩
    have hdu := (hasDerivAt_tailKernel A hsu).hasDerivWithinAt.mul
      (h.rightDeriv u ⟨by linarith [hu.1, pi_pos], hu.2.trans hb⟩)
    convert hdu using 1
    rw [tangentResidual_left h.left_zero]
    unfold tailKernel
    field_simp [hsu]
    linear_combination -(f u) * sin_sq_add_cos_sq u
  have hfn : IntervalIntegrable (fun u => -f u) volume a b := hf.neg
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hk.mul h.continuous.continuousOn) hd (hfn.sub hkr)
  rw [intervalIntegral.integral_sub hfn hkr, intervalIntegral.integral_neg] at he
  simp only [Pi.mul_apply] at he
  linarith

include hφ h in
/-- The common r4 kernel is combined before taking any norm. -/
theorem sharp_middle_formula {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    f t = (∫ u in t..(π / 2 - φ), cornerResidual f df u) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u) +
      (1 / cos φ - sin t) * (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
      (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hcφ : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hp0 (by linarith)).ne'
  have hct : cos t ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩).ne'
  have hr := intervalIntegrable_subinterval h.middle ht.1 ht.2 le_rfl
  have hshift : IntervalIntegrable (fun u => f (u + π / 2)) volume t (π / 2 - φ) :=
    (h.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hdf : IntervalIntegrable df volume t (π / 2 - φ) := by
    have he := hshift.sub hr
    simpa only [cornerResidual, sub_sub_cancel] using he
  have hrec := corner_reconstruct ht.2 h.continuous.continuousOn
    (fun u hu => h.rightDeriv u ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩) hdf hshift
  have hthird := sharp_third_formula hφ h (t := π / 2 - φ) ⟨le_rfl, by linarith⟩
  have hlast := sharp_last_formula h (t := π / 2 + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htail := tail_product_integral h (1 / cos φ)
    (a := π / 2 + t) (b := π - φ) (by linarith [ht.1]) (by linarith [ht.2]) (by linarith)
  have hT : tailKernel (1 / cos φ) (π - φ) = tan φ := by
    simp only [tailKernel, sin_pi_sub, cos_pi_sub, tan_eq_sin_div_cos]
    field_simp [hcφ, hsφ]
    nlinarith [sin_sq_add_cos_sq φ, congrArg (fun x : ℝ => cos φ * x) (sin_sq_add_cos_sq φ)]
  have hstart : tailKernel (1 / cos φ) (π / 2 + t) = (1 / cos φ - sin t) / cos t := by
    simp only [tailKernel, sin_add, cos_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul,
      add_zero, zero_sub]
    ring
  have hIshift : (∫ u in t..(π / 2 - φ), f (u + π / 2)) =
      ∫ u in (π / 2 + t)..(π - φ), f u := by
    rw [intervalIntegral.integral_comp_add_right f (π / 2)]
    congr 1 <;> ring
  simp only [show π - φ - (π / 2 - φ) = π / 2 by ring,
    sin_pi_div_two, cos_pi_div_two_sub, one_mul] at hthird
  simp only [sin_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul, add_zero] at hlast
  rw [hIshift, htail, hT, hstart, hthird, hlast] at hrec
  rw [tan_eq_sin_div_cos] at hrec
  rw [hrec]
  field_simp
  ring

end Reconstruction
end MovingSofaStability

end SharpReconstruction

/-!
## The actual kernel integrals equal the closed-form Green norms

These equalities connect the displayed Green formulas to integrals, rather than
merely bounding the formulas as independent scalars.
-/

section SharpKernelNorms

open Real Set MeasureTheory

namespace MovingSofaStability

private theorem reciprocal_endpoint_cancel (A c s : ℝ) (hs : s ≠ 0)
    (hAc : A * c = 1) (hunit : s ^ 2 + c ^ 2 = 1) :
    A * s + (A ^ 2 + 1) * (c / s) - 2 * A / s = 0 := by
  field_simp [hs]
  linear_combination A * hunit + (A - c) * hAc

private theorem middle_variable_cancel (A c s : ℝ) (hc : c ≠ 0)
    (hunit : s ^ 2 + c ^ 2 = 1) :
    ((A - s) ^ 2 - (A ^ 2 + 1)) * (s / c) + 2 * A / c = c * (2 * A - s) := by
  field_simp [hc]
  linear_combination (s - 2 * A) * hunit

/-- Norm of the r3 kernel on its whole arc. -/
theorem third_full_kernel_norm {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) = tan φ := by
  have hs : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2, hφ.2, pi_pos])
      (by linarith [hu.1, hφ.1, pi_pos])).ne'
  rw [shifted_cosecant_sq_integral (by linarith [hφ.1]) hs]
  simp only [cotangent, show π - φ - π / 2 = π / 2 - φ by ring,
    show π - φ - (π / 2 - φ) = π / 2 by ring,
    cos_pi_div_two_sub, sin_pi_div_two_sub, cos_pi_div_two, sin_pi_div_two,
    zero_div, sub_zero, tan_eq_sin_div_cos]

/-- The third-arc evaluation includes a last-arc component, and their squared
norms add before estimating f. -/
theorem third_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    (-(cos t / cos φ)) ^ 2 * (-sin (π - φ) * cos (π - φ)) +
      sin (π - φ - t) ^ 2 *
        (∫ u in t..(π / 2), (1 / sin (π - φ - u)) ^ 2) =
      sin t * cos t + 2 * tan φ * cos t ^ 2 := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hc : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1, ht.1])).ne'
  have hst := hs t ⟨le_rfl, ht.2⟩
  have hscale : (-(cos t / cos φ)) ^ 2 * (-sin (π - φ) * cos (π - φ)) =
      tan φ * cos t ^ 2 := by
    rw [sin_pi_sub, cos_pi_sub, tan_eq_sin_div_cos]
    field_simp [hc]
  rw [hscale, shifted_cosecant_sq_integral ht.2 hs]
  have hcot : cotangent (π - φ - π / 2) = tan φ := by
    simp only [cotangent, show π - φ - π / 2 = π / 2 - φ by ring,
      cos_pi_div_two_sub, sin_pi_div_two_sub, tan_eq_sin_div_cos]
  rw [hcot]
  have hcancel : sin (π - φ - t) ^ 2 * cotangent (π - φ - t) =
      sin (π - φ - t) * cos (π - φ - t) := by
    unfold cotangent
    field_simp [hst]
  rw [mul_sub, hcancel]
  rw [show π - φ - t = π - (φ + t) by ring, sin_pi_sub, cos_pi_sub,
    sin_add, cos_add, tan_eq_sin_div_cos]
  field_simp [hc]
  linear_combination (cos t * (cos φ * sin t + cos t * sin φ)) * sin_sq_add_cos_sq φ

/-- The middle-arc kernel has two disjoint pieces on the last residual arc. -/
theorem middle_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc φ (π / 2 - φ)) :
    (π / 2 - φ - t) +
      (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) ^ 2) +
      ((1 / cos φ - sin t) ^ 2 *
        (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) ^ 2) +
        (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u ^ 2)) =
      cos t * (2 / cos φ - sin t) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hcφ : cos φ ≠ 0 := (cap_angle_parameters hφ).1.ne'
  have hsφ : sin φ ≠ 0 := (sin_pos_of_pos_of_lt_pi hp0 (by linarith)).ne'
  have hct : cos t ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩).ne'
  have hs : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hsin1 : ∀ u ∈ Icc (π / 2) (π / 2 + t), sin u ≠ 0 :=
    fun u hu => hs u ⟨hu.1, by linarith [hu.2, ht.2]⟩
  have hsin2 : ∀ u ∈ Icc (π / 2 + t) (π - φ), sin u ≠ 0 :=
    fun u hu => hs u ⟨by linarith [hu.1, ht.1], hu.2⟩
  rw [third_full_kernel_norm hφ,
    cosecant_sq_integral (by linarith [ht.1]) hsin1,
    tailKernel_sq_integral (1 / cos φ) (by linarith [ht.2]) hsin2]
  let A := 1 / cos φ
  have hAc : A * cos φ = 1 := by
    dsimp [A]
    field_simp [hcφ]
  have hbase := reciprocal_endpoint_cancel A (cos φ) (sin φ) hsφ hAc (sin_sq_add_cos_sq φ)
  have hvar := middle_variable_cancel A (cos t) (sin t) hct (sin_sq_add_cos_sq t)
  change (π / 2 - φ - t) + tan φ +
    ((A - sin t) ^ 2 * (cotangent (π / 2) - cotangent (π / 2 + t)) +
      (tailKernelPrimitive A (π - φ) - tailKernelPrimitive A (π / 2 + t))) = _
  simp only [tailKernelPrimitive, cotangent, sin_pi_sub, cos_pi_sub,
    sin_add, cos_add, sin_pi_div_two, cos_pi_div_two,
    one_mul, zero_mul, add_zero, zero_div, zero_sub,
    tan_eq_sin_div_cos]
  have htan : sin φ / cos φ = A * sin φ := by dsimp [A]; ring
  have htwo : 2 / cos φ = 2 * A := by dsimp [A]; ring
  rw [htan, htwo]
  linear_combination hbase + hvar

/-- On the first arc the middle evaluation at phi has disjoint energy from r1. -/
theorem first_evaluation_norm {φ t : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (ht : t ∈ Icc 0 φ) :
    (cos t / cos φ) ^ 2 * (cos φ * (2 / cos φ - sin φ)) +
      cos t ^ 2 * (∫ u in t..φ, (1 / cos u) ^ 2) =
      cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t) := by
  have hcφ := (cap_angle_parameters hφ).1.ne'
  have hc : ∀ u ∈ Icc t φ, cos u ≠ 0 := by
    intro u hu
    exact (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1, pi_pos],
      by linarith [hu.2, hφ.2, pi_pos]⟩).ne'
  rw [secant_sq_integral ht.2 hc, tan_eq_sin_div_cos φ]
  field_simp [hcφ]
  ring

end MovingSofaStability

end SharpKernelNorms

/-!
## Sharp evaluation of the four residuals

Kernel norms and residual energies are kept separate. The two pieces of r4 on
the middle arc are recombined using their disjoint integration intervals, so the
same energy is not counted twice.
-/

section SharpEvaluation

open Real Set MeasureTheory

namespace MovingSofaStability

section Evaluation

variable {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
variable {f df : ℝ → ℝ} (H : FourResidualData φ f df)
-- The statements below do not mention these hypotheses, so each theorem includes the ones
-- it uses explicitly.

include H in
theorem sharp_last_control {t : ℝ} (ht : t ∈ Icc (π / 2) π) :
    SquareControl (f t) (-sin t * cos t) (arcSquare (π / 2) π (tangentResidual π f df)) := by
  by_cases htπ : t = π
  · simpa only [htπ, H.left_zero, sin_pi, neg_zero, zero_mul] using
      SquareControl.zero
        (arcSquare_nonneg (by linarith [pi_pos] : π / 2 ≤ π) (tangentResidual π f df))
  have htt : t ∈ Ico (π / 2) π := ⟨ht.1, lt_of_le_of_ne ht.2 htπ⟩
  have hs : ∀ u ∈ Icc (π / 2) t, sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1, pi_pos]) (hu.2.trans_lt htt.2)).ne'
  have hk : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) t) :=
    continuousOn_const.div continuous_sin.continuousOn hs
  have hI := (integral_square_control ht.1 hk
    (intervalIntegrable_subinterval H.last le_rfl ht.1 ht.2)
    (intervalIntegrable_subinterval H.last_sq le_rfl ht.1 ht.2)).smul (-sin t)
  have hn : (-sin t) ^ 2 * (∫ u in (π / 2)..t, (1 / sin u) ^ 2) = -sin t * cos t := by
    simpa only [neg_sq] using last_kernel_norm htt
  rw [← sharp_last_formula H htt, hn] at hI
  exact hI.mono_energy (arcSquare_mono H.last_sq le_rfl ht.1 ht.2)

include hφ H in
theorem sharp_third_control {t : ℝ} (ht : t ∈ Icc (π / 2 - φ) (π / 2)) :
    SquareControl (f t) (sin t * cos t + 2 * tan φ * cos t ^ 2)
      (arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hs : ∀ u ∈ Icc t (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1, ht.1])).ne'
  have hk : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc t (π / 2)) :=
    continuousOn_const.div (by fun_prop) hs
  have hI := (integral_square_control ht.2 hk
    (intervalIntegrable_subinterval H.third ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.third_sq ht.1 ht.2 le_rfl)).smul (sin (π - φ - t))
  have hT := (sharp_last_control H (t := π - φ)
    ⟨by linarith, by linarith⟩).smul (-(cos t / cos φ))
  have he := hT.add hI
  rw [← sharp_third_formula hφ H ht, third_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have hsub := arcSquare_mono H.third_sq ht.1 ht.2 le_rfl
  linarith

include hφ H in
theorem sharp_middle_control {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    SquareControl (f t) (cos t * (2 / cos φ - sin t))
      (arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df)) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hb : π / 2 - φ ≤ π / 2 := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hT : π - φ ≤ π := by linarith
  have hvT : π / 2 ≤ π - φ := by linarith
  have hvt : π / 2 ≤ π / 2 + t := by linarith
  have hvtT : π / 2 + t ≤ π - φ := by linarith [ht.2]
  have hs3 : ∀ u ∈ Icc (π / 2 - φ) (π / 2), sin (π - φ - u) ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.2]) (by linarith [hu.1])).ne'
  have hs4 : ∀ u ∈ Icc (π / 2) (π - φ), sin u ≠ 0 := by
    intro u hu
    exact (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])).ne'
  have hk3 : ContinuousOn (fun u => 1 / sin (π - φ - u)) (Icc (π / 2 - φ) (π / 2)) :=
    continuousOn_const.div (by fun_prop) hs3
  have hk4L : ContinuousOn (fun u => 1 / sin u) (Icc (π / 2) (π / 2 + t)) :=
    continuousOn_const.div continuous_sin.continuousOn
      (fun u hu => hs4 u ⟨hu.1, hu.2.trans hvtT⟩)
  have hk4R : ContinuousOn (tailKernel (1 / cos φ)) (Icc (π / 2 + t) (π - φ)) :=
    (continuousOn_const.add continuous_cos.continuousOn).div continuous_sin.continuousOn
      (fun u hu => hs4 u ⟨hvt.trans hu.1, hu.2⟩)
  have c2 := integral_unit_square_control ht.2
    (intervalIntegrable_subinterval H.middle ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.middle_sq ht.1 ht.2 le_rfl)
  have c3 := integral_square_control hb hk3 H.third H.third_sq
  have c4L := (integral_square_control hvt hk4L
    (intervalIntegrable_subinterval H.last le_rfl hvt (hvtT.trans hT))
    (intervalIntegrable_subinterval H.last_sq le_rfl hvt (hvtT.trans hT))).smul (1 / cos φ - sin t)
  have c4R := integral_square_control hvtT hk4R
    (intervalIntegrable_subinterval H.last hvt hvtT hT)
    (intervalIntegrable_subinterval H.last_sq hvt hvtT hT)
  have c4 := c4L.add c4R
  rw [arcSquare_split (intervalIntegrable_subinterval H.last_sq le_rfl hvT hT) hvt hvtT] at c4
  have he := (c2.add c3).add c4
  have hrec := sharp_middle_formula hφ H ht
  have hvalue : f t =
      ((∫ u in t..(π / 2 - φ), cornerResidual f df u) +
        (∫ u in (π / 2 - φ)..(π / 2), (1 / sin (π - φ - u)) * tangentResidual (π - φ) f df u)) +
      ((1 / cos φ - sin t) *
        (∫ u in (π / 2)..(π / 2 + t), (1 / sin u) * tangentResidual π f df u) +
        (∫ u in (π / 2 + t)..(π - φ), tailKernel (1 / cos φ) u * tangentResidual π f df u)) := by
    rw [hrec]
    ring
  rw [← hvalue, middle_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have h2 := arcSquare_mono H.middle_sq ht.1 ht.2 le_rfl
  have h4 := arcSquare_mono H.last_sq le_rfl hvT hT
  linarith

include hφ H in
theorem sharp_first_control {t : ℝ} (ht : t ∈ Icc 0 φ) :
    SquareControl (f t) (cos t ^ 2 * (2 * (1 / cos φ) ^ 2 - tan t))
      (2 * fourResidualEnergy φ f df) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have hmid := (sharp_middle_control hφ H (t := φ) ⟨le_rfl, by linarith⟩).smul (cos t / cos φ)
  have hk : ContinuousOn (fun u => 1 / cos u) (Icc t φ) :=
    continuousOn_const.div continuous_cos.continuousOn (fun u hu =>
      (cos_pos_of_mem_Ioo ⟨by linarith [hu.1, ht.1], by linarith [hu.2]⟩).ne')
  have hI := (integral_square_control ht.2 hk
    (intervalIntegrable_subinterval H.first ht.1 ht.2 le_rfl)
    (intervalIntegrable_subinterval H.first_sq ht.1 ht.2 le_rfl)).smul (cos t)
  have he := hmid.add hI
  have hvalue : f t = (cos t / cos φ) * f φ + cos t *
      (∫ u in t..φ, (1 / cos u) * tangentResidual (π / 2) f df u) := by
    rw [sharp_first_formula hφ H ht]
    ring
  rw [← hvalue, first_evaluation_norm hφ ht] at he
  apply he.mono_energy
  have hsub := arcSquare_mono H.first_sq ht.1 ht.2 le_rfl
  unfold fourResidualEnergy
  linarith

include hφ H in
/-- The actual square-integral norm at every evaluation point. -/
theorem sharp_green_control {t : ℝ} (ht : t ∈ Icc 0 π) :
    SquareControl (f t) (greenNormSquared φ t) (2 * fourResidualEnergy φ f df) := by
  have hp0 := hφ.1
  have hp4 := hφ.2
  have hpi := pi_pos
  have e1 := arcSquare_nonneg hp0.le (tangentResidual (π / 2) f df)
  have e2 := arcSquare_nonneg (by linarith : φ ≤ π / 2 - φ) (cornerResidual f df)
  have e3 := arcSquare_nonneg (by linarith : π / 2 - φ ≤ π / 2) (tangentResidual (π - φ) f df)
  have e4 := arcSquare_nonneg (by linarith : π / 2 ≤ π) (tangentResidual π f df)
  by_cases h1 : t ≤ φ
  · simpa only [greenNormSquared, ite_eq_left h1] using sharp_first_control hφ H ⟨ht.1, h1⟩
  by_cases h2 : t ≤ π / 2 - φ
  · have hc := sharp_middle_control hφ H ⟨(not_le.mp h1).le, h2⟩
    have henergy : arcSquare φ (π / 2 - φ) (cornerResidual f df) +
        arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_left h2] using hc.mono_energy henergy
  by_cases h3 : t ≤ π / 2
  · have hc := sharp_third_control hφ H ⟨(not_le.mp h2).le, h3⟩
    have henergy : arcSquare (π / 2 - φ) (π / 2) (tangentResidual (π - φ) f df) +
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] using
      hc.mono_energy henergy
  · have hc := sharp_last_control H ⟨(not_le.mp h3).le, ht.2⟩
    have henergy :
        arcSquare (π / 2) π (tangentResidual π f df) ≤ 2 * fourResidualEnergy φ f df := by
      unfold fourResidualEnergy
      linarith
    simpa only [greenNormSquared, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] using
      hc.mono_energy henergy

include hφ H in
/-- The coefficient is 2/cos(phi), not the earlier non-sharp 80. -/
theorem sharp_four_arc_coercivity {t : ℝ} (ht : t ∈ Icc 0 π) :
    |f t| ≤ (2 / cos φ) * sqrt (fourResidualEnergy φ f df) := by
  have hc := (sharp_green_control hφ H ht).mono_kernel (greenNormSquared_le hφ ht)
  apply green_evaluation_from_squared hφ
  nlinarith only [hc.bound]

end Evaluation
end MovingSofaStability

end SharpEvaluation

/-!
## The improved Euclidean cap-distance certificate

The actual Mamikon residuals satisfy the analytic hypotheses, and their square
integrals are identified before applying the sharp four-arc estimate. No
kernel-reconstruction premise remains in these theorems.

The old coefficient-80 declarations remain for compatibility. These stronger
entry points have the same domains and the same pinned horizontal translation.
The coefficient is not asserted optimal over feasible caps or free translations.
-/

section SharpCapDistance

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The improved residual estimate for any two normalized, possibly nonsmooth caps. -/
theorem sharp_capDifference_le_energy {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (h₀ : IsCap K₀.1 (π / 2)) (h₁ : IsCap K₁.1 (π / 2))
    {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference K₀.1 K₁.1 t| ≤ (2 / cos φ) * sqrt (capResidualEnergy φ K₀ K₁) := by
  have he := sharp_four_arc_coercivity hφ (capDifference_data hφ K₀ K₁ h₀ h₁) ht
  rwa [fourResidualEnergy_eq_capEnergy hφ K₀ K₁] at he

/-- The original Q deficit controls the cap with coefficient 2 sec(phi). -/
theorem sharp_wide_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap x.1.1.1 t| ≤
      (2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x) := by
  have hφ := GerverParams.gm_φ_mem_Ioo hP hbox
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num) (cap_angle_parameters hφ).1.le
  have he := sharp_capDifference_le_energy hφ (wideGerverTriple hP hbox).1.1 x.1.1
    (wideGerverTriple hP hbox).2.1 x.2.1 ht
  exact he.trans (mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (wide_capResidualEnergy_le_deficit hP hbox x)) hc)

/-- The sharper sofa-area-deficit estimate on the original injective class. -/
theorem sharp_ki_cap_support_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) {t : ℝ} (ht : t ∈ Icc 0 π) :
    |capDifference P.cap K t| ≤ (2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  have he := sharp_wide_cap_support_bound hP hbox (toWideTriple (kiExtensionTriple hbox.1 hK)) ht
  have hA := theorem8_2_4 hbox.1 hK
  have hdef : area (gerverSofa P) - wideUpperQ P.φ (toWideTriple (kiExtensionTriple hbox.1 hK)) ≤
      area (gerverSofa P) - sofaArea (π / 2) K := by
    change area (gerverSofa P) - upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) ≤ _
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hdef) hc)

/-- Actual Euclidean cap distance on the enlarged nonsmooth triple domain. -/
theorem sharp_wide_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 x.2.1
    (mul_nonneg hc (sqrt_nonneg _))
  intro t ht
  exact sharp_wide_cap_support_bound hP hbox x ht

/-- Actual Euclidean cap distance from the original sofa-area deficit. -/
theorem sharp_ki_cap_distance_bound {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) := by
  have hc : 0 ≤ 2 / cos P.φ := div_nonneg (by norm_num)
    (cap_angle_parameters (GerverParams.gm_φ_mem_Ioo hP hbox)).1.le
  apply cap_euclideanClose_of_upper_support (wideGerverTriple hP hbox).2.1 hK.1
    (mul_nonneg hc (sqrt_nonneg _))
  intro t ht
  exact sharp_ki_cap_support_bound hP hbox hK ht

/-- A rational coefficient, justified by inequalities rather than a decimal fit. -/
theorem wide_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
      x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  (sharp_wide_cap_distance_bound hP hbox x).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

theorem ki_cap_distance_bound_2002 {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Point} (hK : IsKi K) :
    EuclideanClose ((1001 / 500) * sqrt (area (gerverSofa P) - sofaArea (π / 2) K))
      K (shiftedReferenceCap P.cap K) :=
  (sharp_ki_cap_distance_bound hP hbox hK).mono
    (mul_le_mul_of_nonneg_right (cap_constant_lt_2002 hbox.1).2.le (sqrt_nonneg _))

end MovingSofaStability

end SharpCapDistance

/-!
## The coercive certificate

One estimate for Baek's upper bound `𝒬` on the enlarged domain of triples carries optimality,
uniqueness and stability. For every triple `x` of the enlarged domain, `𝒬(x) ≤ |G|`
(`wideUpperQ_le_gerver`, from the concavity of `𝒬` and its first variation at Gerver's triple),
and the cap of `x` lies within Euclidean Hausdorff distance `(2 / cos φ) √(|G| - 𝒬(x))` of
Gerver's cap, translated horizontally so that their leftmost points have the same abscissa
(`sharp_wide_cap_distance_bound`, from the residual energies of the deficit).

The first part bounds the value of a maximizing right-angle cap, which gives optimality
(`MovingSofaExtremal.gerver_sofa_optimal`). At zero deficit the second part says that such a cap
is a translate of Gerver's cap, which gives uniqueness
(`MovingSofaExtremal.image_eq_gerver_of_volume_eq`). At small deficit both parts give the local
estimate of the stability theorem (`nearby_cap_distance`, `unrestricted_stability`).
-/

section CoerciveCertificate

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- **The coercive certificate.** For every triple `x` of the enlarged domain, Baek's upper bound
satisfies `𝒬(x) ≤ |G|`, and the cap of `x` lies within Euclidean Hausdorff distance
`(2 / cos φ) √(|G| - 𝒬(x))` of Gerver's cap translated horizontally. -/
theorem coercive_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ area (gerverSofa P) ∧
      EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
        x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  ⟨(wideUpperQ_le_gerver hP hbox x).trans_eq (wideGerver_value hP hbox),
    sharp_wide_cap_distance_bound hP hbox x⟩

end MovingSofaStability

end CoerciveCertificate
