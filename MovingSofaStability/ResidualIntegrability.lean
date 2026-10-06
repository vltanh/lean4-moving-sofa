module

public import MovingSofaStability.ODEReconstruction

/-!
# Integrability of the actual cap residuals

Mamikon's boundedness theorem supplies both first and second integrability.
Endpoint values of a tangent quotient are not identified with its geometric
displacement at a singular endpoint: the identification is made on the open
interval, then transferred across the two null singletons.
-/

@[expose] public section
noncomputable section

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
