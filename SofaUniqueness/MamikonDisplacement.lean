module

public import MovingSofa.Convex.Mamikon
public import SofaUniqueness.SquareGap
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Equality in Mamikon's formula identifies the displacement functions

The square-integrability hypotheses are proved from the bounded measurable
functions supplied by Theorem 7.4.1. Equality cannot arise from Lean's default
value for a nonintegrable integral. The result is first almost-everywhere
 equality and then pointwise equality on any interval where both displacements
are continuous.

Uncompiled source; no admitted statements.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter MovingSofa

namespace SofaUniqueness

/-- Signed tangent displacement from the positive endpoint of the support face. -/
def displacement (K : Set (ℝ × ℝ)) (z : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  dot (z t - vplus K t) (vvec t)

variable {a b : ℝ} (hab : a < b) (hb : b < a + π)
variable (z : ConvexBodySet → ℝ → ℝ × ℝ)
variable (hz : ∀ K, IsCBV (z K) a b)
variable (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)

include hab hb hz hzl in
/-- Products of two tangent displacements are integrable on the interval. -/
theorem displacement_mul_integrable (K₀ K₁ : ConvexBodySet) :
    IntegrableOn (fun t => displacement K₀.1 (z K₀) t * displacement K₁.1 (z K₁) t)
      (Ioo a b) volume := by
  have hM := fun K : ConvexBodySet => theorem7_4_1 K.2 hab hb (hz K) (hzl K)
  obtain ⟨C₀, hC₀⟩ := (hM K₀).2.1
  obtain ⟨C₁, hC₁⟩ := (hM K₁).2.1
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ a ⟨le_rfl, hab.le⟩)
  have hI : IntegrableOn
      (fun t => displacement K₀.1 (z K₀) t * displacement K₁.1 (z K₁) t)
      (Icc a b) volume := by
    have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine Integrable.of_bound ((hM K₀).1.mul (hM K₁).1).aestronglyMeasurable
      (C₀ * C₁) ?_
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC₀ t ht) (hC₁ t ht) (abs_nonneg _) hC₀0
  exact hI.mono_set Ioo_subset_Icc_self

include hab hb hz hzl in
/-- Mamikon's area in the same restricted-measure form as `SquareGap`. -/
theorem mamikon_eq_halfSquareIntegral (K : ConvexBodySet) :
    mamikon K.1 a b (z K) =
      halfSquareIntegral (volume.restrict (Ioo a b)) (displacement K.1 (z K)) := by
  rw [(theorem7_4_1 K.2 hab hb (hz K) (hzl K)).2.2.2,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rfl

variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)

include hlin in
/-- The signed displacement is affine in the convex body. -/
theorem displacement_combo (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc a b) :
    displacement (convexBodyComb c K₀ K₁).1 (z (convexBodyComb c K₀ K₁)) t =
      (1 - c) * displacement K₀.1 (z K₀) t + c * displacement K₁.1 (z K₁) t := by
  unfold displacement
  rw [hlin K₀ K₁ c hc t ht, cvx_vplus_comb hc K₀ K₁ t]
  simp only [dot_sub_left, dot_add_left, dot_smul_left]
  ring

include hab hb hz hzl hlin in
/-- Equality in a nontrivial Mamikon convexity inequality gives a.e. equality
of the underlying displacement functions. -/
theorem displacement_ae_eq_of_mamikon_eq (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁)) :
    displacement K₀.1 (z K₀) =ᵐ[volume.restrict (Ioo a b)] displacement K₁.1 (z K₁) := by
  let μ := volume.restrict (Ioo a b)
  let f := displacement K₀.1 (z K₀)
  let g := displacement K₁.1 (z K₁)
  have hfg : Integrable (fun t => f t * g t) μ :=
    displacement_mul_integrable hab hb z hz hzl K₀ K₁
  have hf : Integrable (fun t => f t ^ 2) μ :=
    Integrable.congr (displacement_mul_integrable hab hb z hz hzl K₀ K₀)
      (Eventually.of_forall fun t => (pow_two (f t)).symm)
  have hg : Integrable (fun t => g t ^ 2) μ :=
    Integrable.congr (displacement_mul_integrable hab hb z hz hzl K₁ K₁)
      (Eventually.of_forall fun t => (pow_two (g t)).symm)
  have hcombo : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      halfSquareIntegral μ (fun t => (1 - c) * f t + c * g t) := by
    rw [mamikon_eq_halfSquareIntegral hab hb z hz hzl]
    unfold halfSquareIntegral
    congr 1
    apply integral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    show displacement (convexBodyComb c K₀ K₁).1 (z (convexBodyComb c K₀ K₁)) t ^ 2 =
      ((1 - c) * f t + c * g t) ^ 2
    rw [displacement_combo z hlin K₀ K₁ ⟨hc.1.le, hc.2.le⟩ ⟨ht.1.le, ht.2.le⟩]
  rw [hcombo, mamikon_eq_halfSquareIntegral hab hb z hz hzl K₀,
    mamikon_eq_halfSquareIntegral hab hb z hz hzl K₁] at heq
  exact (halfSquareIntegral_combo_eq_iff μ hc hf hg hfg).mp heq

include hab hb hz hzl hlin in
/-- Continuity upgrades a.e. displacement equality on the open interval.
Endpoint values are not asserted; the later support argument uses continuity
of the support function itself at those endpoints. -/
theorem displacement_eqOn_of_mamikon_eq (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁))
    (hcont₀ : ContinuousOn (displacement K₀.1 (z K₀)) (Ioo a b))
    (hcont₁ : ContinuousOn (displacement K₁.1 (z K₁)) (Ioo a b)) :
    EqOn (displacement K₀.1 (z K₀)) (displacement K₁.1 (z K₁)) (Ioo a b) := by
  exact Measure.eqOn_Ioo_of_ae_eq (μ := volume)
    (displacement_ae_eq_of_mamikon_eq hab hb z hz hzl hlin K₀ K₁ hc heq)
    hcont₀ hcont₁

end SofaUniqueness
