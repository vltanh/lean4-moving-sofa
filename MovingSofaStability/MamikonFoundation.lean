module

public import MovingSofaUniqueness.Rigid

/-!
# Neutral Mamikon infrastructure for the quantitative route

Uncompiled proof source. These elementary square-integral and displacement
lemmas use Baek's Mamikon formula, not the old equality/CapKernel argument.
The original MovingSofaUniqueness.Rigidity module is deliberately unchanged.
The quantitative route uses the declarations in MovingSofaStability below,
so it does not import the original rigidity module merely for its utilities.

The distinct namespace preserves coexistence with the old theorem family.
A later checked deduplication can turn the old utilities into compatibility
aliases, but no such change to the original proof is needed for this route.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter MovingSofaOptimality

namespace MovingSofaStability

section Square

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

def halfSquareIntegral (f : X → ℝ) : ℝ := (1 / 2) * ∫ x, f x ^ 2 ∂μ

theorem integrable_sq_sub
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun x => (f x - g x) ^ 2) μ := by
  have hsum : Integrable (fun x => f x ^ 2 + g x ^ 2 - 2 * (f x * g x)) μ :=
    (hf.add hg).sub (hfg.const_mul 2)
  exact hsum.congr (Eventually.of_forall fun x => by ring)

theorem halfSquareIntegral_combo_gap (c : ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g -
        halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
      (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
  have hcombo : (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
      (1 - c) * (∫ x, f x ^ 2 ∂μ) + c * (∫ x, g x ^ 2 ∂μ) -
        c * (1 - c) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
    have h₁ : Integrable (fun x => (1 - c) * f x ^ 2 + c * g x ^ 2) μ :=
      (hf.const_mul _).add (hg.const_mul _)
    have h₂ : Integrable (fun x => c * (1 - c) * (f x - g x) ^ 2) μ :=
      (integrable_sq_sub μ hf hg hfg).const_mul _
    calc
      _ = ∫ x, ((1 - c) * f x ^ 2 + c * g x ^ 2) - c * (1 - c) * (f x - g x) ^ 2 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = _ := by
        rw [integral_sub h₁ h₂, integral_add (hf.const_mul _) (hg.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
  unfold halfSquareIntegral
  rw [hcombo]
  ring

theorem integral_sq_sub_eq_zero_iff
    (hint : Integrable (fun x => (f x - g x) ^ 2) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) = 0 ↔ f =ᵐ[μ] g := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x - g x)) hint]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · simpa [sub_eq_zero] using hx
  · simp [hx]

end Square

/-- A signed tangent displacement, independent of any maximizer or equality claim. -/
def displacement (K : Set (ℝ × ℝ)) (z : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  dot (z t - vplus K t) (vvec t)

section Displacement

variable {a b : ℝ} (hab : a < b) (hb : b < a + π)
variable (z : ConvexBodySet → ℝ → ℝ × ℝ)
variable (hz : ∀ K, IsCBV (z K) a b)
variable (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)

include hab hb hz hzl in
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
    letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine Integrable.of_bound ((hM K₀).1.mul (hM K₁).1).aestronglyMeasurable (C₀ * C₁) ?_
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC₀ t ht) (hC₁ t ht) (abs_nonneg _) hC₀0
  exact hI.mono_set Ioo_subset_Icc_self

include hab hb hz hzl in
theorem mamikon_eq_halfSquareIntegral (K : ConvexBodySet) :
    mamikon K.1 a b (z K) =
      halfSquareIntegral (volume.restrict (Ioo a b)) (displacement K.1 (z K)) := by
  rw [(theorem7_4_1 K.2 hab hb (hz K) (hzl K)).2.2.2,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rfl

variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)

include hlin in
theorem displacement_combo (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc a b) :
    displacement (convexBodyComb c K₀ K₁).1 (z (convexBodyComb c K₀ K₁)) t =
      (1 - c) * displacement K₀.1 (z K₀) t + c * displacement K₁.1 (z K₁) t := by
  unfold displacement
  rw [hlin K₀ K₁ c hc t ht, cvx_vplus_comb hc K₀ K₁ t]
  simp only [dot_sub_left, dot_add_left, dot_smul_left]
  ring

end Displacement

theorem tangent_displacement_formula (K : Set (ℝ × ℝ)) {T t : ℝ} (ht : t < T) :
    displacement K (tangentParam K T) t =
      (supp K T - supp K t * cos (T - t)) / sin (T - t) - dot (vplus K t) (vvec t) := by
  simp only [displacement, tangentParam, ht, ite_true, vint, dot_sub_left,
    dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
    mul_zero, mul_one, zero_add]

theorem outer_displacement_formula (K : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K (outerCorner K) t = supp K (t + π / 2) - dot (vplus K t) (vvec t) := by
  rw [displacement, dot_sub_left, inj_dot_outerCorner_vvec]

/-- The canonical triple requires only Baek's injective-class construction. -/
def kiExtensionTriple {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) : LTriple φ :=
  ⟨(⟨K, hK.1.2.1⟩, ⟨rightBody φ K, (theorem8_1_8 hφ hK).2.1⟩,
    ⟨leftBody φ K, (theorem8_1_8 hφ hK).2.2.1⟩), theorem8_1_8 hφ hK⟩

/-- This is Baek's intermediate Q maximum, not his final sofa optimality theorem. -/
theorem upperQL_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : LTriple P.φ) : upperQL P.φ x ≤ upperQL P.φ (gerverTriple hP hbox) :=
  corollary8_5_8 hP hbox x.2

end MovingSofaStability
