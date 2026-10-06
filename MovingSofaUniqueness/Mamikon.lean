module

public import MovingSofaUniqueness.Rigid

/-!
# Square integrals and Mamikon displacements

Half square integrals and their gap under convex combinations (`halfSquareIntegral`,
`halfSquareIntegral_combo_gap`), the tangent displacements of a cap and Mamikon's area as their half
square integral (`displacement`, `mamikon_eq_halfSquareIntegral`), the displacements of the tangent
points and of the outer corner, and the canonical triple of a cap of `𝒦^i` with Baek's maximum of
`𝒬` at Gerver's triple (`kiExtensionTriple`, `upperQL_le_gerver`). The equality analysis of the
first proof of uniqueness (`MovingSofaUniqueness.Rigidity`), the coercive certificate and the
stability proof (`MovingSofaStability`) all use them.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter MovingSofaOptimality

namespace MovingSofaUniqueness

/-!
## The square gap

Mamikon's formula writes an area as `halfSquareIntegral μ f = (1/2) ∫ f²` for a tangent
displacement `f`. If `f ^ 2`, `g ^ 2` and `f * g` are integrable, the convexity gap of this
functional along `(1 - c) f + c g` is `c (1 - c) / 2 · ∫ (f - g)²` for every `c`
(`halfSquareIntegral_combo_gap`); at the midpoint the factor is `1/8`. So for `c ∈ (0, 1)` the gap
vanishes if and only if `f = g` almost everywhere (`halfSquareIntegral_combo_eq_iff`).
-/

section SquareGap

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

/-- Half the integral of `f ^ 2`, the form of Mamikon's area formula. -/
noncomputable def halfSquareIntegral (f : X → ℝ) : ℝ :=
  (1 / 2) * ∫ x, (f x) ^ 2 ∂μ

/-- If `f ^ 2`, `g ^ 2` and `f * g` are integrable, so is `(f - g) ^ 2`. -/
theorem integrable_sq_sub
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun x => (f x - g x) ^ 2) μ := by
  have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) μ :=
    (hf.add hg).sub (hfg.const_mul 2)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  ring

/-- The convexity gap of `halfSquareIntegral` at `c` is `c (1 - c) / 2 · ∫ (f - g)²`; at the
midpoint the factor is `1/8`. -/
theorem halfSquareIntegral_combo_gap (c : ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g -
        halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
      (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
  -- Pointwise, `((1 - c) f + c g)² = (1 - c) f² + c g² - c (1 - c) (f - g)²`.
  have hcombo : (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
      (1 - c) * (∫ x, (f x) ^ 2 ∂μ) + c * (∫ x, (g x) ^ 2 ∂μ) -
        c * (1 - c) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
    have h₁ : Integrable (fun x => (1 - c) * (f x) ^ 2 + c * (g x) ^ 2) μ :=
      (hf.const_mul _).add (hg.const_mul _)
    have h₂ : Integrable (fun x => c * (1 - c) * (f x - g x) ^ 2) μ :=
      (integrable_sq_sub μ hf hg hfg).const_mul _
    calc (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ)
        = ∫ x, ((1 - c) * (f x) ^ 2 + c * (g x) ^ 2) - c * (1 - c) * (f x - g x) ^ 2 ∂μ :=
          integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = _ := by
        rw [integral_sub h₁ h₂, integral_add (hf.const_mul _) (hg.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
  unfold halfSquareIntegral
  rw [hcombo]
  ring

/-- `∫ (f - g)² = 0` if and only if `f = g` almost everywhere. -/
theorem integral_sq_sub_eq_zero_iff
    (hint : Integrable (fun x => (f x - g x) ^ 2) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) = 0 ↔ f =ᵐ[μ] g := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x - g x)) hint]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · simpa [sub_eq_zero] using hx
  · simp [hx]

/-- For `c ∈ (0, 1)`, the convexity inequality of `halfSquareIntegral` is an equality if and only
if `f = g` almost everywhere. -/
theorem halfSquareIntegral_combo_eq_iff {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
        (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g ↔
      f =ᵐ[μ] g := by
  have hcoef : c * (1 - c) / 2 ≠ 0 := (div_pos (mul_pos hc.1 (sub_pos.2 hc.2)) two_pos).ne'
  rw [eq_comm, ← sub_eq_zero, halfSquareIntegral_combo_gap μ c hf hg hfg, mul_eq_zero,
    or_iff_right hcoef, integral_sq_sub_eq_zero_iff μ (integrable_sq_sub μ hf hg hfg)]

end SquareGap

/-!
## Mamikon's area as a square integral

For continuous supporting curves `z K` of bounded variation on `[a, b]`, Baek's Theorem 7.4.1
writes Mamikon's area as `halfSquareIntegral` of the bounded tangent displacement
`displacement K (z K)` (`mamikon_eq_halfSquareIntegral`). If `z` is affine under Minkowski
combinations, so is the displacement (`displacement_combo`).
-/

section Displacement

/-- The signed distance along the supporting line from the endpoint `vplus K t` of the support face
to `z t`. -/
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
  refine (IntegrableOn.of_bound measure_Icc_lt_top ((hM K₀).1.mul (hM K₁).1).aestronglyMeasurable
    (C₀ * C₁) (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_)).mono_set
    Ioo_subset_Icc_self
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul (hC₀ t ht) (hC₁ t ht) (abs_nonneg _) hC₀0

include hab hb hz hzl in
/-- Mamikon's area is `halfSquareIntegral` of the displacement (Baek's Theorem 7.4.1). -/
theorem mamikon_eq_halfSquareIntegral (K : ConvexBodySet) :
    mamikon K.1 a b (z K) =
      halfSquareIntegral (volume.restrict (Ioo a b)) (displacement K.1 (z K)) := by
  rw [(theorem7_4_1 K.2 hab hb (hz K) (hzl K)).2.2.2,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  rfl

variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)

include hlin in
/-- The displacement is affine under Minkowski combinations when `z` is. -/
theorem displacement_combo (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc a b) :
    displacement (convexBodyComb c K₀ K₁).1 (z (convexBodyComb c K₀ K₁)) t =
      (1 - c) * displacement K₀.1 (z K₀) t + c * displacement K₁.1 (z K₁) t := by
  unfold displacement
  rw [hlin K₀ K₁ c hc t ht, cvx_vplus_comb hc K₀ K₁ t]
  simp only [dot_sub_left, dot_add_left, dot_smul_left]
  ring

end Displacement

/-!
## The displacements of the tangent points and of the outer corner; the canonical triple
-/

/-- The displacement of the intersection with the supporting line at `T`. -/
theorem tangent_displacement_formula (K : Set (ℝ × ℝ)) {T t : ℝ} (ht : t < T) :
    displacement K (tangentParam K T) t =
      (supp K T - supp K t * cos (T - t)) / sin (T - t) -
        dot (vplus K t) (vvec t) := by
  simp only [displacement, tangentParam, ht, ite_true, vint, dot_sub_left,
    dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
    mul_zero, mul_one, zero_add]

/-- The displacement of the outer corner. -/
theorem outer_displacement_formula (K : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K (outerCorner K) t =
      supp K (t + π / 2) - dot (vplus K t) (vvec t) := by
  rw [displacement, dot_sub_left, inj_dot_outerCorner_vvec]

/-- Baek's Corollary 8.5.8: Gerver's triple maximizes `𝒬`. -/
theorem upperQL_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : LTriple P.φ) : upperQL P.φ x ≤ upperQL P.φ (gerverTriple hP hbox) :=
  corollary8_5_8 hP hbox x.2

/-- The canonical triple `(K, B_K, D_K)` in `𝓛` of a cap `K` in `𝒦^i` (Baek's Theorem 8.1.8). -/
noncomputable def kiExtensionTriple {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) : LTriple φ :=
  ⟨(⟨K, hK.1.2.1⟩, ⟨rightBody φ K, (theorem8_1_8 hφ hK).2.1⟩,
    ⟨leftBody φ K, (theorem8_1_8 hφ hK).2.2.1⟩), theorem8_1_8 hφ hK⟩

end MovingSofaUniqueness
