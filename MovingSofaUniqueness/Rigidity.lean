module

public import MovingSofaUniqueness.Rigid

/-!
# Proposition 5: a maximizing cap with the injectivity condition is Gerver's cap

If a cap `K` in `𝒦^i` has the sofa area of Gerver's sofa, it attains the maximum of Baek's upper
bound `𝒬`, so the segment from Gerver's cap to `K` saturates each of Mamikon's convexity
inequalities (`ki_maximizer_equality_conditions`). Equality in Mamikon's formula makes the
difference of the support functions satisfy the tangent equations of a horizontal translation
(`capKernel_of_triple_midpoint`, `CapKernel.eq_horizontal_translation`), so `K` minus its niche
is a horizontal translate of Gerver's sofa (`sofa_eq_translate_of_upper_support`).
-/

@[expose] public section
noncomputable section

/-!
## The square gap

Mamikon's formula writes an area as `halfSquareIntegral μ f = (1/2) ∫ f²` for a tangent
displacement `f`. If `f ^ 2`, `g ^ 2` and `f * g` are integrable, the convexity gap of this
functional along `(1 - c) f + c g` is `c (1 - c) / 2 · ∫ (f - g)²` for every `c`
(`halfSquareIntegral_combo_gap`); at the midpoint the factor is `1/8`. So for `c ∈ (0, 1)` the gap
vanishes if and only if `f = g` almost everywhere (`halfSquareIntegral_combo_eq_iff`).
-/

section

open MeasureTheory Filter

namespace MovingSofaUniqueness

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
  have hcoef : c * (1 - c) / 2 ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hc.1 (sub_pos.mpr hc.2)) (by norm_num))
  have hint := integrable_sq_sub μ hf hg hfg
  constructor
  · intro heq
    have hz : (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) = 0 := by
      rw [← halfSquareIntegral_combo_gap μ c hf hg hfg, heq, sub_self]
    exact (integral_sq_sub_eq_zero_iff μ hint).mp
      ((mul_eq_zero.mp hz).resolve_left hcoef)
  · intro hae
    have hz := (integral_sq_sub_eq_zero_iff μ hint).mpr hae
    have hgap := halfSquareIntegral_combo_gap μ c hf hg hfg
    rw [hz, mul_zero] at hgap
    exact (sub_eq_zero.mp hgap).symm

end MovingSofaUniqueness

end

/-!
## The cap kernel is a horizontal translation

`CapKernel φ f` collects the equations that equality in the four Mamikon terms of a cap imposes on
the difference `f` of two support functions: `f(π/2) = 0`; on `[0, φ]`, `[π/2 - φ, π/2]` and
`[π/2, π]`, the solutions `p cos t + q sin t` of the tangent equations with targets `π/2`, `π - φ`
and `π`; and on `[φ, π/2 - φ]`, the integrated form of `f'(t) = f(t + π/2)`. Solving these in
reverse order, as in the proof of Proposition 5 of note 20, gives `f(t) = a cos t` on `[0, π]` with
`a = -f(π)` (`CapKernel.eq_horizontal_translation`).
-/

section

open Set Real MeasureTheory

namespace MovingSofaUniqueness

/-- `f(t) = p cos t + q sin t` on `[a, b]` and at the target `T`: the form of the solutions of the
tangent equation `sin (T - t) f'(t) + cos (T - t) f(t) = f(T)`. -/
def TangentKernel (f : ℝ → ℝ) (a b T : ℝ) : Prop :=
  ∃ p q : ℝ, EqOn f (fun t => p * cos t + q * sin t) (Icc a b) ∧
    f T = p * cos T + q * sin T

/-- The equations imposed on the difference `f` of two support functions by equality in the four
Mamikon terms of the cap. The middle equation `f'(t) = f(t + π/2)` is stated in integrated form. -/
structure CapKernel (φ : ℝ) (f : ℝ → ℝ) : Prop where
  top : f (π / 2) = 0
  first : TangentKernel f 0 φ (π / 2)
  middle : ∀ t ∈ Icc φ (π / 2 - φ),
    f t = f (π / 2 - φ) - ∫ u in t..(π / 2 - φ), f (u + π / 2)
  third : TangentKernel f (π / 2 - φ) (π / 2) (π - φ)
  fourth : TangentKernel f (π / 2) π π

/-- On `[π/2, π]`, `f(t) = -f(π) cos t`. -/
theorem CapKernel.upper_left {φ : ℝ} {f : ℝ → ℝ} (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc (π / 2) π) := by
  obtain ⟨p, q, heq, hπ⟩ := h.fourth
  have hL := heq (x := π / 2) ⟨le_rfl, by linarith [pi_pos]⟩
  have hq : q = 0 := by simpa [h.top] using hL.symm
  have hp : p = -f π := by
    simp only [cos_pi, sin_pi, mul_neg_one, mul_zero, add_zero] at hπ
    linarith
  intro t ht
  simpa [hp, hq] using heq ht

/-- On `[0, π]`, `f(t) = -f(π) cos t`: the two support functions differ by a horizontal
translation. -/
theorem CapKernel.eq_horizontal_translation {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc 0 π) := by
  -- Solve the equations in reverse order: on `[π/2, π]`, `[π/2 - φ, π/2]`, `[φ, π/2 - φ]` and
  -- `[0, φ]`; each step fixes the constants of the next one.
  set a : ℝ := -f π
  have hleft : EqOn f (fun t => a * cos t) (Icc (π / 2) π) := h.upper_left
  have hcos : cos φ ≠ 0 := (cos_pos_of_mem_Ioo
    ⟨by linarith [pi_pos, hφ.1], by linarith [hφ.2, pi_pos]⟩).ne'
  have hT : cos (π - φ) ≠ 0 := by simpa [cos_pi_sub] using hcos
  have hψ : φ ≤ π / 2 - φ := by linarith [hφ.2]
  have hthird : EqOn f (fun t => a * cos t) (Icc (π / 2 - φ) (π / 2)) := by
    obtain ⟨p, q, heq, htarget⟩ := h.third
    have hL := heq (x := π / 2) ⟨by linarith [hφ.1], le_rfl⟩
    have hq : q = 0 := by simpa [h.top] using hL.symm
    have htarget' := hleft (x := π - φ)
      ⟨by linarith [hφ.2, pi_pos], by linarith [hφ.1]⟩
    have hpa : p = a := by
      have he : p * cos (π - φ) = a * cos (π - φ) := by
        simpa [hq] using htarget.symm.trans htarget'
      exact (mul_right_cancel₀ hT) he
    intro t ht
    simpa [hpa, hq] using heq ht
  have hmiddle : EqOn f (fun t => a * cos t) (Icc φ (π / 2 - φ)) := by
    intro t ht
    have hi : (∫ u in t..(π / 2 - φ), f (u + π / 2)) =
        a * (cos (π / 2 - φ) - cos t) := by
      calc
        _ = ∫ u in t..(π / 2 - φ), -a * sin u := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le ht.2] at hu
          show f (u + π / 2) = -a * sin u
          rw [hleft (x := u + π / 2) ⟨by linarith [hu.1, ht.1, hφ.1],
            by linarith [hu.2, hφ.1]⟩]
          simp only [cos_add_pi_div_two]
          ring
        _ = -a * (cos t - cos (π / 2 - φ)) := by
          rw [intervalIntegral.integral_const_mul, integral_sin]
        _ = _ := by ring
    rw [h.middle t ht, hi,
      hthird (x := π / 2 - φ) ⟨le_rfl, by linarith [hφ.1]⟩]
    ring
  have hfirst : EqOn f (fun t => a * cos t) (Icc 0 φ) := by
    obtain ⟨p, q, heq, htarget⟩ := h.first
    have hq : q = 0 := by simpa [h.top] using htarget.symm
    have he := heq (x := φ) ⟨hφ.1.le, le_rfl⟩
    have hm := hmiddle (x := φ) ⟨le_rfl, hψ⟩
    have hp : p = a := by
      have he' : p * cos φ = a * cos φ := by simpa [hq] using he.symm.trans hm
      exact (mul_right_cancel₀ hcos) he'
    intro t ht
    simpa [hp, hq] using heq ht
  intro t ht
  by_cases hL : π / 2 ≤ t
  · exact hleft ⟨hL, ht.2⟩
  by_cases hψt : π / 2 - φ ≤ t
  · exact hthird ⟨hψt, (not_le.mp hL).le⟩
  by_cases hφt : φ ≤ t
  · exact hmiddle ⟨hφt, (not_le.mp hψt).le⟩
  · exact hfirst ⟨ht.1, (not_le.mp hφt).le⟩

end MovingSofaUniqueness

end

/-!
## Equality in a concave functional

A concave functional is constant on the segment between two of its global maximizers
(`eq_on_segment_of_isMax`).
-/

section

open Set

namespace MovingSofaOptimality
namespace ConvexDomain

variable {V : Type} (D : ConvexDomain V) {f : V → ℝ}

/-- A concave functional is constant on a segment joining two global maximizers. -/
theorem eq_on_segment_of_isMax (hc : D.IsConcave f) {x y : V}
    (hmax : ∀ z, f z ≤ f x) (hxy : f y = f x) {c : ℝ} (hcm : c ∈ Icc (0 : ℝ) 1) :
    f (D.comb c x y) = f x := by
  have h := hc x y c hcm
  rw [hxy] at h
  linarith [hmax (D.comb c x y)]

end ConvexDomain
end MovingSofaOptimality

end

/-!
## Equality in a Mamikon term

For continuous supporting curves `z K` of bounded variation on `[a, b]`, Baek's Theorem 7.4.1
writes Mamikon's area as `halfSquareIntegral` of the bounded tangent displacement
`displacement K (z K)` (`mamikon_eq_halfSquareIntegral`). If `z` is affine under Minkowski
combinations, so is the displacement (`displacement_combo`), and equality in Mamikon's convexity
inequality makes the displacements of the two bodies agree almost everywhere
(`displacement_ae_eq_of_mamikon_eq`), and everywhere on `(a, b)` if both are continuous there
(`displacement_eqOn_of_mamikon_eq`).
-/

section

open Real Set MeasureTheory Filter MovingSofaOptimality

namespace MovingSofaUniqueness

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

include hab hb hz hzl hlin in
/-- For `c ∈ (0, 1)`, equality in Mamikon's convexity inequality makes the displacements agree
almost everywhere. -/
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
/-- For `c ∈ (0, 1)`, equality in Mamikon's convexity inequality makes displacements that are
continuous on `(a, b)` agree there. -/
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

end MovingSofaUniqueness

end

/-!
## Solving the support equations

Under Baek's condition `InjCond1` the support function `h_K` is differentiable at every
`t ∈ [0, π/2) ∪ (π/2, π]`, with derivative `dot (vplus K t) (vvec t)`
(`support_hasDerivAt_of_injCond1`), and `vplus K` is continuous inside each `UpperArc`. A
continuous solution of the tangent equation `sin (T - t) f'(t) + cos (T - t) f(t) = f(T)` on
`(a, b)` has the form `p cos t + q sin t` on `[a, b]` and at `T` (`tangentKernel_of_equation`), and
a continuous solution of `f'(t) = f(t + L)` satisfies its integrated form
(`integrated_middle_equation`).
-/

section

open Real Set MeasureTheory MovingSofaOptimality
open MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- `[a, b]` lies in `[0, π/2]` or in `[π/2, π]`. -/
def UpperArc (a b : ℝ) : Prop :=
  (0 ≤ a ∧ b ≤ π / 2) ∨ (π / 2 ≤ a ∧ b ≤ π)

/-- Under `InjCond1`, `h_K` has derivative `dot (vplus K t) (vvec t)` at every
`t ∈ [0, π/2) ∪ (π/2, π]`. -/
theorem support_hasDerivAt_of_injCond1 {K : Set (ℝ × ℝ)}
    (hK : IsConvexBody K) (h1 : InjCond1 K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) :
    HasDerivAt (supp K) (dot (vplus K t) (vvec t)) t := by
  have hl := hasDerivWithinAt_supp_left hK t
  rw [← inj_vplus_eq_vminus_of_injCond1 hK h1 ht] at hl
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using
    hl.union (hasDerivWithinAt_supp_right hK t)

/-- An interior point of an upper arc is a normal in `[0, π/2) ∪ (π/2, π]`. -/
theorem arc_mem_regular {a b t : ℝ} (h : UpperArc a b) (ht : t ∈ Ioo a b) :
    t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩
  · exact Or.inr ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩

/-- Under `InjCond1`, `vplus K` is continuous inside an upper arc. -/
theorem vplus_continuousOn_arc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (hArc : UpperArc a b) :
    ContinuousOn (vplus K) (Ioo a b) := by
  obtain ⟨hcA, hcC, _, _⟩ := proposition6_4_6_continuous hK h1
  have hfirst : ContinuousOn (vplus K) (Ioo 0 (π / 2)) := by
    apply hcA.congr_mono ?_ Ioo_subset_Icc_self
    intro t ht
    exact ((proposition6_4_5 hK h1).1 t ⟨ht.1.le, ht.2⟩).1
  have hsecond : ContinuousOn (vplus K) (Ioo (π / 2) π) := by
    have hc : ContinuousOn (fun t => cK K (t - π / 2)) (Ioo (π / 2) π) :=
      hcC.comp (continuous_id.sub continuous_const).continuousOn
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    apply hc.congr
    intro t ht
    simp only [cK, cPlus, sub_add_cancel]
  rcases hArc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hfirst.mono (fun t ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)
  · exact hsecond.mono (fun t ht => ⟨ha.trans_lt ht.1, ht.2.trans_le hb⟩)

/-- The displacement of a continuous curve is continuous inside an upper arc. -/
theorem displacement_continuousOn_arc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (hArc : UpperArc a b) {z : ℝ → ℝ × ℝ}
    (hz : ContinuousOn z (Icc a b)) :
    ContinuousOn (displacement K z) (Ioo a b) := by
  have hd := (hz.mono Ioo_subset_Icc_self).sub (vplus_continuousOn_arc hK h1 hArc)
  have hv : ContinuousOn vvec (Ioo a b) := by unfold vvec; fun_prop
  exact (hd.fst.mul hv.fst).add (hd.snd.mul hv.snd)

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

/-- A continuous solution of the tangent equation `sin (T - t) f'(t) + cos (T - t) f(t) = f(T)` on
`(a, b)` has the form `p cos t + q sin t` on `[a, b]` and at `T`. -/
theorem tangentKernel_of_equation {f f' : ℝ → ℝ} {a b T : ℝ}
    (hab : a < b) (hTa : T - π < a) (hbT : b ≤ T) (hf : Continuous f)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (heq : ∀ t ∈ Ioo a b,
      sin (T - t) * f' t + cos (T - t) * f t = f T) :
    TangentKernel f a b T := by
  let q : ℝ → ℝ := fun t => (f t - f T * cos (T - t)) / sin (T - t)
  have hspos (t : ℝ) (ht : t ∈ Ioo a b) : 0 < sin (T - t) :=
    sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
  have hqd : ∀ t ∈ Ioo a b, HasDerivAt q 0 t := by
    intro t ht
    have hsne := (hspos t ht).ne'
    have hu : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub T
    have hcos := hu.cos
    have hsin := hu.sin
    have hnum : (f' t - f T * sin (T - t)) * sin (T - t) +
        (f t - f T * cos (T - t)) * cos (T - t) = 0 := by
      calc
        _ = (sin (T - t) * f' t + cos (T - t) * f t) -
            f T * (sin (T - t) ^ 2 + cos (T - t) ^ 2) := by ring
        _ = 0 := by rw [heq t ht, sin_sq_add_cos_sq]; ring
    have hquot := ((hd t ht).sub (hcos.const_mul (f T))).div hsin hsne
    have hq_eq : q = (f - fun y => f T * cos (T - y)) / fun x => sin (T - x) := rfl
    rw [hq_eq]
    convert hquot using 1
    simp only [Pi.sub_apply]
    rw [eq_div_iff (pow_ne_zero 2 hsne)]
    linear_combination -hnum
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected
    (fun t ht => (hqd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hqd t ht).deriv)
  have hsol : ∀ t ∈ Ioo a b, f t = f T * cos (T - t) + C * sin (T - t) := by
    intro t ht
    have h := hC t ht
    change (f t - f T * cos (T - t)) / sin (T - t) = C at h
    have hmul := (div_eq_iff (hspos t ht).ne').mp h
    linarith
  have hclosed : IsClosed {t : ℝ | f t = f T * cos (T - t) + C * sin (T - t)} :=
    isClosed_eq hf (by fun_prop)
  have hfull : ∀ t ∈ Icc a b, f t = f T * cos (T - t) + C * sin (T - t) := by
    have h := closure_minimal (fun t ht => hsol t ht) hclosed
    rw [closure_Ioo hab.ne] at h
    exact h
  refine ⟨f T * cos T + C * sin T, f T * sin T - C * cos T, ?_, ?_⟩
  · intro t ht
    rw [hfull t ht]
    simp only [cos_sub, sin_sub]
    ring
  · calc
      f T = f T * (sin T ^ 2 + cos T ^ 2) := by rw [sin_sq_add_cos_sq, mul_one]
      _ = _ := by ring

/-- A continuous solution of `f'(t) = f(t + L)` on `(a, b)` satisfies
`f(t) = f(b) - ∫ₜᵇ f(u + L) du` on `[a, b]`. -/
theorem integrated_middle_equation {f : ℝ → ℝ} {a b L : ℝ}
    (hf : Continuous f)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f (t + L)) t) :
    ∀ t ∈ Icc a b, f t = f b - ∫ u in t..b, f (u + L) := by
  intro t ht
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2
    hf.continuousOn
    (fun u hu => hd u ⟨ht.1.trans_lt hu.1, hu.2⟩)
    ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable t b)
  linarith

end MovingSofaUniqueness

end

/-!
## From equality in a Mamikon term to a support equation

Let `K₀` and `K₁` be right-angle caps satisfying `InjCond1`, and `[a, b]` an upper arc. Equality in
the Mamikon term of the tangent curves `tangentParam K T` (Baek's Theorems 8.3.1 and 8.3.2) makes
`h_{K₁} - h_{K₀}` a solution of the tangent equation with target `T`
(`tangentKernel_of_mamikon_eq`). Equality in the term of the outer corners gives the integrated
equation `f'(t) = f(t + π/2)` (`middleKernel_of_mamikon_eq`).
-/

section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- Equality in the Mamikon term with tangent target `T` on an upper arc `[a, b]` makes
`h_{K₁} - h_{K₀}` a `TangentKernel`. -/
theorem tangentKernel_of_mamikon_eq {a b T : ℝ}
    (hab : a < b) (hTa : T - π < a) (hbT : b ≤ T) (hArc : UpperArc a b)
    (K₀ K₁ : ConvexBodySet) (hcap₀ : IsCap K₀.1 (π / 2)) (hcap₁ : IsCap K₁.1 (π / 2))
    (h1₀ : InjCond1 K₀.1) (h1₁ : InjCond1 K₁.1) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b
        (tangentParam (convexBodyComb c K₀ K₁).1 T) =
      (1 - c) * mamikon K₀.1 a b (tangentParam K₀.1 T) +
        c * mamikon K₁.1 a b (tangentParam K₁.1 T)) :
    TangentKernel (fun t => supp K₁.1 t - supp K₀.1 t) a b T := by
  have hbπ : b < a + π := by linarith
  let z : ConvexBodySet → ℝ → ℝ × ℝ := fun K => tangentParam K.1 T
  have hz : ∀ K, IsCBV (z K) a b :=
    fun K => (theorem8_3_1 K.2 hTa hab.le hbT).1
  have hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t := by
    intro K t ht
    by_cases hlt : t < T
    · simp only [z, tangentParam, hlt, ite_true]
      exact vint_mem_line_left K.1 t T
    · have he : t = T := le_antisymm (ht.2.trans hbT) (not_lt.mp hlt)
      subst t
      simp only [z, tangentParam, lt_irrefl, ite_false]
      exact dot_vminus_uvec K.1 T
  have hlin : ∀ K L, ∀ d ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb d K L) t = (1 - d) • z K t + d • z L t :=
    fun K L d hd t ht => theorem8_3_2 hab.le hbT K L hd t ht
  have hdEq := displacement_eqOn_of_mamikon_eq hab hbπ z hz hzl hlin K₀ K₁ hc heq
    (displacement_continuousOn_arc hcap₀ h1₀ hArc (hz K₀).1)
    (displacement_continuousOn_arc hcap₁ h1₁ hArc (hz K₁).1)
  let f : ℝ → ℝ := fun t => supp K₁.1 t - supp K₀.1 t
  let f' : ℝ → ℝ := fun t => dot (vplus K₁.1 t) (vvec t) -
    dot (vplus K₀.1 t) (vvec t)
  have hf : Continuous f := K₁.2.continuous_supp.sub K₀.2.continuous_supp
  have hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t := by
    intro t ht
    exact (support_hasDerivAt_of_injCond1 K₁.2 h1₁ (arc_mem_regular hArc ht)).sub
      (support_hasDerivAt_of_injCond1 K₀.2 h1₀ (arc_mem_regular hArc ht))
  apply tangentKernel_of_equation hab hTa hbT hf hd
  intro t ht
  have hlt : t < T := ht.2.trans_le hbT
  have hs : sin (T - t) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [ht.1])).ne'
  have he := hdEq ht
  change displacement K₀.1 (tangentParam K₀.1 T) t =
    displacement K₁.1 (tangentParam K₁.1 T) t at he
  rw [tangent_displacement_formula K₀.1 hlt, tangent_displacement_formula K₁.1 hlt] at he
  field_simp [hs] at he
  dsimp [f, f']
  nlinarith [he]

/-- Equality in the outer-corner Mamikon term on an upper arc gives
`f(t) = f(b) - ∫ₜᵇ f(u + π/2) du` for `f = h_{K₁} - h_{K₀}`. -/
theorem middleKernel_of_mamikon_eq {a b : ℝ}
    (hab : a < b) (hbπ : b < a + π) (hArc : UpperArc a b)
    (K₀ K₁ : ConvexBodySet) (hcap₀ : IsCap K₀.1 (π / 2)) (hcap₁ : IsCap K₁.1 (π / 2))
    (h1₀ : InjCond1 K₀.1) (h1₁ : InjCond1 K₁.1) {c : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikon (convexBodyComb c K₀ K₁).1 a b
        (outerCorner (convexBodyComb c K₀ K₁).1) =
      (1 - c) * mamikon K₀.1 a b (outerCorner K₀.1) +
        c * mamikon K₁.1 a b (outerCorner K₁.1)) :
    ∀ t ∈ Icc a b, supp K₁.1 t - supp K₀.1 t =
      (supp K₁.1 b - supp K₀.1 b) -
        ∫ u in t..b, supp K₁.1 (u + π / 2) - supp K₀.1 (u + π / 2) := by
  let z : ConvexBodySet → ℝ → ℝ × ℝ := fun K => outerCorner K.1
  have hz : ∀ K, IsCBV (z K) a b := fun K => opt_outerCorner_cbv K.2 a b
  have hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t := by
    intro K t ht
    exact inj_dot_outerCorner_uvec K.1 t
  have hlin : ∀ K L, ∀ d ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
      z (convexBodyComb d K L) t = (1 - d) • z K t + d • z L t := by
    intro K L d hd t ht
    change outerCorner (convexBodyComb d K L).1 t = _
    rw [cvx_convexBodyComb_val hd, opt_outerCorner_comb K.2 L.2 hd]
    rfl
  have hdEq := displacement_eqOn_of_mamikon_eq hab hbπ z hz hzl hlin K₀ K₁ hc heq
    (displacement_continuousOn_arc hcap₀ h1₀ hArc (hz K₀).1)
    (displacement_continuousOn_arc hcap₁ h1₁ hArc (hz K₁).1)
  let f : ℝ → ℝ := fun t => supp K₁.1 t - supp K₀.1 t
  have hf : Continuous f := K₁.2.continuous_supp.sub K₀.2.continuous_supp
  apply integrated_middle_equation hf
  intro t ht
  have hd := (support_hasDerivAt_of_injCond1 K₁.2 h1₁ (arc_mem_regular hArc ht)).sub
    (support_hasDerivAt_of_injCond1 K₀.2 h1₀ (arc_mem_regular hArc ht))
  have he := hdEq ht
  change displacement K₀.1 (outerCorner K₀.1) t =
    displacement K₁.1 (outerCorner K₁.1) t at he
  rw [outer_displacement_formula, outer_displacement_formula] at he
  convert hd using 1
  dsimp [f]
  linarith

end MovingSofaUniqueness

end

/-!
## Equality in Baek's upper bound

`MamikonSegmentEquality φ x y c` says that the Minkowski combination with parameter `c` of the
triples `x` and `y` attains equality in each of the three Mamikon convexity inequalities behind the
concavity of `𝒬` (Baek's Lemma 8.3.3 and Theorem 8.3.8); this is equivalent to equality in the
concavity of `𝒬` (`mamikonSegmentEquality_iff`). If a cap `K` in `𝒦^i` has the sofa area of
Gerver's sofa, its triple `kiExtensionTriple` attains Gerver's value of `𝒬` (Baek's Theorem 8.2.4
and Corollary 8.5.8), so the segment from Gerver's triple to it satisfies these equalities
(`ki_maximizer_equality_conditions`).
-/

section

open Real Set MeasureTheory

namespace MovingSofaUniqueness

open MovingSofaOptimality

open GerverParams

/-- Equality at the parameter `c` in each of the three Mamikon convexity inequalities used to prove
the concavity of `𝒬`: for the cap and for the two auxiliary bodies. -/
structure MamikonSegmentEquality (φ : ℝ) (x y : LTriple φ) (c : ℝ) : Prop where
  middle : mamikonS φ ((lDomain φ).comb c x y).1.1.1 =
    (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1
  right : mamikonR φ ((lDomain φ).comb c x y).1.2.1.1 =
    (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1
  left : mamikonL φ ((lDomain φ).comb c x y).1.2.2.1 =
    (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1

/-- Equality in the concavity of `𝒬` at `c` is equivalent to equality in each of the three Mamikon
convexity inequalities. -/
theorem mamikonSegmentEquality_iff {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality φ x y c ↔
      upperQL φ ((lDomain φ).comb c x y) = (1 - c) * upperQL φ x + c * upperQL φ y := by
  -- `𝒬 = (𝒫 + 𝒮) - 𝒮 - ℛ - ℒ`, where the first term is affine (Baek's Lemma 8.3.7) and the other
  -- three are convex (Baek's Lemma 8.3.3); so `𝒬` is affine along the segment if and only if each
  -- of the three convexity inequalities is an equality.
  obtain ⟨-, cS, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hLin := lemma8_3_7 hφ
  set z := (lDomain φ).comb c x y with hz
  have hzv : z.1 = (convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2) := by
    simp only [hz, lDomain, LTriple.comb, hc, ↓reduceDIte]
  set kx : KiSet := ⟨x.1.1, x.2.1⟩
  set ky : KiSet := ⟨y.1.1, y.2.1⟩
  set kz : KiSet := ⟨z.1.1, z.2.1⟩
  have hkz : kz = kiComb c kx ky := by
    apply Subtype.ext
    show z.1.1 = (kiComb c kx ky).1
    simp only [kiComb, hc, ↓reduceDIte]
    rw [hzv]
  have hQ : ∀ w : LTriple φ, upperQL φ w = (mamikonS φ w.1.1.1 - -upperP φ w.1.1.1) -
      mamikonS φ w.1.1.1 - mamikonR φ w.1.2.1.1 - mamikonL φ w.1.2.2.1 := by
    intro w
    simp only [upperQL]
    rw [lemma8_3_4 hφ w.2]
    ring
  have hB : z.1.2.1 = convexBodyComb c x.1.2.1 y.1.2.1 := by rw [hzv]
  have hD : z.1.2.2 = convexBodyComb c x.1.2.2 y.1.2.2 := by rw [hzv]
  have e1 : mamikonS φ z.1.1.1 - -upperP φ z.1.1.1 =
      (1 - c) * (mamikonS φ x.1.1.1 - -upperP φ x.1.1.1) +
        c * (mamikonS φ y.1.1.1 - -upperP φ y.1.1.1) := by
    have h := hLin c hc kx ky
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at h
    exact h
  have e2 : mamikonS φ z.1.1.1 ≤
      (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1 := by
    have h := cS kx ky c hc
    rw [show kiDomain.comb c kx ky = kz from hkz.symm] at h
    exact h
  have e3 : mamikonR φ z.1.2.1.1 ≤
      (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1 := by
    rw [hB]
    exact cR x.1.2.1 y.1.2.1 c hc
  have e4 : mamikonL φ z.1.2.2.1 ≤
      (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1 := by
    rw [hD]
    exact cL x.1.2.2 y.1.2.2 c hc
  constructor
  · intro h
    have hS := h.middle
    have hR := h.right
    have hL := h.left
    change mamikonS φ z.1.1.1 = _ at hS
    change mamikonR φ z.1.2.1.1 = _ at hR
    change mamikonL φ z.1.2.2.1 = _ at hL
    change upperQL φ z = (1 - c) * upperQL φ x + c * upperQL φ y
    rw [hQ, hQ, hQ]
    linarith
  · intro hflat
    change upperQL φ z = (1 - c) * upperQL φ x + c * upperQL φ y at hflat
    rw [hQ, hQ, hQ] at hflat
    constructor
    · change mamikonS φ z.1.1.1 = _
      linarith
    · change mamikonR φ z.1.2.1.1 = _
      linarith
    · change mamikonL φ z.1.2.2.1 = _
      linarith

/-- If `x` and `y` both maximize `𝒬`, the three Mamikon convexity inequalities are equalities along
the segment from `x` to `y`: the equality case of Baek's Theorem 8.3.8. -/
theorem mamikonSegmentEquality_of_isMax {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {x y : LTriple φ} (hmax : ∀ z, upperQL φ z ≤ upperQL φ x)
    (hxy : upperQL φ y = upperQL φ x) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality φ x y c := by
  apply (mamikonSegmentEquality_iff hφ x y hc).2
  rw [(lDomain φ).eq_on_segment_of_isMax (theorem8_3_8 hφ) hmax hxy hc, hxy]
  ring

/-- Baek's Corollary 8.5.8: Gerver's triple maximizes `𝒬`. -/
theorem upperQL_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : LTriple P.φ) : upperQL P.φ x ≤ upperQL P.φ (gerverTriple hP hbox) :=
  corollary8_5_8 hP hbox x.2

/-- The canonical triple `(K, B_K, D_K)` in `𝓛` of a cap `K` in `𝒦^i` (Baek's Theorem 8.1.8). -/
noncomputable def kiExtensionTriple {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) : LTriple φ :=
  ⟨(⟨K, hK.1.2.1⟩, ⟨rightBody φ K, (theorem8_1_8 hφ hK).2.1⟩,
    ⟨leftBody φ K, (theorem8_1_8 hφ hK).2.2.1⟩), theorem8_1_8 hφ hK⟩

/-- If a cap in `𝒦^i` has the sofa area of Gerver's sofa, its canonical triple attains Gerver's
value of `𝒬`: both inequalities of `A_{π/2}(K) ≤ 𝒬(x) ≤ 𝒬(x_G)` are equalities. -/
theorem ki_upperQL_eq_gerver_of_sofaArea_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (harea : sofaArea (π / 2) K = area (gerverSofa P)) :
    upperQL P.φ (kiExtensionTriple hbox.1 hK) = upperQL P.φ (gerverTriple hP hbox) := by
  change upperQ P.φ K (rightBody P.φ K) (leftBody P.φ K) =
    upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap)
  have hLower := theorem8_2_4 hbox.1 hK
  have hUpper := corollary8_5_8 hP hbox (theorem8_1_8 hbox.1 hK)
  have hG := theorem8_4_6 hP hbox
  have hGarea := gm_sofaArea_cap hP hbox
  linarith

/-- If a cap in `𝒦^i` has the sofa area of Gerver's sofa, the segment from Gerver's triple to the
cap's triple satisfies `MamikonSegmentEquality`: both triples maximize `𝒬` (Baek's
Corollary 8.5.8). -/
theorem ki_maximizer_equality_conditions {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (harea : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∀ c ∈ Icc (0 : ℝ) 1,
      MamikonSegmentEquality P.φ (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) c :=
  fun _ hc => mamikonSegmentEquality_of_isMax (gm_φ_mem_Ioo hP hbox) (upperQL_le_gerver hP hbox)
    (ki_upperQL_eq_gerver_of_sofaArea_eq hP hbox hK harea) hc

end MovingSofaUniqueness

end

/-!
## The cap kernel

The cap's Mamikon term `mamikonS φ` is the sum of four terms, on `[0, φ]`, `[φ, π/2 - φ]`,
`[π/2 - φ, π/2]` and `[π/2, π]`, each convex under Minkowski combinations. Equality for the sum
forces equality in each term, and the preceding sections turn the four equalities into
`CapKernel φ (h_{K₁} - h_{K₀})` (`capKernel_of_mamikonS_eq`). `capKernel_of_triple_midpoint` states
this for the caps of two triples with `MamikonSegmentEquality` at `c = 1/2`, the form that
`ki_sofa_eq_gerver_translate` uses to prove Proposition 5 of note 20.
-/

section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- For caps `K₀` and `K₁` in `𝒦^i` and `c ∈ (0, 1)`, equality in the convexity inequality of
`mamikonS φ` gives `CapKernel φ (h_{K₁} - h_{K₀})`. -/
theorem capKernel_of_mamikonS_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (hK₀ : IsKi K₀.1) (hK₁ : IsKi K₁.1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikonS φ (convexBodyComb c K₀ K₁).1 =
      (1 - c) * mamikonS φ K₀.1 + c * mamikonS φ K₁.1) :
    CapKernel φ (fun t => supp K₁.1 t - supp K₀.1 t) := by
  have hπ := pi_pos
  have hc' : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
  -- Step 1: `mamikonS φ` is the sum of four Mamikon terms, each convex (`opt_mamikon_tangent`,
  -- `opt_mamikon_outer`), so equality for the sum forces equality in each term.
  let Kc := convexBodyComb c K₀ K₁
  let F₁ : ConvexBodySet → ℝ := fun K => mamikon K.1 0 φ (tangentParam K.1 (π / 2))
  let F₂ : ConvexBodySet → ℝ := fun K => mamikon K.1 φ (π / 2 - φ) (outerCorner K.1)
  let F₃ : ConvexBodySet → ℝ := fun K => mamikon K.1 (π / 2 - φ) (π / 2)
    (tangentParam K.1 (π / 2 + (π / 2 - φ)))
  let F₄ : ConvexBodySet → ℝ := fun K => mamikon K.1 (π / 2) π (tangentParam K.1 π)
  have hsum (K : ConvexBodySet) : mamikonS φ K.1 = F₁ K + F₂ K + F₃ K + F₄ K := rfl
  have h₁ : F₁ Kc ≤ (1 - c) * F₁ K₀ + c * F₁ K₁ :=
    (opt_mamikon_tangent (t := π / 2) (a := 0) (b := φ)
      hφ.1 (by linarith [hφ.2]) (by linarith) (by linarith [hφ.2])).2 K₀ K₁ c hc'
  have h₂ : F₂ Kc ≤ (1 - c) * F₂ K₀ + c * F₂ K₁ :=
    (opt_mamikon_outer (a := φ) (b := π / 2 - φ)
      (by linarith [hφ.2]) (by linarith [hφ.1])).2 K₀ K₁ c hc'
  have h₃ : F₃ Kc ≤ (1 - c) * F₃ K₀ + c * F₃ K₁ :=
    (opt_mamikon_tangent (t := π / 2 + (π / 2 - φ)) (a := π / 2 - φ) (b := π / 2)
      (by linarith [hφ.1]) (by linarith [hφ.2]) (by linarith)
      (by linarith [hφ.2])).2 K₀ K₁ c hc'
  have h₄ : F₄ Kc ≤ (1 - c) * F₄ K₀ + c * F₄ K₁ :=
    (opt_mamikon_tangent (t := π) (a := π / 2) (b := π)
      (by linarith) (by linarith) (by linarith) le_rfl).2 K₀ K₁ c hc'
  rw [hsum, hsum, hsum] at heq
  change F₁ Kc + F₂ Kc + F₃ Kc + F₄ Kc = _ at heq
  have e₁ : F₁ Kc = (1 - c) * F₁ K₀ + c * F₁ K₁ := by linarith
  have e₂ : F₂ Kc = (1 - c) * F₂ K₀ + c * F₂ K₁ := by linarith
  have e₃ : F₃ Kc = (1 - c) * F₃ K₀ + c * F₃ K₁ := by linarith
  have e₄ : F₄ Kc = (1 - c) * F₄ K₀ + c * F₄ K₁ := by linarith
  -- Step 2: the four equalities give the equations of `CapKernel`; at `π/2` both supports are `1`.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show supp K₁.1 (π / 2) - supp K₀.1 (π / 2) = 0
    rw [hK₀.1.2.2.2.1, hK₁.1.2.2.2.1, sub_self]
  · exact tangentKernel_of_mamikon_eq hφ.1 (by linarith) (by linarith [hφ.2])
      (Or.inl ⟨le_rfl, by linarith [hφ.2]⟩)
      K₀ K₁ hK₀.1 hK₁.1 hK₀.2.1.1 hK₁.2.1.1 hc e₁
  · exact middleKernel_of_mamikon_eq (by linarith [hφ.2]) (by linarith [hφ.1])
      (Or.inl ⟨hφ.1.le, by linarith [hφ.1]⟩)
      K₀ K₁ hK₀.1 hK₁.1 hK₀.2.1.1 hK₁.2.1.1 hc e₂
  · have ht : π / 2 + (π / 2 - φ) = π - φ := by ring
    simp only [F₃, Kc, ht] at e₃
    exact tangentKernel_of_mamikon_eq (by linarith [hφ.1]) (by linarith)
      (by linarith [hφ.2]) (Or.inl ⟨by linarith [hφ.2], le_rfl⟩)
      K₀ K₁ hK₀.1 hK₁.1 hK₀.2.1.1 hK₁.2.1.1 hc e₃
  · exact tangentKernel_of_mamikon_eq (by linarith) (by linarith) le_rfl
      (Or.inr ⟨le_rfl, le_rfl⟩)
      K₀ K₁ hK₀.1 hK₁.1 hK₀.2.1.1 hK₁.2.1.1 hc e₄

/-- If two triples satisfy `MamikonSegmentEquality` at `c = 1/2`, the difference of the support
functions of their caps is a `CapKernel`. -/
theorem capKernel_of_triple_midpoint {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) (h : MamikonSegmentEquality φ x y (1 / 2)) :
    CapKernel φ (fun t => supp y.1.1.1 t - supp x.1.1.1 t) := by
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hcap : ((lDomain φ).comb (1 / 2) x y).1.1 =
      convexBodyComb (1 / 2) x.1.1 y.1.1 := by
    simp only [lDomain, LTriple.comb, hhalf, ↓reduceDIte]
  have heq := h.middle
  rw [hcap] at heq
  exact capKernel_of_mamikonS_eq hφ x.1.1 y.1.1 x.2.1 y.2.1
    (by constructor <;> norm_num) heq

end MovingSofaUniqueness

end

/-!
## Caps with horizontally translated supports

A right-angle cap is the set of points `p` with `0 ≤ p.2` and `dot p (uvec t) ≤ h_K(t)` for
`t ∈ [0, π]` (`mem_right_cap_iff`), and its niche is also described by its supports
(`mem_right_niche_iff`). So if `h_K(t) - h_G(t) = a cos t` on `[0, π]`, translation by `(a, 0)` maps
`G` onto `K` (`cap_eq_translate_of_upper_support`) and the niche of `G` onto that of `K`, and `K`
minus its niche is the translate of `G` minus its niche (`sofa_eq_translate_of_upper_support`):
equation (21) of note 20, and `lem:translate` of the manuscript `docs/paper`. Conversely, a horizontal
translate of a right-angle cap is a right-angle cap (`isCap_translate_horizontal`) whose niche is the
translated niche (`niche_translate_horizontal`), so it has the same sofa area
(`sofaArea_translate_horizontal`).
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- A point lies in a right-angle cap if and only if it lies above the floor and below the
supporting lines at the normals in `[0, π]`. -/
theorem mem_right_cap_iff {K : Set Plane} (hK : IsCap K (π / 2)) (p : Plane) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨(inj_cap_strip hK hp).1,
      fun t _ => dot_le_supp hK.2.1.2.1 hp t⟩
  · rintro ⟨hfloor, hupper⟩
    obtain ⟨hω, hbody, hωtop, htop, hωfloor, hbottom, hplanes⟩ := hK
    rw [nef_eq_setOf_supp hbody hplanes]
    intro t ht
    simp only [jSet, mem_union, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with (ht | ht) | ht | ht
    · exact hupper t ⟨ht.1, by linarith [ht.2, pi_pos]⟩
    · exact hupper t ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    · have he : t = 3 * π / 2 := by linarith
      rw [he, hbottom, uvec_three_pi_div_two]
      simpa [dot] using hfloor
    · rw [ht, hbottom, uvec_three_pi_div_two]
      simpa [dot] using hfloor

/-- A point lies in the niche of a right-angle cap if and only if it lies above the floor and in
the open inner quadrant of some `t ∈ (0, π/2)`. -/
theorem mem_right_niche_iff (K : Set Plane) (p : Plane) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2),
      dot p (uvec t) < supp K t - 1 ∧
      dot p (vvec t) < supp K (t + π / 2) - 1 := by
  have hf : p ∈ fan (π / 2) ↔ 0 ≤ p.2 := by
    simp [fan, halfPlus, uvec_pi_div_two, dot]
  change (p ∈ fan (π / 2) ∧ p ∈ ⋃ t ∈ Ioo (0 : ℝ) (π / 2), qMinus K t) ↔ _
  rw [hf]
  simp only [mem_iUnion, exists_prop, ms_mem_qMinus_iff]

private theorem dot_sub_horizontal_u (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (uvec t) = dot p (uvec t) - a * cos t := by
  simp only [dot, uvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

private theorem dot_sub_horizontal_v (p : Plane) (a t : ℝ) :
    dot (p - (a, 0)) (vvec t) = dot p (vvec t) + a * sin t := by
  simp only [dot, vvec, Prod.fst_sub, Prod.snd_sub, sub_zero]
  ring

/-- If `h_K(t) - h_G(t) = a cos t` on `[0, π]`, then `p ∈ K` if and only if `p - (a, 0) ∈ G`. -/
theorem mem_cap_sub_horizontal_iff {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ K ↔ p - (a, 0) ∈ G := by
  rw [mem_right_cap_iff hK, mem_right_cap_iff hG]
  simp only [Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    rw [dot_sub_horizontal_u]
    linarith [hu t ht, hsupp t ht]
  · rintro ⟨hp, hu⟩
    refine ⟨hp, fun t ht => ?_⟩
    have hi := hu t ht
    rw [dot_sub_horizontal_u] at hi
    linarith [hsupp t ht]

/-- Under the same support identity, `p` lies in the niche of `K` if and only if `p - (a, 0)` lies
in the niche of `G`. -/
theorem mem_niche_sub_horizontal_iff {K G : Set Plane} (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t)
    (p : Plane) : p ∈ niche K (π / 2) ↔ p - (a, 0) ∈ niche G (π / 2) := by
  rw [mem_right_niche_iff, mem_right_niche_iff]
  simp only [Prod.snd_sub, sub_zero]
  have hbounds : ∀ t ∈ Ioo (0 : ℝ) (π / 2),
      supp K t - supp G t = a * cos t ∧
        supp K (t + π / 2) - supp G (t + π / 2) = -a * sin t := by
    intro t ht
    refine ⟨hsupp t ⟨ht.1.le, by linarith [ht.2, pi_pos]⟩, ?_⟩
    have h := hsupp (t + π / 2)
      ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
    simpa [cos_add_pi_div_two, mul_neg, neg_mul] using h
  constructor
  · rintro ⟨hp, t, ht, hu, hv⟩
    refine ⟨hp, t, ht, ?_, ?_⟩
    · rw [dot_sub_horizontal_u]
      linarith [(hbounds t ht).1]
    · rw [dot_sub_horizontal_v]
      linarith [(hbounds t ht).2]
  · rintro ⟨hp, t, ht, hu, hv⟩
    rw [dot_sub_horizontal_u] at hu
    rw [dot_sub_horizontal_v] at hv
    exact ⟨hp, t, ht, by linarith [(hbounds t ht).1],
      by linarith [(hbounds t ht).2]⟩

/-- Equation (21) of note 20: if `h_K(t) - h_G(t) = a cos t` on `[0, π]`, then `K` minus its niche
is the translate by `(a, 0)` of `G` minus its niche. -/
theorem sofa_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K \ niche K (π / 2) = Rigid.translate (a, 0) '' (G \ niche G (π / 2)) := by
  ext p
  constructor
  · intro hp
    refine ⟨p - (a, 0), ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp p).mp hp.1,
      fun hn => hp.2 ((mem_niche_sub_horizontal_iff a hsupp p).mpr hn)⟩, ?_⟩
    simp
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(mem_cap_sub_horizontal_iff hK hG a hsupp _).mpr (by simpa using hq.1), ?_⟩
    intro hn
    have hqN := (mem_niche_sub_horizontal_iff a hsupp _).mp hn
    exact hq.2 (by simpa using hqN)

/-- `lem:translate` of the manuscript `docs/paper`, for the caps: if
`h_K(t) - h_G(t) = a cos t` on `[0, π]` for two right-angle caps, then `K = G + (a, 0)`. With
`mem_niche_sub_horizontal_iff` and `sofa_eq_translate_of_upper_support`, this is part (a) of the lemma. -/
theorem cap_eq_translate_of_upper_support {K G : Set Plane}
    (hK : IsCap K (π / 2)) (hG : IsCap G (π / 2)) (a : ℝ)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp G t = a * cos t) :
    K = Rigid.translate (a, 0) '' G := by
  ext p
  rw [Rigid.mem_translate_image]
  exact mem_cap_sub_horizontal_iff hK hG a hsupp p

/-- Translating a convex body by `(a, 0)` adds `a cos t` to its support function:
`h_{G + (a, 0)}(t) - h_G(t) = a cos t`. -/
theorem supp_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a t : ℝ) :
    supp (Rigid.translate (a, 0) '' G) t - supp G t = a * cos t := by
  rw [Rigid.coe_translate, supp_translate G _ t hG.2.1 hG.1]
  simp only [dot, uvec]
  ring

/-- A horizontal translate `G + (a, 0)` of a right-angle cap `G` is a right-angle cap: the
translation keeps the support values at the normals `π/2` and `3π/2`, where `cos t = 0`, and the
normal angles of the half-planes. -/
theorem isCap_translate_horizontal {G : Set Plane} (hG : IsCap G (π / 2)) (a : ℝ) :
    IsCap (Rigid.translate (a, 0) '' G) (π / 2) := by
  obtain ⟨hω, hbody, htop, htop', hfloor, hfloor', hplanes⟩ := hG
  have hs : ∀ t, cos t = 0 → supp (Rigid.translate (a, 0) '' G) t = supp G t := by
    intro t ht
    have h := supp_translate_horizontal hbody a t
    rwa [ht, mul_zero, sub_eq_zero] at h
  have hc₁ : cos (π / 2) = 0 := cos_pi_div_two
  have hc₂ : cos (π / 2 + π) = 0 := by rw [cos_add_pi, hc₁, neg_zero]
  have hc₃ : cos (3 * π / 2) = 0 := by rw [show 3 * π / 2 = π / 2 + π by ring, hc₂]
  refine ⟨hω, ?_, (hs _ hc₁).trans htop, (hs _ hc₁).trans htop', (hs _ hc₂).trans hfloor,
    (hs _ hc₃).trans hfloor', ?_⟩
  · rw [Rigid.coe_translate]
    exact nef_isConvexBody_translate hbody _
  · rw [Rigid.coe_translate]
    exact nef_isHalfPlaneInter_translate hplanes _

/-- The niche of `G + (a, 0)` is the niche of `G` translated by `(a, 0)`. -/
theorem niche_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    niche (Rigid.translate (a, 0) '' G) (π / 2) = Rigid.translate (a, 0) '' niche G (π / 2) := by
  ext p
  rw [Rigid.mem_translate_image]
  exact mem_niche_sub_horizontal_iff a (fun t _ => supp_translate_horizontal hG a t) p

/-- A horizontal translation preserves the sofa area: `𝒜_{π/2}(G + (a, 0)) = 𝒜_{π/2}(G)`, since
it translates the niche and preserves areas. -/
theorem sofaArea_translate_horizontal {G : Set Plane} (hG : IsConvexBody G) (a : ℝ) :
    sofaArea (π / 2) (Rigid.translate (a, 0) '' G) = sofaArea (π / 2) G := by
  unfold sofaArea
  rw [niche_translate_horizontal hG, Rigid.area_image, Rigid.area_image]

end MovingSofaUniqueness

end
