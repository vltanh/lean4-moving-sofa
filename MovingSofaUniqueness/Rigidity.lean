module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import MovingSofaOptimality.Convex.ConvexDomain
public import MovingSofaOptimality.Convex.Mamikon
public import Mathlib.MeasureTheory.Measure.OpenPos
public import MovingSofaOptimality.Optimality.Concavity
public import Mathlib.Analysis.Calculus.MeanValue
public import MovingSofaOptimality.Main
public import MovingSofaUniqueness.Rigid
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

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
## The scalar equality case behind Mamikon convexity

The Mamikon formula is one half the integral of a squared tangent displacement.
The exact convexity gap is therefore a positive multiple of the squared L²
distance between the two displacement functions. This module proves that scalar
step without any moving-sofa definitions or unproved geometric assumptions.

Integrability is explicit. In particular, the fact that Lean's integral of a
nonintegrable function is defined to be zero cannot produce a spurious equality
case here.
-/

section

open MeasureTheory Filter

namespace MovingSofaUniqueness

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) {f g : X → ℝ}

/-- The scalar functional appearing in Mamikon's formula. -/
noncomputable def halfSquareIntegral (f : X → ℝ) : ℝ :=
  (1 / 2) * ∫ x, (f x) ^ 2 ∂μ

/-- Integrability of the squared displacement difference follows from the three
integrable quadratic monomials. -/
theorem integrable_sq_sub
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun x => (f x - g x) ^ 2) μ := by
  have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) μ :=
    (hf.add hg).sub (hfg.const_mul 2)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  ring

/-- Expanding the integral of a squared difference. -/
theorem integral_sq_sub
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) =
      (∫ x, (f x) ^ 2 ∂μ) + (∫ x, (g x) ^ 2 ∂μ) -
        2 * (∫ x, f x * g x ∂μ) := by
  calc
    (∫ x, (f x - g x) ^ 2 ∂μ) =
        ∫ x, (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ := hf.add hg
      rw [integral_sub hsum (hfg.const_mul 2), integral_add hf hg, integral_const_mul]

/-- Expanding a squared affine combination before integrating. The identity is
valid for every real `c`, not only for convex coefficients. -/
theorem integral_sq_combo (c : ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
      (1 - c) ^ 2 * (∫ x, (f x) ^ 2 ∂μ) +
        (2 * c * (1 - c)) * (∫ x, f x * g x ∂μ) +
        c ^ 2 * (∫ x, (g x) ^ 2 ∂μ) := by
  calc
    (∫ x, ((1 - c) * f x + c * g x) ^ 2 ∂μ) =
        ∫ x, (1 - c) ^ 2 * (f x) ^ 2 +
          (2 * c * (1 - c)) * (f x * g x) + c ^ 2 * (g x) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      have h12 : Integrable
          (fun x => (1 - c) ^ 2 * (f x) ^ 2 + (2 * c * (1 - c)) * (f x * g x)) μ :=
        (hf.const_mul ((1 - c) ^ 2)).add (hfg.const_mul (2 * c * (1 - c)))
      rw [integral_add h12 (hg.const_mul (c ^ 2)),
        integral_add (hf.const_mul ((1 - c) ^ 2)) (hfg.const_mul (2 * c * (1 - c))),
        integral_const_mul, integral_const_mul, integral_const_mul]

/-- Exact square-gap identity. At the midpoint the coefficient is `1/8`. -/
theorem halfSquareIntegral_combo_gap (c : ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) μ)
    (hg : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g -
        halfSquareIntegral μ (fun x => (1 - c) * f x + c * g x) =
      (c * (1 - c) / 2) * (∫ x, (f x - g x) ^ 2 ∂μ) := by
  unfold halfSquareIntegral
  rw [integral_sq_combo μ c hf hg hfg, integral_sq_sub μ hf hg hfg]
  ring

/-- Zero squared L² distance is exactly almost-everywhere equality. -/
theorem integral_sq_sub_eq_zero_iff
    (hint : Integrable (fun x => (f x - g x) ^ 2) μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) = 0 ↔ f =ᵐ[μ] g := by
  have hzero := integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg (f x - g x)) hint
  constructor
  · intro h
    have hae := hzero.mp h
    filter_upwards [hae] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    apply hzero.mpr
    filter_upwards [h] with x hx
    simp [hx]

/-- Equality in a nontrivial convex combination forces equality of the
underlying displacement functions almost everywhere, and conversely. -/
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
## Matching the four Mamikon equality intervals

This file proves the algebraic/integral propagation step independently of caps.
Deriving `CapKernel` from vanishing Mamikon gaps is done in `MamikonCapKernel.lean`.
-/

section

open Set Real MeasureTheory

namespace MovingSofaUniqueness

/-- The solved first-order equation of a tangent term, including its target value.
The target can lie outside the interval on which the equation was solved. -/
def TangentKernel (f : ℝ → ℝ) (a b T : ℝ) : Prop :=
  ∃ p q : ℝ, EqOn f (fun t => p * cos t + q * sin t) (Icc a b) ∧
    f T = p * cos T + q * sin T

/-- Consequences of the four separate zero square gaps.

The middle relation is an integral identity, so no unjustified pointwise
classical derivative or differentiability at the top support is assumed. -/
structure CapKernel (φ : ℝ) (f : ℝ → ℝ) : Prop where
  top : f (π / 2) = 0
  first : TangentKernel f 0 φ (π / 2)
  middle : ∀ t ∈ Icc φ (π / 2 - φ),
    f t = f (π / 2 - φ) - ∫ u in t..(π / 2 - φ), f (u + π / 2)
  third : TangentKernel f (π / 2 - φ) (π / 2) (π - φ)
  fourth : TangentKernel f (π / 2) π π

/-- The upper-left quadrant is determined by the top value. -/
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

/-- Equality in the four cap terms has only the horizontal-translation mode. -/
theorem CapKernel.eq_horizontal_translation {φ : ℝ} {f : ℝ → ℝ}
    (hφ : φ ∈ Ioo 0 (π / 4)) (h : CapKernel φ f) :
    EqOn f (fun t => -f π * cos t) (Icc 0 π) := by
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
## Equality cases for concave quadratic functionals

Theorem 7.1.5 proves maximality from nonpositive first variations. Uniqueness also requires
control of the equality case. The exact deficit identity below separates the first variation
from the midpoint concavity gap; both terms are nonnegative at a maximum.
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
  apply le_antisymm (hmax _)
  have h := hc x y c hcm
  rw [hxy] at h
  nlinarith

/-- The deficit of a quadratic functional is minus its first variation plus four times its
midpoint concavity gap. No concavity or maximality assumption is needed for this identity. -/
theorem quadratic_deficit_identity (hq : D.IsQuadratic f) (x y : V) :
    f x - f y = -D.dirDeriv f x y +
      4 * (f (D.comb (1 / 2) x y) - (f x + f y) / 2) := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : f = fun v => g v v := funext hfg
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  rw [hf, lemma7_1_4 D hg]
  change g x x - g y y = -(g x y + g y x - 2 * g x x) +
    4 * (g (D.comb (1 / 2) x y) (D.comb (1 / 2) x y) - (g x x + g y y) / 2)
  rw [cvx_bilin_comb D hg x y hhalf]
  ring

/-- A concave quadratic functional lies below its first-order affine approximation. -/
theorem quadratic_tangent_bound (hq : D.IsQuadratic f) (hc : D.IsConcave f) (x y : V) :
    f y ≤ f x + D.dirDeriv f x y := by
  have h := hc x y (1 / 2) (by constructor <;> norm_num)
  have he := D.quadratic_deficit_identity hq x y
  nlinarith

/-- A direction from one maximizer to another has zero first variation, not merely a
nonpositive first variation. -/
theorem dirDeriv_eq_zero_of_isMax (hq : D.IsQuadratic f) (hc : D.IsConcave f) {x y : V}
    (hmax : ∀ z, f z ≤ f x) (hxy : f y = f x) : D.dirDeriv f x y = 0 := by
  have hle := (theorem7_1_5 D hq hc x).1 hmax y
  have hge := D.quadratic_tangent_bound hq hc x y
  rw [hxy] at hge
  linarith

end ConvexDomain
end MovingSofaOptimality

end

/-!
## Equality in Mamikon's formula identifies the displacement functions

The square-integrability hypotheses are proved from the bounded measurable
functions supplied by Theorem 7.4.1. Equality cannot arise from Lean's default
value for a nonintegrable integral. The result is first almost-everywhere
 equality and then pointwise equality on any interval where both displacements
are continuous.
-/

section

open Real Set MeasureTheory Filter MovingSofaOptimality

namespace MovingSofaUniqueness

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

end MovingSofaUniqueness

end

/-!
## Support regularity and the exact kernel of the tangent equation

Only open arcs avoiding the possible top atom are differentiated. The support
function itself is continuous at all endpoints. A constant integrating factor
is first proved on the open interval and then extended by continuity; this
also handles a target normal equal to the interval's right endpoint.
-/

section

open Real Set MeasureTheory MovingSofaOptimality
open MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- An upper arc lies entirely on one side of the possible top atom. -/
def UpperArc (a b : ℝ) : Prop :=
  (0 ≤ a ∧ b ≤ π / 2) ∨ (π / 2 ≤ a ∧ b ≤ π)

/-- Equal one-sided support derivatives give an ordinary derivative. -/
theorem support_hasDerivAt_of_injCond1 {K : Set (ℝ × ℝ)}
    (hK : IsConvexBody K) (h1 : InjCond1 K) {t : ℝ}
    (ht : t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π) :
    HasDerivAt (supp K) (dot (vplus K t) (vvec t)) t := by
  have hv := inj_vplus_eq_vminus_of_injCond1 hK h1 ht
  have hl := hasDerivWithinAt_supp_left hK t
  have hr := hasDerivWithinAt_supp_right hK t
  rw [← hv] at hl
  have hu : Iic t ∪ Ici t = (univ : Set ℝ) := by
    ext s
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total s t
  have hd := hl.union hr
  simpa only [hu, hasDerivWithinAt_univ] using hd

theorem arc_mem_regular {a b t : ℝ} (h : UpperArc a b) (ht : t ∈ Ioo a b) :
    t ∈ Ico 0 (π / 2) ∪ Ioc (π / 2) π := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩
  · exact Or.inr ⟨ha.trans_lt ht.1, ht.2.le.trans hb⟩

/-- Positive support vertices are continuous on each open upper arc. -/
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

/-- Any continuous supporting curve has continuous displacement on a regular arc. -/
theorem displacement_continuousOn_arc {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2))
    (h1 : InjCond1 K) {a b : ℝ} (hArc : UpperArc a b) {z : ℝ → ℝ × ℝ}
    (hz : ContinuousOn z (Icc a b)) :
    ContinuousOn (displacement K z) (Ioo a b) := by
  have hd := (hz.mono Ioo_subset_Icc_self).sub (vplus_continuousOn_arc hK h1 hArc)
  have hv : ContinuousOn vvec (Ioo a b) := by unfold vvec; fun_prop
  exact (hd.fst.mul hv.fst).add (hd.snd.mul hv.snd)

/-- Explicit displacement to the intersection with the target supporting line. -/
theorem tangent_displacement_formula (K : Set (ℝ × ℝ)) {T t : ℝ} (ht : t < T) :
    displacement K (tangentParam K T) t =
      (supp K T - supp K t * cos (T - t)) / sin (T - t) -
        dot (vplus K t) (vvec t) := by
  simp only [displacement, tangentParam, ht, ite_true, vint, dot_sub_left,
    dot_add_left, dot_smul_left, dot_uvec_vvec, dot_vvec_self,
    mul_zero, mul_one, zero_add]

/-- Explicit displacement to the outer corner. -/
theorem outer_displacement_formula (K : Set (ℝ × ℝ)) (t : ℝ) :
    displacement K (outerCorner K) t =
      supp K (t + π / 2) - dot (vplus K t) (vvec t) := by
  rw [displacement, dot_sub_left, inj_dot_outerCorner_vvec]

/-- Complete kernel of the tangent equation, with no differentiability assumed
at either endpoint. -/
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

/-- The middle equation integrates to the form consumed by `CapKernel`. -/
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
## From Mamikon equality to the support equations

Each convex-body family uses the continuous supporting curves already proved
in Theorem 8.3.1 and the outer-corner lemmas. Square-integrability and pointwise
interior equality come from `MamikonDisplacement`; support derivatives and
endpoint-safe integration come from `SupportKernelEquations`.
-/

section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- Equality in a tangent Mamikon term forces the complete support kernel. -/
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
  have hf : Continuous f := (inj_continuous_supp K₁.2).sub (inj_continuous_supp K₀.2)
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

/-- Equality in the outer-corner term integrates to the middle support equation. -/
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
    rw [opt_convexBodyComb_val hd, opt_outerCorner_comb K.2 L.2 hd]
    rfl
  have hdEq := displacement_eqOn_of_mamikon_eq hab hbπ z hz hzl hlin K₀ K₁ hc heq
    (displacement_continuousOn_arc hcap₀ h1₀ hArc (hz K₀).1)
    (displacement_continuousOn_arc hcap₁ h1₁ hArc (hz K₁).1)
  let f : ℝ → ℝ := fun t => supp K₁.1 t - supp K₀.1 t
  have hf : Continuous f := (inj_continuous_supp K₁.2).sub (inj_continuous_supp K₀.2)
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
## Equality conditions for the optimal sofa

This module is the first step of the uniqueness argument (`MovingSofaUniqueness/`). A competing
maximizer of `upperQL` has zero first variation at Gerver's triple, and every
Minkowski segment joining it to Gerver's triple saturates all three Mamikon convexity
inequalities separately. At the midpoint these equalities, together with zero first variation,
are also sufficient for equality of `upperQL` values. The final lemmas apply the necessary
conditions to caps in `𝒦^i` that attain Gerver's sofa area.

Geometric rigidity of these equality cases, and equality in the reductions from arbitrary
moving sofas to caps, are proved in `MovingSofaUniqueness/`. Uniqueness of Romik's parameters is not
by itself uniqueness of the area-maximizing moving sofas.
-/

section

open Real Set MeasureTheory

namespace MovingSofaUniqueness

open MovingSofaOptimality

open GerverParams

/-- Equality in each of the three convexity inequalities used to prove concavity of `upperQL`.
The cap and the two auxiliary bodies are kept separate so no cancellation can hide a gap. -/
structure MamikonSegmentEquality (φ : ℝ) (x y : LTriple φ) (c : ℝ) : Prop where
  middle : mamikonS φ ((lDomain φ).comb c x y).1.1.1 =
    (1 - c) * mamikonS φ x.1.1.1 + c * mamikonS φ y.1.1.1
  right : mamikonR φ ((lDomain φ).comb c x y).1.2.1.1 =
    (1 - c) * mamikonR φ x.1.2.1.1 + c * mamikonR φ y.1.2.1.1
  left : mamikonL φ ((lDomain φ).comb c x y).1.2.2.1 =
    (1 - c) * mamikonL φ x.1.2.2.1 + c * mamikonL φ y.1.2.2.1

/-- Equality in concavity of `upperQL` is equivalent to equality in each of the three
Mamikon convexity inequalities. This does not require the endpoints to be maximizers. -/
theorem mamikonSegmentEquality_iff {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : LTriple φ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality φ x y c ↔
      upperQL φ ((lDomain φ).comb c x y) = (1 - c) * upperQL φ x + c * upperQL φ y := by
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

/-- If two triples maximize `upperQL`, the three Mamikon convexity gaps vanish individually
along their entire segment. This is the equality case of the proof of Theorem 8.3.8. -/
theorem mamikonSegmentEquality_of_isMax {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {x y : LTriple φ} (hmax : ∀ z, upperQL φ z ≤ upperQL φ x)
    (hxy : upperQL φ y = upperQL φ x) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality φ x y c := by
  apply (mamikonSegmentEquality_iff hφ x y hc).2
  rw [(lDomain φ).eq_on_segment_of_isMax (theorem8_3_8 hφ) hmax hxy hc, hxy]
  ring

/-- Corollary 8.5.8 in the bundled-triple vocabulary. -/
theorem upperQL_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : LTriple P.φ) : upperQL P.φ x ≤ upperQL P.φ (gerverTriple hP hbox) :=
  corollary8_5_8 hP hbox x.2

/-- Equality in the optimal upper bound forces zero first variation at Gerver's triple. -/
theorem gerver_dirDeriv_eq_zero_of_upperQL_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {x : LTriple P.φ}
    (hx : upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox)) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox) x = 0 :=
  (lDomain P.φ).dirDeriv_eq_zero_of_isMax (proposition8_2_1 (gm_φ_mem_Ioo hP hbox))
    (theorem8_3_8 (gm_φ_mem_Ioo hP hbox)) (upperQL_le_gerver hP hbox) hx

/-- Every competitor attaining Gerver's upper bound saturates the three Mamikon convexity
inequalities separately, for every combination parameter in `[0, 1]`. -/
theorem gerver_mamikonSegmentEquality {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {x : LTriple P.φ} (hx : upperQL P.φ x = upperQL P.φ (gerverTriple hP hbox))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    MamikonSegmentEquality P.φ (gerverTriple hP hbox) x c :=
  mamikonSegmentEquality_of_isMax (gm_φ_mem_Ioo hP hbox) (upperQL_le_gerver hP hbox) hx hc

/-- The canonical extension of a cap in `𝒦^i` to a triple in `𝓛`. -/
noncomputable def kiExtensionTriple {φ : ℝ} (hφ : φ ∈ Icc (0.039 : ℝ) 0.04)
    {K : Set (ℝ × ℝ)} (hK : IsKi K) : LTriple φ :=
  ⟨(⟨K, hK.1.2.1⟩, ⟨rightBody φ K, (theorem8_1_8 hφ hK).2.1⟩,
    ⟨leftBody φ K, (theorem8_1_8 hφ hK).2.2.1⟩), theorem8_1_8 hφ hK⟩

/-- If the sofa-area functional of a cap in `𝒦^i` attains Gerver's area, its canonical triple
attains Gerver's upper bound. This records equality in both bounding steps, rather than
assuming equality for the auxiliary functional. -/
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

/-- Necessary equality conditions for an area-maximizing cap in `𝒦^i`. Geometric rigidity
and the passage back to the original moving sofa are proved in `MovingSofaUniqueness/`. -/
theorem ki_maximizer_equality_conditions {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set (ℝ × ℝ)} (hK : IsKi K)
    (harea : sofaArea (π / 2) K = area (gerverSofa P)) :
    (lDomain P.φ).dirDeriv (upperQL P.φ) (gerverTriple hP hbox)
        (kiExtensionTriple hbox.1 hK) = 0 ∧
      ∀ c ∈ Icc (0 : ℝ) 1,
        MamikonSegmentEquality P.φ (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) c := by
  have hx := ki_upperQL_eq_gerver_of_sofaArea_eq hP hbox hK harea
  exact ⟨gerver_dirDeriv_eq_zero_of_upperQL_eq hP hbox hx,
    fun _ hc => gerver_mamikonSegmentEquality hP hbox hx hc⟩

end MovingSofaUniqueness

end

/-!
## The four cap Mamikon equalities imply the complete support kernel

The four scalar convexity gaps are nonnegative. Their sum can vanish only if
each vanishes. The preceding modules prove the displacement equality,
differentiability on regular arcs, the exact tangent kernel and the integrated
middle equation. Together they give the cap kernel used in Proposition 5 of the
uniqueness argument.
-/

section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaUniqueness

/-- Equality in the cap Mamikon functional yields all four support equations. -/
theorem capKernel_of_mamikonS_eq {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (hK₀ : IsKi K₀.1) (hK₁ : IsKi K₁.1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (heq : mamikonS φ (convexBodyComb c K₀ K₁).1 =
      (1 - c) * mamikonS φ K₀.1 + c * mamikonS φ K₁.1) :
    CapKernel φ (fun t => supp K₁.1 t - supp K₀.1 t) := by
  have hπ := pi_pos
  have hc' : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
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
  have e₁ : F₁ Kc = (1 - c) * F₁ K₀ + c * F₁ K₁ := by
    nlinarith only [heq, h₁, h₂, h₃, h₄]
  have e₂ : F₂ Kc = (1 - c) * F₂ K₀ + c * F₂ K₁ := by
    nlinarith only [heq, h₁, h₂, h₃, h₄]
  have e₃ : F₃ Kc = (1 - c) * F₃ K₀ + c * F₃ K₁ := by
    nlinarith only [heq, h₁, h₂, h₃, h₄]
  have e₄ : F₄ Kc = (1 - c) * F₄ K₀ + c * F₄ K₁ := by
    nlinarith only [heq, h₁, h₂, h₃, h₄]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have ht₀ : supp K₀.1 (π / 2) = 1 := hK₀.1.2.2.2.1
    have ht₁ : supp K₁.1 (π / 2) = 1 := hK₁.1.2.2.2.1
    rw [ht₀, ht₁, sub_self]
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

/-- The cap kernel (Proposition 5) in the bundled-triple vocabulary of the library. -/
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
## Recover caps and their niches as actual sets

These are geometric consequences of a support identity, not consequences of
area equality alone. In particular, no regular-closedness assumption on an
arbitrary competing sofa is introduced.
-/

section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- A right-angle cap is determined by its upper supports and the floor. -/
theorem mem_right_cap_iff {K : Set Plane} (hK : IsCap K (π / 2)) (p : Plane) :
    p ∈ K ↔ 0 ≤ p.2 ∧ ∀ t ∈ Icc (0 : ℝ) π, dot p (uvec t) ≤ supp K t := by
  constructor
  · intro hp
    exact ⟨(opt_cap_mem_strip hK hp).1,
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
      rw [he, hbottom, opt_uvec_three_pi_div_two]
      simpa [dot] using hfloor
    · rw [ht, hbottom, opt_uvec_three_pi_div_two]
      simpa [dot] using hfloor

/-- In a right-angle cap, the fan is the upper half-plane. The quadrant
inequalities remain strict; they have not been replaced by their closures. -/
theorem mem_right_niche_iff (K : Set Plane) (p : Plane) :
    p ∈ niche K (π / 2) ↔ 0 ≤ p.2 ∧ ∃ t ∈ Ioo (0 : ℝ) (π / 2),
      dot p (uvec t) < supp K t - 1 ∧
      dot p (vvec t) < supp K (t + π / 2) - 1 := by
  have hf : p ∈ fan (π / 2) ↔ 0 ≤ p.2 := by
    simp [fan, halfPlus, opt_uvec_pi_div_two, dot]
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

/-- The upper-support translation mode gives an exact membership equivalence. -/
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

/-- No assumption that either cap contains its niche is needed for covariance. -/
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

end MovingSofaUniqueness

end
