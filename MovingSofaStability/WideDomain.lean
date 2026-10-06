module

public import MovingSofaOptimality.Convex.ConvexDomain
public import MovingSofaUniqueness.Mamikon

/-!
# Baek's upper bound on the enlarged domain of triples

Baek's upper bound `𝒬` extended to the enlarged domain `T̄` of triples, on which the cap may have corners
(curvature atoms): the quadratic deficit identity, the Mamikon energies, the domain and its algebra of curves
of bounded variation, and the concavity of `𝒬` on `T̄`.

The sections below follow the steps of the proof.
-/

@[expose] public section
noncomputable section

/-!
## Quantitative deficit of a quadratic functional

The midpoint concavity gap, multiplied by four, is the quadratic energy along
an entire segment. At a global maximizer that energy is bounded by the
objective deficit, with constant one. The proof uses an explicit small segment
parameter, not an unformalized passage to a limit.

There is no assumption of strict concavity or uniqueness of auxiliary variables.
-/

section QuadraticDeficit

open Set
open MovingSofaOptimality

namespace MovingSofaStability

/-- Four times the midpoint concavity gap. For a quadratic functional this is
its negative quadratic part in the direction from `x` to `y`. -/
def segmentEnergy {V : Type} (D : ConvexDomain V) (Q : V → ℝ) (x y : V) : ℝ :=
  4 * (Q (D.comb (1 / 2) x y) - (Q x + Q y) / 2)

/-- The exact deficit is the negative first variation plus the segment energy.
For an affine-minus-squares functional this is its dual-slack certificate. -/
theorem deficit_eq_neg_dirDeriv_add_energy {V : Type} (D : ConvexDomain V)
    {Q : V → ℝ} (hq : D.IsQuadratic Q) (x y : V) :
    Q x - Q y = -D.dirDeriv Q x y + segmentEnergy D Q x y := by
  obtain ⟨g, hg, hfg⟩ := hq
  have hf : Q = fun z => g z z := funext hfg
  subst Q
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  rw [lemma7_1_4 D hg]
  unfold segmentEnergy
  beta_reduce
  rw [cvx_bilin_comb D hg x y hh]
  ring


end MovingSofaStability

end QuadraticDeficit

/-!
## Mamikon difference energies

These statements quantify Mamikon's theorem for two convex bodies and apply to
arbitrary convex bodies, without `InjCond1`. They use the square-integral and
displacement facts of `MamikonFoundation`, not the uniqueness proof's
`Rigidity` module.

The energy is half the integral of the difference of two tangent displacements
squared. It is not the Mamikon area of either body separately.
-/

section MamikonEnergy

open Real Set MeasureTheory Filter
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

section Measure

variable {X : Type*} [MeasurableSpace X]

/-- Nonnegativity does not need an integrability hypothesis. All applications
of identities between integrals below do supply integrability. -/
theorem halfSquareIntegral_nonneg (μ : Measure X) (f : X → ℝ) :
    0 ≤ halfSquareIntegral μ f := by
  unfold halfSquareIntegral
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg (f x))


end Measure

/-- The energy of the difference of tangent displacements on an open arc. -/
def displacementEnergy (a b : ℝ) (z : ConvexBodySet → ℝ → ℝ × ℝ)
    (K₀ K₁ : ConvexBodySet) : ℝ :=
  halfSquareIntegral (volume.restrict (Ioo a b))
    (fun t => displacement K₀.1 (z K₀) t - displacement K₁.1 (z K₁) t)

theorem displacementEnergy_nonneg (a b : ℝ)
    (z : ConvexBodySet → ℝ → ℝ × ℝ) (K₀ K₁ : ConvexBodySet) :
    0 ≤ displacementEnergy a b z K₀ K₁ :=
  halfSquareIntegral_nonneg _ _


section Arc

variable {a b : ℝ} (hab : a < b) (hb : b < a + π)
variable (z : ConvexBodySet → ℝ → ℝ × ℝ)
variable (hz : ∀ K, IsCBV (z K) a b)
variable (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)
-- The statements below do not mention these hypotheses, so they are included explicitly.
include hab hb hz hzl hlin

/-- Exact quantitative Mamikon convexity gap, including the endpoint parameters. -/
theorem mamikon_combo_energy (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      c * (1 - c) * displacementEnergy a b z K₀ K₁ := by
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
    rw [displacement_combo z hlin K₀ K₁ hc ⟨ht.1.le, ht.2.le⟩]
  rw [hcombo, mamikon_eq_halfSquareIntegral hab hb z hz hzl K₀,
    mamikon_eq_halfSquareIntegral hab hb z hz hzl K₁]
  have he := halfSquareIntegral_combo_gap μ c hf hg hfg
  change (1 - c) * halfSquareIntegral μ f + c * halfSquareIntegral μ g -
      halfSquareIntegral μ (fun t => (1 - c) * f t + c * g t) =
      c * (1 - c) * halfSquareIntegral μ (fun t => f t - g t)
  rw [he]
  unfold halfSquareIntegral
  ring


end Arc

end MovingSofaStability

end MamikonEnergy

/-!
## Quantitative energy bounds for Baek's existing triple domain

Unlike the generic algebraic results, the theorems below use the repository's
actual `upperQL`, Gerver parameters, and cap/niche area functional. Their domain
is the existing `LTriple`, whose cap lies in Ki.

This file does NOT claim the nonsmooth enlarged-domain theorem of note 05.
The midpoint energies are identified with displacement-square integrals by
`mamikon_midpoint_energy` term by term; here they are grouped as cap, right,
and left energies. The two nonnegative auxiliary energies can be discarded.
-/

section BaekDeficit

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- The reference value of the actual Q is the area of Gerver's sofa. -/
theorem gerver_upperQL_eq_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    upperQL P.φ (gerverTriple hP hbox) = area (gerverSofa P) := by
  change upperQ P.φ P.cap (rightBody P.φ P.cap) (leftBody P.φ P.cap) = _
  have h₁ := theorem8_4_6 hP hbox
  have h₂ := gm_sofaArea_cap hP hbox
  linarith


end MovingSofaStability

end BaekDeficit

/-!
## The enlarged nonsmooth triple domain

This is the domain of stability note 05: normalized right-angle caps, arbitrary
convex tail bodies, and the original linear wall constraints. No
curvature-density, injectivity, or area threshold is assumed.

The convex-domain construction and `wide_upperQ_decomposition` are proved here.
The further identity `upperP + mamikonS = affineCore` for all nonsmooth caps,
and the enlarged-domain first variation at Gerver, are separate obligations.
-/

section WideDomain

open Real Set
open scoped Pointwise
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The original wall constraints, with `IsCap` instead of `IsKi`. -/
def InWideL (φ : ℝ) (K B D : Set (ℝ × ℝ)) : Prop :=
  IsCap K (π / 2) ∧ IsConvexBody B ∧ IsConvexBody D ∧ B ⊆ K ∧ D ⊆ K ∧
    (∀ t ∈ Icc φ (π / 2), supp K t + supp B (π + t) ≤ 1) ∧
    supp K φ + supp B (π + φ) = 1 ∧ supp K (π / 2) + supp B (π + π / 2) = 1 ∧
    (∀ t ∈ Icc 0 (π / 2 - φ), supp K (π / 2 + t) + supp D (3 * π / 2 + t) ≤ 1) ∧
    supp K (π / 2 + 0) + supp D (3 * π / 2 + 0) = 1 ∧
    supp K (π / 2 + (π / 2 - φ)) + supp D (3 * π / 2 + (π / 2 - φ)) = 1

theorem inWideL_of_inL {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InL φ K B D) :
    InWideL φ K B D := ⟨h.1.1, h.2⟩

/-- Endpoint support identities require only the cap normalization and contacts. -/
theorem inWideL_supp {φ : ℝ} {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    supp B (3 * π / 2) = 0 ∧ supp D (3 * π / 2) = 0 ∧
      supp B (π + φ) = 1 - supp K φ ∧
      supp D (3 * π / 2 + (π / 2 - φ)) = 1 - supp K (π - φ) := by
  obtain ⟨hK, -, -, -, -, -, e1, e1', -, e2, e2'⟩ := h
  have hK2 : supp K (π / 2) = 1 := hK.2.2.2.1
  rw [add_zero, add_zero, hK2] at e2
  rw [hK2, show π + π / 2 = 3 * π / 2 by ring] at e1'
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at e2'
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Nonsmooth feasible triples are closed under componentwise Minkowski combinations. -/
theorem inWideL_comb {φ : ℝ} {K₁ B₁ D₁ K₂ B₂ D₂ : Set (ℝ × ℝ)}
    (h₁ : InWideL φ K₁ B₁ D₁) (h₂ : InWideL φ K₂ B₂ D₂)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    InWideL φ ((1 - c) • K₁ + c • K₂) ((1 - c) • B₁ + c • B₂)
      ((1 - c) • D₁ + c • D₂) := by
  obtain ⟨hK₁, hB₁, hD₁, hBK₁, hDK₁, i1, e1, e1', i2, e2, e2'⟩ := h₁
  obtain ⟨hK₂, hB₂, hD₂, hBK₂, hDK₂, j1, f1, f1', j2, f2, f2'⟩ := h₂
  have sK := supp_comb hK₁.2.1 hK₂.2.1 hc
  have sB := supp_comb hB₁ hB₂ hc
  have sD := supp_comb hD₁ hD₂ hc
  have hc0 := hc.1
  have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
  refine ⟨opt_comb_isCap hK₁ hK₂ hc, isConvexBody_comb hB₁ hB₂,
    isConvexBody_comb hD₁ hD₂,
    Set.add_subset_add (Set.smul_set_mono hBK₁) (Set.smul_set_mono hBK₂),
    Set.add_subset_add (Set.smul_set_mono hDK₁) (Set.smul_set_mono hDK₂),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [sK, sB]
    nlinarith [mul_le_mul_of_nonneg_left (i1 t ht) hc1,
      mul_le_mul_of_nonneg_left (j1 t ht) hc0]
  · rw [sK, sB]; linear_combination (1 - c) * e1 + c * f1
  · rw [sK, sB]; linear_combination (1 - c) * e1' + c * f1'
  · intro t ht
    rw [sK, sD]
    nlinarith [mul_le_mul_of_nonneg_left (i2 t ht) hc1,
      mul_le_mul_of_nonneg_left (j2 t ht) hc0]
  · rw [sK, sD]; linear_combination (1 - c) * e2 + c * f2
  · rw [sK, sD]; linear_combination (1 - c) * e2' + c * f2'

def WideTriple (φ : ℝ) : Type :=
  {x : ConvexBodySet × ConvexBodySet × ConvexBodySet //
    InWideL φ x.1.1 x.2.1.1 x.2.2.1}

open Classical in
noncomputable def WideTriple.comb {φ : ℝ} (c : ℝ) (x y : WideTriple φ) : WideTriple φ :=
  if hc : c ∈ Icc (0 : ℝ) 1 then
    ⟨(convexBodyComb c x.1.1 y.1.1, convexBodyComb c x.1.2.1 y.1.2.1,
      convexBodyComb c x.1.2.2 y.1.2.2), by
        simpa [convexBodyComb, hc] using inWideL_comb x.2 y.2 hc⟩
  else x

theorem wideTriple_embeds (φ : ℝ) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℝ E) (e : WideTriple φ → E),
      Function.Injective e ∧ ∀ c ∈ Icc (0 : ℝ) 1, ∀ x y,
        e (WideTriple.comb c x y) = (1 - c) • e x + c • e y := by
  obtain ⟨E, i1, i2, e, he, hlin⟩ := theorem7_1_1
  refine ⟨E × E × E, inferInstance, inferInstance,
    fun x => (e x.1.1, e x.1.2.1, e x.1.2.2), ?_, ?_⟩
  · intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    apply Subtype.ext
    exact Prod.ext (he h1) (Prod.ext (he h2) (he h3))
  · intro c hc x y
    simp only [WideTriple.comb, hc, ↓reduceDIte]
    rw [hlin c hc, hlin c hc, hlin c hc]
    simp only [Prod.smul_mk, Prod.mk_add_mk]

noncomputable def wideDomain (φ : ℝ) : ConvexDomain (WideTriple φ) where
  comb := WideTriple.comb
  embeds := wideTriple_embeds φ

/-- The enlarged functional retains the original curve-area definition. -/
def wideUpperQ (φ : ℝ) (x : WideTriple φ) : ℝ :=
  upperQ φ x.1.1.1 x.1.2.1.1 x.1.2.2.1

def toWideTriple {φ : ℝ} (x : LTriple φ) : WideTriple φ :=
  ⟨x.1, inWideL_of_inL x.2⟩

/-- The tail decomposition extends to the enlarged domain. This proof is the
source's segment/arc argument with the weaker, sufficient endpoint hypotheses. -/
theorem wide_upperQ_decomposition {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K B D : Set (ℝ × ℝ)} (h : InWideL φ K B D) :
    upperQ φ K B D = upperP φ K - mamikonR φ B - mamikonL φ D := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  obtain ⟨hB3, hD3, hBa, hDb⟩ := inWideL_supp h
  obtain ⟨-, hBcb, hDcb, -⟩ := h
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have tR1 : tangentParam B (3 * π / 2) (π + φ) = wRight φ K := by
    simp only [tangentParam, show π + φ < 3 * π / 2 by linarith, ↓reduceIte]
    exact opt_vint_right_eq ⟨hφ0, by linarith⟩ hBa hB3
  have tR2 : tangentParam B (3 * π / 2) (3 * π / 2) = vminus B (3 * π / 2) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have tL1 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2) = zLeft φ K := by
    simp only [tangentParam, show 3 * π / 2 < 3 * π / 2 + (π / 2 - φ) by linarith,
      ↓reduceIte]
    exact opt_vint_left_eq hD3 hDb
  have tL2 : tangentParam D (3 * π / 2 + (π / 2 - φ)) (3 * π / 2 + (π / 2 - φ)) =
      vminus D (3 * π / 2 + (π / 2 - φ)) := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have hlR := (theorem8_3_1 hBcb (t := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) le_rfl).2.2
  have hlL := (theorem8_3_1 hDcb (t := 3 * π / 2 + (π / 2 - φ)) (a := 3 * π / 2)
    (b := 3 * π / 2 + (π / 2 - φ)) (by linarith) (by linarith) le_rfl).2.2
  rw [tR1, tR2] at hlR
  rw [tL1, tL2] at hlL
  have z1 := segArea_of_snd_eq_zero (p := wRight φ K) rfl
    (opt_snd_vminus_three_pi_div_two hB3)
  have z2 := segArea_of_snd_eq_zero (opt_snd_vplus_three_pi_div_two hD3)
    (q := zLeft φ K) (by rw [opt_zLeft_eq])
  have z3 := segArea_self (vminus B (3 * π / 2))
  have z4 := segArea_self (vminus D (3 * π / 2 + (π / 2 - φ)))
  obtain ⟨hXB, hWl, hxR⟩ := opt_right_mem_line hc.ne' hBa
  obtain ⟨hYD, hZl, hxL⟩ := opt_left_mem_line hc.ne' hDb
  have c1 := segArea_add_of_mem_line hxR hXB hWl
  have c2 := segArea_add_of_mem_line hZl hYD hxL
  simp only [upperQ, upperP, mamikonR, mamikonL, mamikon, hlR, hlL,
    tR1, tR2, tL1, tL2]
  simp only [xB, yD] at c1 c2 ⊢
  linarith

end MovingSofaStability

end WideDomain

/-!
## Curve-area affinity without differentiating the competitor

The difference between the outer and inner corner curves is the fixed curve
`uvec + vvec`. The difference of their quadratic curve areas is therefore affine
on the entire convex-body domain.

This replaces the C1 calculation of the first part of source Lemma 8.3.6 by
an argument in the real vector space of continuous bounded-variation curves.
It applies to nonsmooth competing caps and does not assume Ki.
-/

section CBVAlgebra

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- Continuous bounded-variation curves form a genuine real vector subspace. -/
def cbvSubmodule (a b : ℝ) : Submodule ℝ (ℝ → ℝ × ℝ) where
  carrier := {x | IsCBV x a b}
  zero_mem' := by
    refine ⟨continuous_const.continuousOn, ?_⟩
    simp [BoundedVariationOn, eVariationOn]
  add_mem' := by
    intro x y hx hy
    exact ⟨hx.1.add hy.1, boundedVariationOn_add hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨hx.1.const_smul c, cvx_bv_const_smul hx.2 c⟩

abbrev CBVSpace (a b : ℝ) := ↥(cbvSubmodule a b)

/-- The existing curve bilinear form on the newly packaged vector space. -/
theorem cbvSpace_bilinear {a b : ℝ} (hab : a ≤ b) :
    (vectorDomain (CBVSpace a b)).IsConvexBilinear
      (vectorDomain (CBVSpace a b)) realDomain
      (fun x y => curveBilin x.1 y.1 a b) := by
  constructor
  · intro x c hc y z
    change curveBilin x.1 ((1 - c) • y.1 + c • z.1) a b =
      (1 - c) * curveBilin x.1 y.1 a b + c * curveBilin x.1 z.1 a b
    exact cvx_curveBilin_comb_right hab x.2.1 y.2 z.2
  · intro y c hc x z
    change curveBilin ((1 - c) • x.1 + c • z.1) y.1 a b =
      (1 - c) * curveBilin x.1 y.1 a b + c * curveBilin z.1 y.1 a b
    exact cvx_curveBilin_comb_left y.1 x.2.1 z.2.1 c

/-- A fixed curve offset changes quadratic curve area by an affine functional. -/
theorem shifted_curveArea_affine {a b : ℝ} (hab : a ≤ b) (w : CBVSpace a b) :
    (vectorDomain (CBVSpace a b)).IsConvexLinear realDomain
      (fun x => curveArea (x + w).1 a b - curveArea x.1 a b) := by
  have h := lemma7_1_6 (cbvSpace_bilinear hab) w w
  intro c hc x y
  have he := h c hc x y
  change curveArea ((1 - c) • x + c • y).1 a b -
      curveArea ((1 - c) • x + c • y + w).1 a b =
    (1 - c) * (curveArea x.1 a b - curveArea (x + w).1 a b) +
      c * (curveArea y.1 a b - curveArea (y + w).1 a b) at he
  change curveArea ((1 - c) • x + c • y + w).1 a b -
      curveArea ((1 - c) • x + c • y).1 a b =
    (1 - c) * (curveArea (x + w).1 a b - curveArea x.1 a b) +
      c * (curveArea (y + w).1 a b - curveArea y.1 a b)
  linarith

/-- Generalized source Lemma 8.3.6(1), with only convex-body hypotheses. -/
theorem outer_inner_area_affine {a b c : ℝ} (hab : a ≤ b)
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    curveArea (outerCorner ((1 - c) • K₁ + c • K₂)) a b -
      curveArea (innerCorner ((1 - c) • K₁ + c • K₂)) a b =
      (1 - c) * (curveArea (outerCorner K₁) a b - curveArea (innerCorner K₁) a b) +
      c * (curveArea (outerCorner K₂) a b - curveArea (innerCorner K₂) a b) := by
  let K := (1 - c) • K₁ + c • K₂
  have hK : IsConvexBody K := isConvexBody_comb h₁ h₂
  let x : CBVSpace a b := ⟨innerCorner K₁, opt_innerCorner_cbv h₁ a b⟩
  let y : CBVSpace a b := ⟨innerCorner K₂, opt_innerCorner_cbv h₂ a b⟩
  let z : CBVSpace a b := ⟨innerCorner K, opt_innerCorner_cbv hK a b⟩
  let w : CBVSpace a b :=
    (⟨outerCorner K₁, opt_outerCorner_cbv h₁ a b⟩ : CBVSpace a b) - x
  have hz : z = (1 - c) • x + c • y := by
    apply Subtype.ext
    exact opt_innerCorner_comb h₁ h₂ hc
  have hxw : (x + w).1 = outerCorner K₁ := by
    funext t
    change innerCorner K₁ t + (outerCorner K₁ t - innerCorner K₁ t) = _
    abel
  have hyw : (y + w).1 = outerCorner K₂ := by
    funext t
    change innerCorner K₂ t + (outerCorner K₁ t - innerCorner K₁ t) = _
    rw [opt_outer_eq_inner_add K₁, opt_outer_eq_inner_add K₂]
    abel
  have hzw : (z + w).1 = outerCorner K := by
    funext t
    change innerCorner K t + (outerCorner K₁ t - innerCorner K₁ t) = _
    rw [opt_outer_eq_inner_add K₁, opt_outer_eq_inner_add K]
    abel
  have he := shifted_curveArea_affine hab w c hc x y
  change curveArea ((1 - c) • x + c • y + w).1 a b -
      curveArea ((1 - c) • x + c • y).1 a b =
    (1 - c) * (curveArea (x + w).1 a b - curveArea x.1 a b) +
      c * (curveArea (y + w).1 a b - curveArea y.1 a b) at he
  rw [← hz, hxw, hyw, hzw] at he
  exact he

end MovingSofaStability

end CBVAlgebra

/-!
## Cap area split at the four Mamikon arcs, retaining all atoms

In a nonsmooth cap, atoms at 0, phi, pi/2-phi and pi cannot be discarded. The
five edge segments below account for those atoms and the top edge. This is the
missing bookkeeping in a naive reuse of the Ki-only source Lemma 8.3.5.
-/

section ArcAtoms

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Signed area of the supporting face traversed counterclockwise. -/
def edgeArea (K : Set (ℝ × ℝ)) (t : ℝ) : ℝ :=
  segArea (vminus K t) (vplus K t)

/-- A curvature atom contributes exactly its supporting-face area. -/
theorem edgeArea_eq_atom {K : Set (ℝ × ℝ)} (hK : IsConvexBody K) (t : ℝ) :
    edgeArea K t = (1 / 2) * (sigma K).real {t} * supp K t := by
  have hv := (proposition2_1_2 hK t).2
  have hcross : cross (vminus K t) (vvec t) = supp K t := by
    simpa [cross, vvec, dot, uvec] using dot_vminus_uvec K t
  unfold edgeArea segArea
  rw [hv, cross_add_right, cross_self, cross_smul_right, hcross]
  simp only [zero_add, sigmaAt, measureReal_def]
  ring

/-- Right-endpoint atoms in a support integral. -/
theorem support_integral_Ioc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {a b : ℝ} (hab : a < b) :
    (∫ t in Ioc a b, supp K t ∂(sigma K)) =
      (∫ t in Ioo a b, supp K t ∂(sigma K)) + (sigma K).real {b} * supp K b := by
  have hf := hK.continuous_supp
  have hint : IntegrableOn (supp K) (Icc a b) (sigma K) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint : IntegrableOn (supp K) ({b} : Set ℝ) (sigma K) :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨hab.le, le_rfl⟩)
  rw [← Ioo_union_right hab,
    setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ioo_subset_Icc_self) hpoint,
    integral_singleton, smul_eq_mul]

/-- Left-endpoint atoms in a support integral. -/
theorem support_integral_Icc {K : Set (ℝ × ℝ)} (hK : IsConvexBody K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, supp K t ∂(sigma K)) =
      (∫ t in Ioc a b, supp K t ∂(sigma K)) + (sigma K).real {a} * supp K a := by
  have hf := hK.continuous_supp
  have hint : IntegrableOn (supp K) (Icc a b) (sigma K) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint : IntegrableOn (supp K) ({a} : Set ℝ) (sigma K) :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨le_rfl, hab⟩)
  rw [← Ioc_union_left hab,
    setIntegral_union (by simp) (measurableSet_singleton _)
      (hint.mono_set Ioc_subset_Icc_self) hpoint,
    integral_singleton, smul_eq_mul]

/-- The two half-arcs plus their three endpoint faces give the cap's area. -/
theorem cap_area_two_arcs {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    area K = convexCurveArea K 0 (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K (π / 2) + edgeArea K π := by
  have hcb := hK.2.1
  have hf := hcb.continuous_supp
  have hv : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  have hvπ : π / 2 < π := by linarith [pi_pos]
  have hup : (∫ t in Icc 0 π, supp K t ∂(sigma K)) =
      (∫ t in Ioo 0 (π / 2), supp K t ∂(sigma K)) +
      (∫ t in Ioo (π / 2) π, supp K t ∂(sigma K)) +
      (sigma K).real {0} * supp K 0 +
      (sigma K).real {π / 2} * supp K (π / 2) +
      (sigma K).real {π} * supp K π := by
    rw [support_integral_Icc hcb pi_pos.le,
      ← intervalIntegral.integral_of_le pi_pos.le,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 (π / 2)) (hf.intervalIntegrable (π / 2) π),
      intervalIntegral.integral_of_le hv.le,
      intervalIntegral.integral_of_le hvπ.le,
      support_integral_Ioc hcb hv, support_integral_Ioc hcb hvπ]
    ring
  rw [theorem7_1_3 hcb, opt_Ico_eq_Icc hK hf hK.2.2.2.2.2.1, hup]
  rw [edgeArea_eq_atom hcb, edgeArea_eq_atom hcb, edgeArea_eq_atom hcb]
  unfold convexCurveArea
  ring

/-- Four cap Mamikon arcs plus all five supporting faces. No atom is omitted. -/
theorem cap_area_four_arcs {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    area K = convexCurveArea K 0 φ + convexCurveArea K φ (π / 2 - φ) +
      convexCurveArea K (π / 2 - φ) (π / 2) + convexCurveArea K (π / 2) π +
      edgeArea K 0 + edgeArea K φ + edgeArea K (π / 2 - φ) +
      edgeArea K (π / 2) + edgeArea K π := by
  have hcb := hK.2.1
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have c1 := (lemma7_3_4 hcb hφ0 (by linarith : φ < π / 2)
    (by linarith)).2.2.2
  have c2 := (lemma7_3_4 hcb (by linarith : φ < π / 2 - φ)
    (by linarith : π / 2 - φ < π / 2) (by linarith)).2.2.2
  have ha := cap_area_two_arcs hK
  unfold edgeArea at *
  linarith

/-- A useful three-point collinearity identity, with a face inserted between
its two endpoints rather than identified with a point. -/
theorem segArea_join_face {t h : ℝ} {z₁ pl pr z₂ : ℝ × ℝ}
    (hz₁ : z₁ ∈ line t h) (hpl : pl ∈ line t h)
    (hpr : pr ∈ line t h) (hz₂ : z₂ ∈ line t h) :
    segArea z₁ pl + segArea pr z₂ + segArea pl pr = segArea z₁ z₂ := by
  have h1 := segArea_add_of_mem_line hz₁ hpl hpr
  have h2 := segArea_add_of_mem_line hz₁ hpr hz₂
  linarith

end MovingSofaStability

end ArcAtoms

/-!
## Atom-aware cap Mamikon bookkeeping

Every supporting-face contribution is retained and then cancelled against its
adjacent Mamikon connector segments. In particular, no equality of `vminus` and
`vplus` is assumed at a cut or endpoint.

The result writes `mamikonS + upperP` as a sum of affine terms. Unlike the
source Ki-only proof, the displayed boundary term has no vertex coordinates:
the top face cancels those as well.
-/

section NonsmoothBookkeeping

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- The boundary part left after all five supporting faces have been joined. -/
def capAffineBoundary (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  supp K 0 + supp K π + (2 * sin φ - supp K φ - supp K (π - φ)) / (2 * cos φ)

def rightSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
    segArea (wRight φ K) (xRight φ K)

def leftSegmentRemainder (φ : ℝ) (K : Set (ℝ × ℝ)) : ℝ :=
  segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2))
      (outerCorner K (π / 2 - φ)) -
    segArea (zLeft φ K) (xLeft φ K)

/-- Generalized Mamikon bookkeeping for arbitrary normalized right-angle caps. -/
theorem mamikonS_add_upperP_nonsmooth {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K : Set (ℝ × ℝ)} (hK : IsCap K (π / 2)) :
    mamikonS φ K + upperP φ K = capAffineBoundary φ K + rightSegmentRemainder φ K +
      (curveArea (outerCorner K) φ (π / 2 - φ) -
        curveArea (innerCorner K) φ (π / 2 - φ)) - leftSegmentRemainder φ K := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ0, by linarith⟩
  have hcb := hK.2.1
  have htop : supp K (π / 2) = 1 := hK.2.2.2.1
  have hc : cos φ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, hφ2.2⟩).ne'
  let b : ℝ := π / 2 - φ
  let T : ℝ := π / 2 + (π / 2 - φ)
  have hb : b = π / 2 - φ := rfl
  have hT : T = π / 2 + (π / 2 - φ) := rfl
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hbv : b < π / 2 := by dsimp [b]; linarith
  have hvT : π / 2 < T := by dsimp [T]; linarith
  have c1 := (theorem8_3_1 hcb (t := π / 2) (a := 0) (b := φ)
    (by linarith) hφ0.le (by linarith)).2.2
  have c3 := (theorem8_3_1 hcb (t := T) (a := b) (b := π / 2)
    (by dsimp [T, b]; linarith) hbv.le hvT.le).2.2
  have c4 := (theorem8_3_1 hcb (t := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) le_rfl).2.2
  have l10 : tangentParam K (π / 2) 0 = (supp K 0, 1) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte,
      vint, htop, sub_zero, cos_pi_div_two, sin_pi_div_two, uvec_zero, vvec_zero]
    ext <;> simp
  have l3b : tangentParam K T b = outerCorner K b := by
    change tangentParam K (π / 2 + b) b = _
    rw [show π / 2 + b = b + π / 2 by ring]
    simp only [tangentParam, show b < b + π / 2 by linarith, ↓reduceIte, vint,
      show b + π / 2 - b = π / 2 by ring, cos_pi_div_two, sin_pi_div_two,
      mul_zero, sub_zero, div_one, proposition2_2_2_outerCorner]
  have l4v : tangentParam K π (π / 2) = (-supp K π, 1) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte, vint, htop,
      show π - π / 2 = π / 2 by ring, cos_pi_div_two, sin_pi_div_two,
      mul_zero, sub_zero, div_one, uvec_pi_div_two, vvec_pi_div_two]
    ext <;> simp
  have l4π : tangentParam K π π = vminus K π := by
    simp only [tangentParam, lt_irrefl, ↓reduceIte]
  have l10mem : tangentParam K (π / 2) 0 ∈ line 0 (supp K 0) := by
    simp only [tangentParam, show (0 : ℝ) < π / 2 by linarith, ↓reduceIte]
    exact vint_mem_line_left K 0 (π / 2)
  have l1φmem : tangentParam K (π / 2) φ ∈ line φ (supp K φ) := by
    simp only [tangentParam, hφ2.2, ↓reduceIte]
    exact vint_mem_line_left K φ (π / 2)
  have l3vmem : tangentParam K T (π / 2) ∈ line (π / 2) (supp K (π / 2)) := by
    simp only [tangentParam, hvT, ↓reduceIte]
    exact vint_mem_line_left K (π / 2) T
  have l4vmem : tangentParam K π (π / 2) ∈ line (π / 2) (supp K (π / 2)) := by
    simp only [tangentParam, show π / 2 < π by linarith, ↓reduceIte]
    exact vint_mem_line_left K (π / 2) π
  have l4vleft : tangentParam K π (π / 2) ∈ line π (supp K π) := by
    rw [l4v]
    simp [line, dot, uvec]
  have e0 : edgeArea K 0 + segArea (vplus K 0) (tangentParam K (π / 2) 0) =
      supp K 0 / 2 := by
    calc
      _ = segArea (vminus K 0) (tangentParam K (π / 2) 0) :=
        segArea_add_of_mem_line (dot_vminus_uvec K 0) (dot_vplus_uvec K 0) l10mem
      _ = _ := by
        rw [(inj_cap_consecutive hK).1, l10]
        simp only [segArea, cross]
        ring
  have eφ : segArea (tangentParam K (π / 2) φ) (vminus K φ) +
      segArea (vplus K φ) (outerCorner K φ) + edgeArea K φ =
      segArea (tangentParam K (π / 2) φ) (outerCorner K φ) :=
    segArea_join_face l1φmem (dot_vminus_uvec K φ) (dot_vplus_uvec K φ)
      (inj_dot_outerCorner_uvec K φ)
  have eb : segArea (outerCorner K b) (vminus K b) +
      segArea (vplus K b) (outerCorner K b) + edgeArea K b = 0 := by
    have he := segArea_join_face (inj_dot_outerCorner_uvec K b)
      (dot_vminus_uvec K b) (dot_vplus_uvec K b) (inj_dot_outerCorner_uvec K b)
    rw [segArea_self] at he
    exact he
  have ev : segArea (tangentParam K T (π / 2)) (vminus K (π / 2)) +
      segArea (vplus K (π / 2)) (tangentParam K π (π / 2)) + edgeArea K (π / 2) =
      segArea (tangentParam K T (π / 2)) (tangentParam K π (π / 2)) :=
    segArea_join_face l3vmem (dot_vminus_uvec K (π / 2))
      (dot_vplus_uvec K (π / 2)) l4vmem
  have eπ : segArea (tangentParam K π (π / 2)) (vminus K π) + edgeArea K π =
      supp K π / 2 := by
    calc
      _ = segArea (tangentParam K π (π / 2)) (vplus K π) :=
        segArea_add_of_mem_line l4vleft (dot_vminus_uvec K π) (dot_vplus_uvec K π)
      _ = _ := by
        rw [l4v, opt_cap_vplus_pi hK]
        simp only [segArea, cross]
        ring
  have hboundary : supp K 0 / 2 +
      segArea (tangentParam K (π / 2) 0) (tangentParam K (π / 2) φ) +
      segArea (tangentParam K T (π / 2)) (tangentParam K π (π / 2)) + supp K π / 2 =
      capAffineBoundary φ K := by
    rw [l10, l4v, opt_tangent_right_eq hφ2 htop]
    change supp K 0 / 2 +
      segArea (supp K 0, 1) (wRight φ K + ((1 - sin φ) / cos φ, 1)) +
      segArea (tangentParam K (π / 2 + (π / 2 - φ)) (π / 2)) (-supp K π, 1) +
      supp K π / 2 = _
    rw [opt_tangent_left_eq hφ2 htop, opt_wRight_eq, opt_zLeft_eq]
    simp only [capAffineBoundary, segArea, cross, Prod.fst_add, Prod.snd_add]
    field_simp [hc]
    ring
  have harea := cap_area_four_arcs hφ hK
  have swR := segArea_swap (xRight φ K) (wRight φ K)
  have swL := segArea_swap (outerCorner K b) (tangentParam K T (π / 2))
  change mamikonS φ K + upperP φ K = capAffineBoundary φ K +
      (segArea (tangentParam K (π / 2) φ) (outerCorner K φ) -
        segArea (wRight φ K) (xRight φ K)) +
      (curveArea (outerCorner K) φ b - curveArea (innerCorner K) φ b) -
      (segArea (tangentParam K T (π / 2)) (outerCorner K b) -
        segArea (zLeft φ K) (xLeft φ K))
  simp only [mamikonS, mamikon, upperP]
  change _ = _ at harea
  simp only [← hb] at *
  rw [c1, c3, c4, l3b, l4π]
  simp only [segArea_self]
  linarith only [harea, e0, eφ, eb, ev, eπ, hboundary, swR, swL]

end MovingSofaStability

end NonsmoothBookkeeping

/-!
## The affine cap remainder on all normalized caps

The atom-aware decomposition and the bounded-variation curve argument remove all
Ki assumptions from the affine part of Q.
-/

section NonsmoothAffinity

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- The joined boundary expression is affine even when supporting faces have length. -/
theorem capAffineBoundary_comb (φ : ℝ) {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    capAffineBoundary φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * capAffineBoundary φ K₁ + c * capAffineBoundary φ K₂ := by
  simp only [capAffineBoundary, supp_comb h₁ h₂ hc]
  ring

/-- Source Lemma 8.3.6(2) uses the top support, but not cap injectivity. -/
theorem rightSegmentRemainder_comb {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    rightSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * rightSegmentRemainder φ K₁ + c * rightSegmentRemainder φ K₂ := by
  have hm := opt_comb_isCap h₁ h₂ hc
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  simp only [rightSegmentRemainder]
  rw [opt_tangent_right_eq hφ hm.2.2.2.1,
    opt_tangent_right_eq hφ h₁.2.2.2.1, opt_tangent_right_eq hφ h₂.2.2.2.1,
    opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
    opt_wRight_comb hcb₁ hcb₂ hc, xRight, xRight, xRight,
    opt_innerCorner_comb hcb₁ hcb₂ hc]
  simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The left segment term is likewise affine for all normalized caps. -/
theorem leftSegmentRemainder_comb {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    leftSegmentRemainder φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * leftSegmentRemainder φ K₁ + c * leftSegmentRemainder φ K₂ := by
  have hm := opt_comb_isCap h₁ h₂ hc
  have hcb₁ := h₁.2.1
  have hcb₂ := h₂.2.1
  simp only [leftSegmentRemainder]
  rw [opt_tangent_left_eq hφ hm.2.2.2.1,
    opt_tangent_left_eq hφ h₁.2.2.2.1, opt_tangent_left_eq hφ h₂.2.2.2.1,
    opt_outer_eq_inner_add, opt_outer_eq_inner_add, opt_outer_eq_inner_add,
    opt_zLeft_comb hcb₁ hcb₂ hc, xLeft, xLeft, xLeft,
    opt_innerCorner_comb hcb₁ hcb₂ hc]
  simp only [segArea, cross, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The nonsmooth extension of source Lemma 8.3.7. No density or arm condition appears. -/
theorem cap_mamikon_upperP_affine {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCap K₁ (π / 2)) (h₂ : IsCap K₂ (π / 2))
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    mamikonS φ ((1 - c) • K₁ + c • K₂) + upperP φ ((1 - c) • K₁ + c • K₂) =
      (1 - c) * (mamikonS φ K₁ + upperP φ K₁) +
      c * (mamikonS φ K₂ + upperP φ K₂) := by
  have hpi := pi_pos
  have hφ2 : φ ∈ Ioo 0 (π / 2) := ⟨hφ.1, by linarith [hφ.2]⟩
  have hM := opt_comb_isCap h₁ h₂ hc
  have hboundary := capAffineBoundary_comb φ h₁.2.1 h₂.2.1 hc
  have hright := rightSegmentRemainder_comb hφ2 h₁ h₂ hc
  have hleft := leftSegmentRemainder_comb hφ2 h₁ h₂ hc
  have hcurve := outer_inner_area_affine
    (a := φ) (b := π / 2 - φ) (by linarith [hφ.2]) h₁.2.1 h₂.2.1 hc
  rw [mamikonS_add_upperP_nonsmooth hφ hM,
    mamikonS_add_upperP_nonsmooth hφ h₁, mamikonS_add_upperP_nonsmooth hφ h₂]
  linarith

/-- The cap Mamikon sum was convex on all convex bodies even before restricting to Ki. -/
theorem mamikonS_convex_all {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    convexBodyDomain.IsConvexFun (fun K => mamikonS φ K.1) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have c1 := (opt_mamikon_tangent (t := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith)).2
  have c2 := (opt_mamikon_outer (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith)).2
  have c3 := (opt_mamikon_tangent (t := π / 2 + (π / 2 - φ))
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)).2
  have c4 := (opt_mamikon_tangent (t := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl).2
  exact opt_isConvexFun_add (opt_isConvexFun_add (opt_isConvexFun_add c1 c2) c3) c4

end MovingSofaStability

end NonsmoothAffinity

/-!
## Baek's Q is quadratic and concave on the enlarged domain

This is an extension of the functional's algebraic properties, not yet its
geometric upper bound on arbitrary near-maximizers. The enlarged-domain first
variation at Gerver is a separate dependency.
-/

section WideConcavity

open Real Set
open scoped Pointwise
open MovingSofaOptimality

namespace MovingSofaStability

/-- Projection to the cap preserves convex combinations. -/
theorem wide_projK_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.1) := by
  intro c hc x y
  simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

theorem wide_projB_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.2.1) := by
  intro c hc x y
  simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

theorem wide_projD_linear (φ : ℝ) :
    (wideDomain φ).IsConvexLinear convexBodyDomain (fun x : WideTriple φ => x.1.2.2) := by
  intro c hc x y
  simp only [wideDomain, convexBodyDomain, WideTriple.comb, hc, ↓reduceDIte]

/-- The original six-term curve-area functional is quadratic on nonsmooth triples. -/
theorem wideUpperQ_quadratic {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (wideDomain φ).IsQuadratic (wideUpperQ φ) := by
  have hpi := pi_pos
  obtain ⟨hφ0, hφ4⟩ := hφ
  have t1 : (wideDomain φ).IsQuadratic (fun x => area x.1.1.1) :=
    opt_isQuadratic_comp (wide_projK_linear φ) theorem7_1_3_quadratic
  have t2 : (wideDomain φ).IsQuadratic
      (fun x => convexCurveArea x.1.2.2.1 (3 * π / 2) (3 * π / 2 + (π / 2 - φ))) :=
    opt_isQuadratic_comp (wide_projD_linear φ) theorem7_3_2_quadratic
  have t3 : (wideDomain φ).IsQuadratic
      (fun x => segArea (yD φ x.1.2.2.1) (xLeft φ x.1.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.2.2)
        (g := fun K : ConvexBodySet => vminus K.1 (3 * π / 2 + (π / 2 - φ)))
        (wide_projD_linear φ) (opt_vminus_linear _))
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 (π / 2 - φ))
        (wide_projK_linear φ) (opt_innerCorner_linear _))
  have t4 : (wideDomain φ).IsQuadratic
      (fun x => curveArea (innerCorner x.1.1.1) φ (π / 2 - φ)) :=
    opt_isQuadratic_comp
      (opt_isConvexLinear_comp (wide_projK_linear φ) (opt_innerCBV_linear φ (π / 2 - φ)))
      (proposition7_2_2 (by linarith))
  have t5 : (wideDomain φ).IsQuadratic
      (fun x => segArea (xRight φ x.1.1.1) (xB φ x.1.2.1.1)) :=
    opt_isQuadratic_segArea
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.1)
        (g := fun K : ConvexBodySet => innerCorner K.1 φ)
        (wide_projK_linear φ) (opt_innerCorner_linear _))
      (opt_isConvexLinear_comp (f := fun x : WideTriple φ => x.1.2.1)
        (g := fun K : ConvexBodySet => vplus K.1 (π + φ))
        (wide_projB_linear φ) (opt_vplus_linear _))
  have t6 : (wideDomain φ).IsQuadratic
      (fun x => convexCurveArea x.1.2.1.1 (π + φ) (3 * π / 2)) :=
    opt_isQuadratic_comp (wide_projB_linear φ) theorem7_3_2_quadratic
  exact opt_isQuadratic_add (opt_isQuadratic_add (opt_isQuadratic_sub
    (opt_isQuadratic_add (opt_isQuadratic_add t1 t2) t3) t4) t5) t6

/-- Set-level concavity, with cap regularity nowhere assumed. -/
theorem wide_upperQ_concave_sets {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    {K₁ B₁ D₁ K₂ B₂ D₂ : Set (ℝ × ℝ)}
    (h₁ : InWideL φ K₁ B₁ D₁) (h₂ : InWideL φ K₂ B₂ D₂)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * upperQ φ K₁ B₁ D₁ + c * upperQ φ K₂ B₂ D₂ ≤
      upperQ φ ((1 - c) • K₁ + c • K₂) ((1 - c) • B₁ + c • B₂)
        ((1 - c) • D₁ + c • D₂) := by
  have hM := inWideL_comb h₁ h₂ hc
  have hlin := cap_mamikon_upperP_affine hφ h₁.1 h₂.1 hc
  let k₁ : ConvexBodySet := ⟨K₁, h₁.1.2.1⟩
  let k₂ : ConvexBodySet := ⟨K₂, h₂.1.2.1⟩
  let b₁ : ConvexBodySet := ⟨B₁, h₁.2.1⟩
  let b₂ : ConvexBodySet := ⟨B₂, h₂.2.1⟩
  let d₁ : ConvexBodySet := ⟨D₁, h₁.2.2.1⟩
  let d₂ : ConvexBodySet := ⟨D₂, h₂.2.2.1⟩
  have hS := mamikonS_convex_all hφ k₁ k₂ c hc
  obtain ⟨-, -, -, cR, -, cL⟩ := lemma8_3_3 hφ
  have hR := cR b₁ b₂ c hc
  have hL := cL d₁ d₂ c hc
  change mamikonS φ (convexBodyComb c k₁ k₂).1 ≤
    (1 - c) * mamikonS φ K₁ + c * mamikonS φ K₂ at hS
  change mamikonR φ (convexBodyComb c b₁ b₂).1 ≤
    (1 - c) * mamikonR φ B₁ + c * mamikonR φ B₂ at hR
  change mamikonL φ (convexBodyComb c d₁ d₂).1 ≤
    (1 - c) * mamikonL φ D₁ + c * mamikonL φ D₂ at hL
  rw [cvx_convexBodyComb_val hc] at hS hR hL
  rw [wide_upperQ_decomposition hφ h₁, wide_upperQ_decomposition hφ h₂,
    wide_upperQ_decomposition hφ hM]
  linarith

/-- The complete enlarged-domain concavity theorem. -/
theorem wideUpperQ_concave {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) :
    (wideDomain φ).IsConcave (wideUpperQ φ) := by
  intro x y c hc
  have h := wide_upperQ_concave_sets hφ x.2 y.2 hc
  simpa [wideUpperQ, wideDomain, WideTriple.comb, hc, convexBodyComb] using h

/-- A first-variation certificate is sufficient on the enlarged domain.
The separate task is proving this derivative sign at Gerver for all wide triples. -/
theorem wide_maximum_iff_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x₀ : WideTriple φ) :
    (∀ x, wideUpperQ φ x ≤ wideUpperQ φ x₀) ↔
      ∀ x, (wideDomain φ).dirDeriv (wideUpperQ φ) x₀ x ≤ 0 :=
  theorem7_1_5 (wideDomain φ) (wideUpperQ_quadratic hφ) (wideUpperQ_concave hφ) x₀

end MovingSofaStability

end WideConcavity

/-!
## Mixed-area first variation without atom-free endpoints

The source mixed-area symmetry argument removed the atoms at 0 and 2*pi using
Ki. Here those atoms are retained: periodicity makes their endpoint
contributions equal. The integration-by-parts theorem already applies to
arbitrary convex bodies.
-/

section MixedArea

open Real Set MeasureTheory
open MovingSofaOptimality

namespace MovingSofaStability

/-- Swapping the included endpoint of an interval preserves the integral when
the two singleton contributions agree. Atoms need not vanish. -/
theorem integral_Ico_eq_Ioc_of_endpoint_balance (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : Continuous f) (he : μ.real {a} * f a = μ.real {b} * f b) :
    (∫ t in Ico a b, f t ∂μ) = ∫ t in Ioc a b, f t ∂μ := by
  have hsplit : Ico a b = Ioo a b ∪ {a} := by
    ext t
    simp only [mem_Ico, mem_union, mem_Ioo, mem_singleton_iff]
    constructor
    · intro ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, ht.2⟩
    · rintro (ht | rfl)
      · exact ⟨ht.1.le, ht.2⟩
      · exact ⟨le_rfl, hab⟩
  have hint : IntegrableOn f (Icc a b) μ :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hia : IntegrableOn f ({a} : Set ℝ) μ :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨le_rfl, hab.le⟩)
  have hib : IntegrableOn f ({b} : Set ℝ) μ :=
    hint.mono_set (by intro t ht; rw [mem_singleton_iff.mp ht]; exact ⟨hab.le, le_rfl⟩)
  rw [hsplit, ← Ioo_union_right hab,
    setIntegral_union (by simp) (measurableSet_singleton _) (hint.mono_set Ioo_subset_Icc_self) hia,
    setIntegral_union (by simp) (measurableSet_singleton _) (hint.mono_set Ioo_subset_Icc_self) hib,
    integral_singleton, integral_singleton, smul_eq_mul, smul_eq_mul, he]

/-- Periodic support/curvature pairs have equal endpoint contributions. -/
theorem mixedArea_Ico_eq_Ioc {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) :
    (∫ t in Ico 0 (2 * π), supp K₁ t ∂(sigma K₂)) =
      ∫ t in Ioc 0 (2 * π), supp K₁ t ∂(sigma K₂) := by
  have hμ : sigma K₂ {2 * π} = sigma K₂ {0} := by
    have h := sigma_periodic h₂ ({0} : Set ℝ)
    simpa only [image_singleton, zero_add] using h
  have hs : supp K₁ (2 * π) = supp K₁ 0 := by
    simpa only [zero_add] using supp_add_two_pi K₁ 0
  apply integral_Ico_eq_Ioc_of_endpoint_balance (sigma K₂)
    (by linarith [pi_pos]) h₁.continuous_supp
  rw [hs]
  change (sigma K₂ {0}).toReal * supp K₁ 0 =
    (sigma K₂ {2 * π}).toReal * supp K₁ 0
  rw [hμ]

/-- Symmetry of mixed area for arbitrary convex bodies. -/
theorem mixedArea_symm {K₁ K₂ : Set (ℝ × ℝ)}
    (h₁ : IsConvexBody K₁) (h₂ : IsConvexBody K₂) :
    opt_Bs (Ico 0 (2 * π)) K₁ K₂ = opt_Bs (Ico 0 (2 * π)) K₂ K₁ := by
  have key : ∀ {L₁ L₂ : Set (ℝ × ℝ)}, IsConvexBody L₁ → IsConvexBody L₂ →
      opt_Bs (Ico 0 (2 * π)) L₁ L₂ =
        -(∫ t in (0 : ℝ)..(2 * π), opt_g L₁ t * opt_g L₂ t) +
          ∫ t in (0 : ℝ)..(2 * π), supp L₁ t * supp L₂ t := by
    intro L₁ L₂ hL₁ hL₂
    have hs : supp L₁ (2 * π) = supp L₁ 0 := by
      simpa only [zero_add] using supp_add_two_pi L₁ 0
    unfold opt_Bs
    rw [mixedArea_Ico_eq_Ioc hL₁ hL₂,
      opt_supp_ibp hL₁ hL₂ (by linarith [pi_pos] : (0 : ℝ) ≤ 2 * π),
      opt_g_two_pi, hs]
    ring
  rw [key h₁ h₂, key h₂ h₁]
  have e1 : (∫ t in (0 : ℝ)..(2 * π), opt_g K₂ t * opt_g K₁ t) =
      ∫ t in (0 : ℝ)..(2 * π), opt_g K₁ t * opt_g K₂ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have e2 : (∫ t in (0 : ℝ)..(2 * π), supp K₂ t * supp K₁ t) =
      ∫ t in (0 : ℝ)..(2 * π), supp K₁ t * supp K₂ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [e1, e2]

/-- The area first variation on the full convex-body domain. -/
theorem area_firstVariation_convex (K Ks : ConvexBodySet) :
    convexBodyDomain.dirDeriv (fun C => area C.1) K Ks =
      ∫ t in Ico 0 (2 * π), (supp Ks.1 t - supp K.1 t) ∂(sigma K.1) := by
  have hf : (fun C : ConvexBodySet => area C.1) =
      fun C => (1 / 2) * ∫ t in Ico 0 (2 * π), supp C.1 t ∂(sigma C.1) :=
    funext fun C => theorem7_1_3 C.2
  refine ((congrArg (fun f => convexBodyDomain.dirDeriv f K Ks) hf).trans
    (lemma7_1_4 convexBodyDomain
      ((cvx_integral_supp_sigma_bilin (Metric.isBounded_Ico 0 (2 * π))).const_mul (1 / 2))
      K Ks)).trans ?_
  have hsymm := mixedArea_symm K.2 Ks.2
  simp only [opt_Bs] at hsymm
  rw [hsymm]
  have hiK : IntegrableOn (supp K.1) (Ico 0 (2 * π)) (sigma K.1) :=
    (K.2.continuous_supp.continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π)))).mono_set Ico_subset_Icc_self
  have hiKs : IntegrableOn (supp Ks.1) (Ico 0 (2 * π)) (sigma K.1) :=
    (Ks.2.continuous_supp.continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π)))).mono_set Ico_subset_Icc_self
  rw [integral_sub hiKs hiK]
  ring

/-- For normalized caps the lower semicircle contributes nothing, even with atoms. -/
theorem area_firstVariation_caps (K Ks : ConvexBodySet)
    (hK : IsCap K.1 (π / 2)) (hKs : IsCap Ks.1 (π / 2)) :
    convexBodyDomain.dirDeriv (fun C => area C.1) K Ks =
      ∫ t in Icc 0 π, (supp Ks.1 t - supp K.1 t) ∂(sigma K.1) := by
  rw [area_firstVariation_convex]
  apply opt_Ico_eq_Icc hK (Ks.2.continuous_supp.sub K.2.continuous_supp)
  rw [Pi.sub_apply, hKs.2.2.2.2.2.1, hK.2.2.2.2.2.1, sub_self]

end MovingSofaStability

end MixedArea
