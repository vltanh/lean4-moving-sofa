module

public import MovingSofaStability.WideDomain

/-!
# Curve-area affinity without differentiating the competitor

The difference between the outer and inner corner curves is the fixed curve
`uvec + vvec`. The difference of their quadratic curve areas is therefore affine
on the entire convex-body domain.

This replaces the C1 calculation of the first part of source Lemma 8.3.6 by
an argument in the real vector space of continuous bounded-variation curves.
It applies to nonsmooth competing caps and does not assume Ki.
-/

@[expose] public section
noncomputable section

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
