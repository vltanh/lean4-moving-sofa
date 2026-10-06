module

public import MovingSofaStability.NonsmoothAffinity

/-!
# Baek's Q is quadratic and concave on the enlarged domain

This is an extension of the functional's algebraic properties, not yet its
geometric upper bound on arbitrary near-maximizers. The enlarged-domain first
variation at Gerver is a separate dependency.
-/

@[expose] public section
noncomputable section

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

/-- Exact quadratic energy is nonnegative on the enlarged domain. -/
theorem wideEnergy_nonneg {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4)) (x y : WideTriple φ) :
    0 ≤ segmentEnergy (wideDomain φ) (wideUpperQ φ) x y :=
  segmentEnergy_nonneg (wideDomain φ) (wideUpperQ_concave hφ) x y

/-- A first-variation certificate is sufficient on the enlarged domain.
The separate task is proving this derivative sign at Gerver for all wide triples. -/
theorem wide_maximum_iff_firstVariation {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x₀ : WideTriple φ) :
    (∀ x, wideUpperQ φ x ≤ wideUpperQ φ x₀) ↔
      ∀ x, (wideDomain φ).dirDeriv (wideUpperQ φ) x₀ x ≤ 0 :=
  theorem7_1_5 (wideDomain φ) (wideUpperQ_quadratic hφ) (wideUpperQ_concave hφ) x₀

end MovingSofaStability
