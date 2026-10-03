module

public import SofaUniqueness.SupportKernelEquations

/-!
# From Mamikon equality to the support equations

Each convex-body family uses the continuous supporting curves already proved
in Theorem 8.3.1 and the outer-corner lemmas. Square-integrability and pointwise
interior equality come from `MamikonDisplacement`; support derivatives and
endpoint-safe integration come from `SupportKernelEquations`.

Uncompiled scripts; no admitted statements.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofa SofaUniqueness.Draft

namespace SofaUniqueness

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
  sorry

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
  sorry

end SofaUniqueness
