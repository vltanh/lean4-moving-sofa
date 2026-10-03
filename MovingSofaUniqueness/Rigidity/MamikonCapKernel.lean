module

public import MovingSofaUniqueness.Rigidity.EqualityConditions
public import MovingSofaUniqueness.Rigidity.TangentEquality

/-!
# The four cap Mamikon equalities imply the complete support kernel

The four scalar convexity gaps are nonnegative. Their sum can vanish only if
each vanishes. The preceding modules prove the displacement equality,
differentiability on regular arcs, the exact tangent kernel and the integrated
middle equation. Together they give the cap kernel used in Proposition 5 of the
uniqueness argument.
-/

@[expose] public section
noncomputable section

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
