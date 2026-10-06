module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaStability.QuadraticDeficit

/-!
# Mamikon difference energies

Uncompiled proof source. These statements quantify the existing equality-case
lemmas and apply to arbitrary convex bodies, without `InjCond1`.

The energy is half the integral of the *difference* of two tangent
displacements squared. It is not the Mamikon area of either body separately.
-/

@[expose] public section
noncomputable section

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

/-- Reversing the order of the difference leaves its energy unchanged. -/
theorem halfSquareIntegral_sub_comm (μ : Measure X) (f g : X → ℝ) :
    halfSquareIntegral μ (fun x => f x - g x) =
      halfSquareIntegral μ (fun x => g x - f x) := by
  unfold halfSquareIntegral
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

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

theorem displacementEnergy_comm (a b : ℝ)
    (z : ConvexBodySet → ℝ → ℝ × ℝ) (K₀ K₁ : ConvexBodySet) :
    displacementEnergy a b z K₀ K₁ = displacementEnergy a b z K₁ K₀ :=
  halfSquareIntegral_sub_comm _ _ _

section Arc

variable {a b : ℝ} (hab : a < b) (hb : b < a + π)
variable (z : ConvexBodySet → ℝ → ℝ × ℝ)
variable (hz : ∀ K, IsCBV (z K) a b)
variable (hzl : ∀ K, ∀ t ∈ Icc a b, z K t ∈ suppLine K.1 t)
variable (hlin : ∀ K₀ K₁, ∀ c ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b,
  z (convexBodyComb c K₀ K₁) t = (1 - c) • z K₀ t + c • z K₁ t)

/-- Exact quantitative Mamikon convexity gap, including the endpoint parameters. -/
theorem mamikon_combo_energy (K₀ K₁ : ConvexBodySet) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (z K₀) + c * mamikon K₁.1 a b (z K₁) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (z (convexBodyComb c K₀ K₁)) =
      c * (1 - c) * displacementEnergy a b z K₀ K₁ := by
  sorry

/-- Four times the midpoint gap is exactly the difference-square energy. -/
theorem mamikon_midpoint_energy (K₀ K₁ : ConvexBodySet) :
    4 * ((mamikon K₀.1 a b (z K₀) + mamikon K₁.1 a b (z K₁)) / 2 -
      mamikon (convexBodyComb (1 / 2) K₀ K₁).1 a b
        (z (convexBodyComb (1 / 2) K₀ K₁))) =
      displacementEnergy a b z K₀ K₁ := by
  sorry

end Arc

end MovingSofaStability
