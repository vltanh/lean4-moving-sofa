module

public import MovingSofaStability.WideGerverCertificate
public import MovingSofaStability.Residuals

/-!
# Six squared displacement differences in the enlarged deficit

Uncompiled proof source. This identifies the abstract quadratic energy with
actual integrals, not merely with a midpoint expression. The four cap integrals
are bounded by the objective deficit for EVERY nonsmooth feasible triple.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- Sum of the four cap displacement energies, for arbitrary convex bodies. -/
def capResidualEnergy (φ : ℝ) (K₀ K₁ : ConvexBodySet) : ℝ :=
  displacementEnergy 0 φ (fun K => tangentParam K.1 (π / 2)) K₀ K₁ +
  displacementEnergy φ (π / 2 - φ) (fun K => outerCorner K.1) K₀ K₁ +
  displacementEnergy (π / 2 - φ) (π / 2)
    (fun K => tangentParam K.1 (π / 2 + (π / 2 - φ))) K₀ K₁ +
  displacementEnergy (π / 2) π (fun K => tangentParam K.1 π) K₀ K₁

def rightResidualEnergy (φ : ℝ) (B₀ B₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (π + φ) (3 * π / 2) (fun B => tangentParam B.1 (3 * π / 2)) B₀ B₁

def leftResidualEnergy (φ : ℝ) (D₀ D₁ : ConvexBodySet) : ℝ :=
  displacementEnergy (3 * π / 2) (3 * π / 2 + (π / 2 - φ))
    (fun D => tangentParam D.1 (3 * π / 2 + (π / 2 - φ))) D₀ D₁

theorem capResidualEnergy_nonneg (φ : ℝ) (K₀ K₁ : ConvexBodySet) :
    0 ≤ capResidualEnergy φ K₀ K₁ := by
  unfold capResidualEnergy
  exact add_nonneg (add_nonneg (add_nonneg (displacementEnergy_nonneg _ _ _ _ _)
    (displacementEnergy_nonneg _ _ _ _ _)) (displacementEnergy_nonneg _ _ _ _ _))
    (displacementEnergy_nonneg _ _ _ _ _)

theorem rightResidualEnergy_nonneg (φ : ℝ) (B₀ B₁ : ConvexBodySet) :
    0 ≤ rightResidualEnergy φ B₀ B₁ := displacementEnergy_nonneg _ _ _ _ _

theorem leftResidualEnergy_nonneg (φ : ℝ) (D₀ D₁ : ConvexBodySet) :
    0 ≤ leftResidualEnergy φ D₀ D₁ := displacementEnergy_nonneg _ _ _ _ _

/-- Specialize the quantitative Mamikon identity to a fixed tangent line. -/
theorem tangent_energy_gap {a b T c : ℝ} (hab : a < b) (hb : b < a + π)
    (ha : T - π < a) (hbt : b ≤ T) (K₀ K₁ : ConvexBodySet)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (tangentParam K₀.1 T) +
      c * mamikon K₁.1 a b (tangentParam K₁.1 T) -
      mamikon (convexBodyComb c K₀ K₁).1 a b
        (tangentParam (convexBodyComb c K₀ K₁).1 T) =
      c * (1 - c) * displacementEnergy a b (fun K => tangentParam K.1 T) K₀ K₁ := by
  sorry

/-- Specialize the identity to the outer-corner family. -/
theorem outer_energy_gap {a b c : ℝ} (hab : a < b) (hb : b < a + π)
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikon K₀.1 a b (outerCorner K₀.1) +
      c * mamikon K₁.1 a b (outerCorner K₁.1) -
      mamikon (convexBodyComb c K₀ K₁).1 a b (outerCorner (convexBodyComb c K₀ K₁).1) =
      c * (1 - c) * displacementEnergy a b (fun K => outerCorner K.1) K₀ K₁ := by
  sorry

/-- The grouped cap gap is the sum of all four displacement energies. -/
theorem capResidualEnergy_gap {φ c : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (K₀ K₁ : ConvexBodySet) (hc : c ∈ Icc (0 : ℝ) 1) :
    (1 - c) * mamikonS φ K₀.1 + c * mamikonS φ K₁.1 -
      mamikonS φ (convexBodyComb c K₀ K₁).1 = c * (1 - c) * capResidualEnergy φ K₀ K₁ := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have h1 := tangent_energy_gap (T := π / 2) (a := 0) (b := φ)
    hφ0 (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h2 := outer_energy_gap (a := φ) (b := π / 2 - φ)
    (by linarith) (by linarith) K₀ K₁ hc
  have h3 := tangent_energy_gap (T := π / 2 + (π / 2 - φ))
    (a := π / 2 - φ) (b := π / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) K₀ K₁ hc
  have h4 := tangent_energy_gap (T := π) (a := π / 2) (b := π)
    (by linarith) (by linarith) (by linarith) le_rfl K₀ K₁ hc
  unfold mamikonS capResidualEnergy
  linarith

/-- All six integral energies, retaining the two auxiliary-body terms. -/
def wideResidualEnergy {φ : ℝ} (x y : WideTriple φ) : ℝ :=
  capResidualEnergy φ x.1.1 y.1.1 + rightResidualEnergy φ x.1.2.1 y.1.2.1 +
    leftResidualEnergy φ x.1.2.2 y.1.2.2

theorem wideEnergy_eq_integrals {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 4))
    (x y : WideTriple φ) :
    segmentEnergy (wideDomain φ) (wideUpperQ φ) x y = wideResidualEnergy x y := by
  have hpi := pi_pos
  have hφ0 := hφ.1
  have hφ4 := hφ.2
  have hc : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hS := capResidualEnergy_gap hφ x.1.1 y.1.1 hc
  have hR := tangent_energy_gap (T := 3 * π / 2) (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.1 y.1.2.1 hc
  have hL := tangent_energy_gap (T := 3 * π / 2 + (π / 2 - φ))
    (a := 3 * π / 2) (b := 3 * π / 2 + (π / 2 - φ))
    (by linarith) (by linarith) (by linarith) le_rfl x.1.2.2 y.1.2.2 hc
  change (1 - 1 / 2) * mamikonR φ x.1.2.1.1 + (1 / 2) * mamikonR φ y.1.2.1.1 -
    mamikonR φ (convexBodyComb (1 / 2) x.1.2.1 y.1.2.1).1 =
    (1 / 2) * (1 - 1 / 2) * rightResidualEnergy φ x.1.2.1 y.1.2.1 at hR
  change (1 - 1 / 2) * mamikonL φ x.1.2.2.1 + (1 / 2) * mamikonL φ y.1.2.2.1 -
    mamikonL φ (convexBodyComb (1 / 2) x.1.2.2 y.1.2.2).1 =
    (1 / 2) * (1 - 1 / 2) * leftResidualEnergy φ x.1.2.2 y.1.2.2 at hL
  have hlin := cap_mamikon_upperP_affine hφ x.2.1 y.2.1 hc
  have hm := inWideL_comb x.2 y.2 hc
  simp only [cvx_convexBodyComb_val hc] at hS hR hL
  unfold segmentEnergy wideResidualEnergy
  simp only [wideUpperQ, wideDomain, WideTriple.comb, hc, ↓reduceDIte,
    cvx_convexBodyComb_val hc]
  rw [wide_upperQ_decomposition hφ hm,
    wide_upperQ_decomposition hφ x.2, wide_upperQ_decomposition hφ y.2]
  linarith

/-- The exact deficit identity in integral, rather than abstract midpoint, form. -/
theorem wide_deficit_eq_slack_add_integrals {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    area (gerverSofa P) - wideUpperQ P.φ x =
      wideDualSlack hP hbox x + wideResidualEnergy (wideGerverTriple hP hbox) x := by
  sorry

/-- Cap-only integral energy is bounded by the nonsmooth Q deficit. -/
theorem wide_capResidualEnergy_le_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) (x : WideTriple P.φ) :
    capResidualEnergy P.φ (wideGerverTriple hP hbox).1.1 x.1.1 ≤
      area (gerverSofa P) - wideUpperQ P.φ x := by
  rw [wide_deficit_eq_slack_add_integrals hP hbox x]
  have hs := wideDualSlack_nonneg hP hbox x
  have hr := rightResidualEnergy_nonneg P.φ (wideGerverTriple hP hbox).1.2.1 x.1.2.1
  have hl := leftResidualEnergy_nonneg P.φ (wideGerverTriple hP hbox).1.2.2 x.1.2.2
  unfold wideResidualEnergy
  linarith

end MovingSofaStability
