module

public import MovingSofaStability.EuclideanGeometry
public import MovingSofaUniqueness.Main

/-!
# The unrestricted stability target

`UnrestrictedStability` and `TerminalAngleStability` state the main theorems;
`GlobalStability.lean` proves them (`unrestricted_stability`,
`terminal_angle_stability`).

The metric conclusion uses both directed Euclidean bounds on the actual
nonconvex sets. The normalization agrees with note 08 and uses translation
only. No injective-cap or special-envelope hypothesis appears in the target.
-/

@[expose] public section
noncomputable section

open Real Set
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- The deficit of the original sofa's area, not that of a surrogate cap. -/
def sofaDeficit (P : GerverParams) (S : Set Point) : ℝ :=
  area (gerverSofa P) - area S

/-- Pin the top support and the leftmost coordinate without a small-angle denominator. -/
def normalizingShift (P : GerverParams) (S : Set Point) : Point :=
  (supp S π - supp (gerverSofa P) π, 1 - supp S (π / 2))

def normalizedSofa (P : GerverParams) (S : Set Point) : Set Point :=
  Rigid.translate (normalizingShift P S) '' S

/-- Symmetric-difference area is written explicitly to keep its set meaning visible. -/
def symmetricDifferenceArea (S T : Set Point) : ℝ :=
  area ((S \ T) ∪ (T \ S))

@[simp] theorem area_normalizedSofa (P : GerverParams) (S : Set Point) :
    area (normalizedSofa P S) = area S :=
  (Rigid.translate (normalizingShift P S)).area_image S

@[simp] theorem sofaDeficit_normalized (P : GerverParams) (S : Set Point) :
    sofaDeficit P (normalizedSofa P S) = sofaDeficit P S := by
  simp only [sofaDeficit, area_normalizedSofa]

theorem normalizedSofa_top (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) : supp (normalizedSofa P S) (π / 2) = 1 := by
  unfold normalizedSofa
  rw [Rigid.coe_translate, supp_translate S _ _ hS hne]
  simp only [normalizingShift, dot, uvec_fst, uvec_snd, cos_pi_div_two, sin_pi_div_two]
  ring

theorem normalizedSofa_left (P : GerverParams) {S : Set Point}
    (hS : IsCompact S) (hne : S.Nonempty) :
    supp (normalizedSofa P S) π = supp (gerverSofa P) π := by
  unfold normalizedSofa
  rw [Rigid.coe_translate, supp_translate S _ _ hS hne]
  simp only [normalizingShift, dot, uvec_fst, uvec_snd, cos_pi, sin_pi]
  ring

/-- `theorem1_1_1` bounds ENNReal volume. The imported real-area corollary
performs the finite-measure conversion needed for this real deficit. -/
theorem sofaDeficit_nonneg {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Point} (hS : IsMovingSofa S) : 0 ≤ sofaDeficit P S :=
  sub_nonneg.mpr (MovingSofaUniqueness.area_le_gerver hP hbox hS)

/-- Note 08's unrestricted theorem, in the original sofa definitions;
`unrestricted_stability` proves it. -/
def UnrestrictedStability (P : GerverParams) : Prop :=
  ∃ C Carea ε₀ : ℝ, 0 < C ∧ 0 < Carea ∧ 0 < ε₀ ∧
    ∀ S : Set Point, IsMovingSofa S → sofaDeficit P S < ε₀ →
      EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
      symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤
        Carea * sqrt (sofaDeficit P S)

/-- The angle-rate target is separate from the Hausdorff conclusion. -/
def TerminalAngleStability (P : GerverParams) : Prop :=
  ∃ Cangle ε₀ : ℝ, 0 < Cangle ∧ 0 < ε₀ ∧
    ∀ (S : Set Point) (ω : ℝ), IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
      0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S

end MovingSofaStability
