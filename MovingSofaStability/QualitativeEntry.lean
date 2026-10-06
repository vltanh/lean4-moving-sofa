module

public import MovingSofaStability.SofaLimitMotion

/-!
# Qualitative entry into the quantitative neighborhood

Uncompiled proof source. Compactness supplies entry into a fixed neighborhood,
not a rate. The limit motion is constructed from supporting constraints.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Filter Topology TopologicalSpace
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

def compactShapeOfMoving {S : Set Point} (hS : IsMovingSofa S) : CompactShape where
  carrier := S
  isCompact' := isCompact_of_isMovingSofa hS
  nonempty' := hS.choose_spec.2.1.nonempty

def gerverCompactShape {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) : CompactShape :=
  compactShapeOfMoving ⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩

theorem maximizing_subsequence {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (K : ℕ → CompactShape) (ωn : ℕ → ℝ)
    (hmove : ∀ n, IsMovingSofaWithAngle (K n : Set Point) (ωn n))
    (hangles : ∀ n, ωn n ∈ Icc (arccos (5 / 11)) (π / 2))
    (htops : ∀ n, supp (K n : Set Point) (π / 2) = 1)
    (hlefts : ∀ n, supp (K n : Set Point) π = supp (gerverSofa P) π)
    (harea : Tendsto (fun n => area (K n : Set Point)) atTop (𝓝 (area (gerverSofa P)))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (K ∘ σ) atTop (𝓝 (gerverCompactShape hP hbox)) ∧
      Tendsto (ωn ∘ σ) atTop (𝓝 (π / 2)) := by
  sorry

theorem near_maximizers_enter_neighborhood {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {ρ α₀ : ℝ} (hρ : 0 < ρ) (hα₀ : 0 < α₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ S : Set Point, ∀ ω : ℝ,
      IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
      sofaDeficit P S < ε₀ →
      EuclideanClose ρ (normalizedSofa P S) (gerverSofa P) ∧ π / 2 - ω < α₀ := by
  sorry

end MovingSofaStability
