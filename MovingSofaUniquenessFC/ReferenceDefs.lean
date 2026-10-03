/-
The reference definitions below are from the Formal Conjectures Authors,
Copyright 2026, Apache-2.0, FormalConjectures/Wikipedia/MovingSofa.lean,
Git blob 59b6ed7eb42e11b208b09539c245da4d3f11ed00.
The parameter theorem is replaced by the analytic proof in this repository.
-/
module

public import SofaSubmission.Model
public import SofaUniqueness.ReferenceExistence

/-!
# The exact formal-conjectures Gerver reference

The constants are chosen from the original FULL four-equation specification.
The theorem supplying that choice is proved, not imported from a Challenge
placeholder or from a decision-kernel certificate. The integral definitions,
branch inequalities, translation-before-rotation convention, and special
endpoint hallways are retained.

This module is ordinary source shared by the publication and submission
endpoints. It requires no source exporter. It has not been compiled.
-/

@[expose] public section
noncomputable section

open scoped EuclideanGeometry

noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- Translate first and then rotate, exactly as in the upstream reference. -/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

theorem rotateTranslate_apply (α : Real.Angle) (p q : ℝ²) :
    rotateTranslate α p q = EuclideanGeometry.o.rotation α (q + p) := rfl

/-- Both special endpoint hallways are retained. -/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-- The exact upstream specification, including all non-strict domain bounds. -/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- Analytic existence and uniqueness on the full specification domain. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 := by
  exact SofaUniqueness.Reference.spec_existsUnique

def A : ℝ := ABφθSpec.existsUnique.choose.1
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

/-- Package the constants without choosing a different root. -/
def referenceData : SofaUniqueness.Reference.Data := ⟨A, B, φ, θ⟩

theorem referenceData_valid : referenceData.Valid :=
  ABφθSpec.existsUnique.choose_spec.1

end GerversSofa

/-- The original concrete reference, not an arbitrarily selected maximizer. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

end MovingSofa
