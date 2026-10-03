module

public import Mathlib

/-!
# Independent statement: all maximizing moving sofas are congruent

The motion model and supremum are those of formal-conjectures (Formal
Conjectures Authors, Apache-2.0), copied as mathematical definitions rather
than imported from the local proof. The Challenge imports only Mathlib.

This is the shared uniqueness statement proved by the current source draft.
It does not replace the exact upstream statement naming its concrete
`gerversSofa`; that separate fixture is in `ChallengeUniqueness.lean`.

The single placeholder is the independent challenge statement. It is not
imported by `SofaSubmission.Final` or any of its proof dependencies.
Comparator has not been run.
-/

@[expose] public section
noncomputable section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace MovingSofa

open Topology MeasureTheory
open scoped Real unitInterval EuclideanGeometry

def horizontalHallway : Set ℝ² :=
  {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

def verticalHallway : Set ℝ² :=
  {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

def sofaConstant : ℝ≥0∞ :=
  ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

namespace Canonical

/-- Equality of the actual sets up to isometry, for any two maximizers. -/
theorem maximizers_congruent (s t : Set ℝ²)
    (hs : ∃ m, MovingSofa.IsMovingSofa s m)
    (ht : ∃ m, MovingSofa.IsMovingSofa t m)
    (hsvol : volume s = MovingSofa.sofaConstant)
    (htvol : volume t = MovingSofa.sofaConstant) :
    ∃ g : E(2), s = g '' t := by
  sorry

end Canonical
end MovingSofa
