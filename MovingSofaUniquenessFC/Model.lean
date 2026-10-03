module

public import Mathlib

/-!
# The canonical moving-sofa motion model

The hallway definitions, affine-isometry topology, `IsMovingSofa` structure,
and sofa constant are the formal-conjectures definitions, with their original
names, types, field order, and mathematical bodies. This file imports Mathlib
only, not the paper implementation or an upstream file containing admissions.

Source: google-deepmind/formal-conjectures,
`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00` (Apache-2.0,
Copyright 2026 The Formal Conjectures Authors).

The concrete Gerver constants and theorems are deliberately not postulated here.
This model is shared by the publication bridge and the submission development.
The manuscript's pair-coordinate presentation remains available with its
explicit `MovingSofa.Paper` kernel names. No source exporter is involved.

This module and its clients are uncompiled source drafts.
-/

@[expose] public section
noncomputable section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The horizontal side of the unit hallway. -/
def horizontalHallway : Set ℝ² :=
  {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The vertical side of the unit hallway. -/
def verticalHallway : Set ℝ² :=
  {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The hallway, in the Euclidean-space presentation. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- An identity-start continuous rigid motion taking a connected closed sofa
from the horizontal side into the vertical side. -/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

open MeasureTheory
open scoped ENNReal

/-- The supremum of the volumes of sofas admitting the stated motion. -/
def sofaConstant : ℝ≥0∞ :=
  ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

namespace Canonical

/-- Coordinate membership in the horizontal side. -/
theorem mem_horizontal_iff (p : ℝ²) :
    p ∈ horizontalHallway ↔ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

/-- Coordinate membership in the vertical side. -/
theorem mem_vertical_iff (p : ℝ²) :
    p ∈ verticalHallway ↔ 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩

/-- The supremum bounds every actual competitor without any finiteness premise. -/
theorem volume_le_constant {s : Set ℝ²} (hs : ∃ m, IsMovingSofa s m) :
    volume s ≤ sofaConstant := by
  unfold sofaConstant
  exact le_iSup₂ (f := fun (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m) => volume s) s hs

/-- The motion structure includes nonemptiness through connectedness. -/
theorem nonempty {s : Set ℝ²} (hs : ∃ m, IsMovingSofa s m) : s.Nonempty := by
  obtain ⟨m, hm⟩ := hs
  exact hm.isConnected.nonempty

end Canonical
end MovingSofa
