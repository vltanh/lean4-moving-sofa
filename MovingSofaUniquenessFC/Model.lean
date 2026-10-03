module

public import ChallengeDefs

/-!
# The canonical moving-sofa motion model

The hallway definitions, the affine-isometry topology, the `IsMovingSofa` structure and the sofa
constant of formal-conjectures (`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`, Apache-2.0, Copyright 2026 The Formal Conjectures
Authors) are defined in `ChallengeDefs`, with their original names, types, field order and bodies,
so that `Challenge.lean` states them verbatim. This module proves basic facts about them. The
paper's pair-coordinate presentation is the library `MovingSofaOptimality`; its
`MovingSofaOptimality.IsMovingSofa` and `MovingSofaOptimality.hallway` do not collide with the names
`MovingSofa.*`.
-/

@[expose] public section
noncomputable section

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry
open MeasureTheory
open scoped ENNReal

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
