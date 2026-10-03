module

public import SofaSubmission.Defs

/-!
# Shared canonical moving-sofa model

`SofaSubmission.Defs` is supplied by the pinned `sofa-formal` Lean dependency
at commit 838baca722560f30ea8e60b8c711b20147626175. It gives the original
formal-conjectures definitions, including its exact concrete Gerver formula,
and proves `GerversSofa.ABφθSpec.existsUnique` before choosing the constants.
It does not import the upstream Challenge or its admitted solved statements.

There is no second copy of `MovingSofa.IsMovingSofa`, its induced motion
topology, or `MovingSofa.sofaConstant` in the solution environment. Both the
paper bridge and the final submission theorem use these same declarations.
The pair-coordinate development keeps its `MovingSofa.Paper` definitions;
`SofaUniqueness.Bridge.Motions` proves their precise relationship, including
initial placement and equality of the two extremal values.

Provenance: Formal Conjectures Authors (Apache-2.0), with the parameter proof
from RuifengCao/sofa-formal. The dependency's existing solved results are reused,
not claimed as new work. No source rewriting or code-generation script is
part of this integration. Toolchain compatibility remains uncompiled.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real unitInterval EuclideanGeometry

namespace MovingSofa.Canonical

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

/-- The supremum bounds every actual competitor, with no finiteness premise. -/
theorem volume_le_constant {s : Set ℝ²} (hs : ∃ m, IsMovingSofa s m) :
    volume s ≤ sofaConstant := by
  exact le_iSup₂ (α := ℝ≥0∞) s hs

/-- Nonemptiness is part of connectedness in the canonical motion structure. -/
theorem nonempty {s : Set ℝ²} (hs : ∃ m, IsMovingSofa s m) : s.Nonempty := by
  obtain ⟨m, hm⟩ := hs
  exact hm.isConnected.nonempty

end MovingSofa.Canonical
