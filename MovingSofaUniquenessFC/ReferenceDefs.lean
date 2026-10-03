module

public import MovingSofaUniquenessFC.Model

/-!
# Formal-conjectures' Gerver sofa

The constants `A`, `B`, `φ`, `θ`, the radius `r`, the integrals `x`, `y`, the rotation path `p` and
`gerversSofa` of formal-conjectures (`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`, Apache-2.0, Copyright 2026 The Formal Conjectures
Authors) are defined in `ChallengeDefs`, where `ABφθSpec.existsUnique` is proved by the analytic
argument of `MovingSofaUniquenessFC.Reference.spec_existsUnique`. This module packages the constants
for the reference modules.
-/

@[expose] public section
noncomputable section

open scoped EuclideanGeometry

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

theorem rotateTranslate_apply (α : Real.Angle) (p q : ℝ²) :
    rotateTranslate α p q = EuclideanGeometry.o.rotation α (q + p) := rfl

namespace GerversSofa

/-- Package the constants without choosing a different root. -/
def referenceData : MovingSofaUniquenessFC.Reference.Data := ⟨A, B, φ, θ⟩

theorem referenceData_valid : referenceData.Valid :=
  ABφθSpec.existsUnique.choose_spec.1

end GerversSofa

end MovingSofa
