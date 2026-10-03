module

public import SofaSubmission.Solution
public import SofaSubmission.Uniqueness

/-!
# The exact formal-conjectures moving-sofa uniqueness statement

`SofaSubmission.Solution` comes from the pinned Lean source dependency
RuifengCao/sofa-formal at 838baca722560f30ea8e60b8c711b20147626175. It proves
the pre-existing concrete Gerver motion and volume-optimality facts. Its
`Defs` module proves parameter existence before defining Gerver's constants.
Neither the upstream Challenge nor the old generated insertion fragments is
imported. The shape-uniqueness argument itself is the local, shared one.

The declaration below retains the upstream name, quantifiers and conclusion.
It has no extra uniqueness, smoothness, injectivity or reference-shape premise.
The optional publication corollary then relates the actual pair-coordinate
Gerver witness to the upstream formula through an explicitly placed copy.

UNCOMPILED: no Lean execution, axiom audit, Comparator run, or Palomar
certification has been performed for this source. In particular, the pinned
reference proof was written for Lean 4.33.1 and is not yet checked against the
root project's 4.35.0-rc3 toolchain. A short final proof body does not establish
that its full dependency graph elaborates.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped Real unitInterval EuclideanGeometry

namespace MovingSofa

/-- Gerver's concrete sofa is the unique maximizer up to a Euclidean rigid motion.
This is the exact statement of the formal-conjectures uniqueness declaration. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  exact Canonical.volume_eq_constant_iff_congruent hs
    isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa

/-- The publication's Gerver witness and the upstream concrete formula describe
congruent shapes. Initial placement is explicit, not silently normalized away.
The conclusion is equality of sets, rather than equality modulo null sets. -/
theorem paper_gerver_congruent_gerversSofa {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ (v : ℝ × ℝ) (g : E(2)),
      SofaUniqueness.Bridge.point '' ((fun p => p + v) '' gerverSofa P) =
        g '' gerversSofa := by
  obtain ⟨v, hmove, hvolume⟩ := SofaUniqueness.Bridge.paper_to_canonical_placement
    (theorem1_1_1 hP hbox).1
  have hattains : volume
      (SofaUniqueness.Bridge.point '' ((fun p => p + v) '' gerverSofa P)) =
        sofaConstant :=
    hvolume.trans (Canonical.constant_eq_paper_gerver hP hbox).symm
  obtain ⟨g, hg⟩ := (volume_eq_sofaConstant_iff_congruent_gerversSofa _ hmove).mp hattains
  exact ⟨v, g, hg⟩

end MovingSofa
