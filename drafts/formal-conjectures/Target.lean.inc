/- UNCOMPILED REPLACEMENT DECLARATION.
The exact upstream statement is unchanged. This body depends on the explicit
P1-P6 and B1-B3 admissions and on upstream's previously solved results. It is
not a completed proof and the research-open category is intentionally retained.
The exporter replaces the old declaration; it does not append a duplicate.
-/

@[category research open, AMS 49]
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  constructor
  · intro hvolume
    have hS := UniquenessDraft.upstream_maximizer_is_library_maximizer hs hvolume
    have hG := UniquenessDraft.upstream_maximizer_is_library_maximizer
      isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa.symm
    obtain ⟨g, hg⟩ := SofaUniqueness.Draft.globalMax_congruent hS hG
    exact ⟨UniquenessDraft.realizeRigid g, UniquenessDraft.congruent_of_coordinates g hg⟩
  · intro hcongruent
    exact (SofaUniqueness.volume_eq_of_congruent hcongruent).trans
      sofaConstant_eq_volume_gerversSofa.symm
