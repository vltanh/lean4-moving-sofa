/- UNCOMPILED INSERTION FRAGMENT, after Coordinates.lean.inc.
The only bridge admissions are B1-B3 in that preceding fragment. -/

namespace UniquenessDraft

open Set Real MeasureTheory
open scoped unitInterval EuclideanGeometry

/-- Convert the upstream identity-start motion to the library's lifted-angle
vocabulary. Extending by a continuous clamp handles the different time domains. -/
theorem upstream_to_library {s : Set ℝ²} (hs : ∃ m, IsMovingSofa s m) :
    SofaLegacy.IsMovingSofa (coordinates '' s) := by
  obtain ⟨m, hm⟩ := hs
  obtain ⟨θ, c, hθ, hc, hθ0, hc0, hformula⟩ := real_angle_lift m hm.continuous hm.zero
  let τ : ℝ → I := fun t =>
    ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hτ : Continuous τ := by
    unfold τ
    fun_prop
  have hτ0 : τ 0 = (0 : I) := by apply Subtype.ext; norm_num [τ]
  have hτ1 : τ 1 = (1 : I) := by apply Subtype.ext; norm_num [τ]
  refine ⟨-(θ 1), coordinates_image_closed hm.isClosed,
    hm.isConnected.image _ coordinates_continuous.continuousOn,
    (fun t => θ (τ t)), (fun t => c (τ t)), ?_⟩
  refine ⟨(hθ.comp hτ).continuousOn, (hc.comp hτ).continuousOn,
    by simpa [hτ0] using hθ0, by simp [hτ1], ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa [hτ0, hθ0, hc0, SofaLegacy.rot_zero] using
      (coordinates_mem_horizontal p).mpr (hm.initial hp)
  · rintro t ht _ ⟨p, hp, rfl⟩
    rw [← hformula (τ t) p]
    exact (coordinates_mem_hallway _).mpr
      (hm.subset_hallway (τ t) ⟨p, hp, rfl⟩)
  · rintro _ ⟨p, hp, rfl⟩
    rw [hτ1, ← hformula 1 p]
    exact (coordinates_mem_vertical _).mpr (hm.final ⟨p, hp, rfl⟩)

/-- A library sofa need not initially lie in the horizontal hallway. Translate
it by c(0), then use R_theta(q-c(0))+c(t); this motion starts at the identity.
The returned upstream sofa has EXACTLY the same volume as the input.

It would be false to simply assert that `point '' S` has an identity-start
motion, without the initial-placement translation. -/
theorem library_to_upstream {S : Set CoordinatePlane} (hS : SofaLegacy.IsMovingSofa S) :
    ∃ s : Set ℝ², (∃ m, IsMovingSofa s m) ∧ volume s = volume S := by
  obtain ⟨ω, hSω⟩ := hS
  obtain ⟨hclosed, hconnected, θ, c, hm⟩ := hSω
  let S₀ : Set CoordinatePlane := (fun p => p + c 0) '' S
  let s : Set ℝ² := point '' S₀
  have hS₀ := SofaLegacy.mpc_isMovingSofaWithAngle_translate
    (show SofaLegacy.IsMovingSofaWithAngle S ω from ⟨hclosed, hconnected, θ, c, hm⟩) (c 0)
  have hθ : Continuous (fun t : I => θ t) :=
    hm.continuousOn_angle.comp_continuous continuous_subtype_val (fun t => t.property)
  have hc : Continuous (fun t : I => c t) :=
    hm.continuousOn_shift.comp_continuous continuous_subtype_val (fun t => t.property)
  have hr : Continuous (fun t : I => SofaLegacy.rot (θ t) (c 0)) := by
    have hrotation : Continuous (fun a : ℝ => SofaLegacy.rot a (c 0)) := by
      unfold SofaLegacy.rot
      fun_prop
    exact hrotation.comp hθ
  let m : I → E(2) := fun t =>
    realization (θ t, c t - SofaLegacy.rot (θ t) (c 0))
  have hmcont : Continuous m := realization_continuous.comp (hθ.prodMk (hc.sub hr))
  have hmzero : m 0 = AffineIsometryEquiv.refl ℝ ℝ² := by
    apply AffineIsometryEquiv.ext
    intro p
    apply coordinates_injective
    change coordinates (realization (θ 0, c 0 - SofaLegacy.rot (θ 0) (c 0)) p) = _
    rw [realization_coordinates]
    simp [hm.angle_zero, SofaLegacy.rot_zero]
  have hformula (t : I) (p : CoordinatePlane) :
      coordinates (m t (point (p + c 0))) = SofaLegacy.rot (θ t) p + c t := by
    change coordinates (realization (θ t, c t - SofaLegacy.rot (θ t) (c 0))
      (point (p + c 0))) = _
    rw [realization_coordinates, coordinates_point, SofaLegacy.rot_add_vec]
    abel
  refine ⟨s, ⟨m, ?_⟩, ?_⟩
  · refine ⟨hS₀.2.1.image _ point_continuous.continuousOn,
      point_image_closed hS₀.1, hmcont, hmzero, ?_, ?_, ?_⟩
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      apply (coordinates_mem_horizontal _).mp
      simpa [coordinates_point, hm.angle_zero, SofaLegacy.rot_zero] using hm.start p hp
    · rintro t _ ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
      apply (coordinates_mem_hallway _).mp
      rw [hformula]
      exact hm.inside t t.property p hp
    · rintro _ ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
      apply (coordinates_mem_vertical _).mp
      rw [hformula]
      exact hm.finish p hp
  · change volume (point '' ((fun p => p + c 0) '' S)) = volume S
    rw [volume_point_image]
    exact SofaUniqueness.Draft.volume_translate (c 0) S

/-- Transfer a specific upstream maximizer to a specific library maximizer.
The reverse bridge is essential: it lets the upstream supremum bound EVERY
library competitor, not just coordinate images already in a chosen placement. -/
theorem upstream_maximizer_is_library_maximizer {s : Set ℝ²}
    (hs : ∃ m, IsMovingSofa s m) (hvolume : volume s = sofaConstant) :
    SofaUniqueness.Draft.IsGlobalMax (coordinates '' s) := by
  refine ⟨upstream_to_library hs, fun T hT => ?_⟩
  obtain ⟨t, ht, htv⟩ := library_to_upstream hT
  rw [volume_coordinates_image, hvolume]
  calc
    volume T = volume t := htv.symm
    _ ≤ sofaConstant := le_iSup₂ (α := ℝ≥0∞) t ht

end UniquenessDraft
