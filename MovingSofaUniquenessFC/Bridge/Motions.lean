module

public import SofaUniqueness.Bridge.PathLifting

/-!
# Equivalence of the two moving-sofa presentations

The canonical model requires an identity-start motion, so a given set must
already lie in the horizontal hallway. The paper model permits an initial
translation. Their exact relationship is stated in `canonical_iff_paper`.
For arbitrary paper sofas, `paper_to_canonical_placement` returns the actual
translation, not merely an unrelated sofa with the same area.

All three former bridge admissions have explicit scripts in the imported
coordinate, Euclidean-rigid, orientation, and path-lifting modules. The present
module uses no uniqueness theorem or concrete Gerver-parameter facts.
Uncompiled; no admissions in this module or its bridge prerequisites.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory
open scoped unitInterval EuclideanGeometry

namespace SofaUniqueness.Bridge

/-- Transport an identity-start canonical motion to the paper's real-angle
presentation, extending the parameter functions with a continuous clamp. -/
theorem canonical_to_paper {s : Set Point}
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    MovingSofa.Paper.IsMovingSofa (coordinates '' s) := by
  obtain ⟨m, hm⟩ := hs
  obtain ⟨θ, c, hθ, hc, hθ0, hc0, hformula⟩ :=
    real_angle_lift m hm.continuous hm.zero
  let τ : ℝ → I := fun t =>
    ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hτ : Continuous τ := by unfold τ; fun_prop
  have hτ0 : τ 0 = (0 : I) := by apply Subtype.ext; norm_num [τ]
  have hτ1 : τ 1 = (1 : I) := by apply Subtype.ext; norm_num [τ]
  refine ⟨-(θ 1), coordinates_image_closed hm.isClosed,
    hm.isConnected.image _ coordinates_continuous.continuousOn,
    (fun t => θ (τ t)), (fun t => c (τ t)), ?_⟩
  refine ⟨(hθ.comp hτ).continuousOn, (hc.comp hτ).continuousOn,
    by simpa [hτ0] using hθ0, by simp [hτ1], ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    simpa [hτ0, hθ0, hc0, MovingSofa.rot_zero] using
      (coordinates_mem_horizontal p).mpr (hm.initial hp)
  · rintro t ht _ ⟨p, hp, rfl⟩
    rw [← hformula (τ t) p]
    exact (coordinates_mem_hallway _).mpr
      (hm.subset_hallway (τ t) ⟨p, hp, rfl⟩)
  · rintro _ ⟨p, hp, rfl⟩
    rw [hτ1, ← hformula 1 p]
    exact (coordinates_mem_vertical _).mpr (hm.final ⟨p, hp, rfl⟩)

/-- If the given sofa already lies in the horizontal hallway, prepend a
translation to its paper motion. This makes the motion start at the identity
without changing the sofa. -/
theorem paper_with_initial_to_canonical {s : Set Point}
    (hS : MovingSofa.Paper.IsMovingSofa (coordinates '' s))
    (hinitial : s ⊆ MovingSofa.horizontalHallway) :
    ∃ m, MovingSofa.IsMovingSofa s m := by
  obtain ⟨ω, hclosed, hconnected, θ, c, hm⟩ := hS
  have hsclosed : IsClosed s := by
    simpa only [point_coordinates_image] using point_image_closed hclosed
  have hsconnected : IsConnected s := by
    simpa only [point_coordinates_image] using
      hconnected.image _ point_continuous.continuousOn
  have hθ : Continuous (fun t : I => θ t) :=
    hm.continuousOn_angle.comp_continuous continuous_subtype_val (fun t => t.property)
  have hc : Continuous (fun t : I => c t) :=
    hm.continuousOn_shift.comp_continuous continuous_subtype_val (fun t => t.property)
  let τ : I → I := fun t =>
    ⟨max 0 (2 * (t : ℝ) - 1), le_max_left _ _,
      max_le zero_le_one (by linarith [t.property.2])⟩
  let λ : I → ℝ := fun t => min (2 * (t : ℝ)) 1
  have hτ : Continuous τ := by unfold τ; fun_prop
  have hλ : Continuous λ := by unfold λ; fun_prop
  have hλbounds (t : I) : 0 ≤ λ t ∧ λ t ≤ 1 := by
    exact ⟨le_min (by linarith [t.property.1]) zero_le_one, min_le_right _ _⟩
  have hτ0 : τ 0 = (0 : I) := by apply Subtype.ext; norm_num [τ]
  have hτ1 : τ 1 = (1 : I) := by apply Subtype.ext; norm_num [τ]
  have hλ0 : λ 0 = 0 := by norm_num [λ]
  have hλ1 : λ 1 = 1 := by norm_num [λ]
  let m : I → Motion := fun t => realization (θ (τ t), λ t • c (τ t))
  have hmcont : Continuous m :=
    realization_continuous.comp ((hθ.comp hτ).prodMk (hλ.smul (hc.comp hτ)))
  have hformula (t : I) (p : Point) :
      coordinates (m t p) = MovingSofa.rot (θ (τ t)) (coordinates p) +
        λ t • c (τ t) := realization_coordinates _ _
  have hmzero : m 0 = AffineIsometryEquiv.refl ℝ Point := by
    apply AffineIsometryEquiv.ext
    intro p
    apply coordinates_injective
    rw [hformula]
    simp [hτ0, hλ0, hm.angle_zero, MovingSofa.rot_zero]
  refine ⟨m, hsconnected, hsclosed, hmcont, hmzero, hinitial, ?_, ?_⟩
  · rintro t _ ⟨p, hp, rfl⟩
    apply (coordinates_mem_hallway _).mp
    rw [hformula]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have hτt : τ t = (0 : I) := by
        apply Subtype.ext
        simp only [τ]
        exact max_eq_left (by linarith)
      rw [hτt, hm.angle_zero, MovingSofa.rot_zero]
      left
      have hstart := hm.start (coordinates p) ⟨p, hp, rfl⟩
      rw [hm.angle_zero, MovingSofa.rot_zero] at hstart
      have hfirst : coordinates p ∈ MovingSofa.horizSide :=
        (coordinates_mem_horizontal p).mpr (hinitial hp)
      have h := MovingSofa.ang_horizSide_combo
        (p := coordinates p) (a := (0 : CoordinatePlane)) (b := c 0)
        (by simpa using hfirst) hstart (hλbounds t).1 (hλbounds t).2
      simpa only [smul_zero, zero_add] using h
    · have hλt : λ t = 1 := min_eq_right (by linarith [not_le.mp ht])
      rw [hλt, one_smul]
      exact hm.inside (τ t) (τ t).property (coordinates p) ⟨p, hp, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply (coordinates_mem_vertical _).mp
    rw [hformula, hτ1, hλ1, one_smul]
    exact hm.finish (coordinates p) ⟨p, hp, rfl⟩

/-- Exact relationship between the two definitions on a specified Euclidean set.
The initial-placement condition is necessary and has not been suppressed. -/
theorem canonical_iff_paper (s : Set Point) :
    (∃ m, MovingSofa.IsMovingSofa s m) ↔
      s ⊆ MovingSofa.horizontalHallway ∧
        MovingSofa.Paper.IsMovingSofa (coordinates '' s) := by
  constructor
  · intro hs
    exact ⟨by obtain ⟨m, hm⟩ := hs; exact hm.initial, canonical_to_paper hs⟩
  · rintro ⟨hinit, hpaper⟩
    exact paper_with_initial_to_canonical hpaper hinit

/-- An arbitrary paper sofa has an explicitly translated canonical placement. -/
theorem paper_to_canonical_placement {S : Set CoordinatePlane}
    (hS : MovingSofa.Paper.IsMovingSofa S) :
    ∃ v : CoordinatePlane,
      (∃ m, MovingSofa.IsMovingSofa (point '' ((fun p => p + v) '' S)) m) ∧
        volume (point '' ((fun p => p + v) '' S)) = volume S := by
  obtain ⟨ω, hclosed, hconnected, θ, c, hm⟩ := hS
  have hmove : MovingSofa.IsMovingSofaWithAngle S ω :=
    ⟨hclosed, hconnected, θ, c, hm⟩
  have hplaced := MovingSofa.mpc_isMovingSofaWithAngle_translate hmove (c 0)
  refine ⟨c 0, ?_, ?_⟩
  · apply paper_with_initial_to_canonical
    · rw [coordinates_point_image]
      exact ⟨ω, hplaced⟩
    · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      apply (coordinates_mem_horizontal _).mp
      simpa only [coordinates_point, hm.angle_zero, MovingSofa.rot_zero] using
        hm.start p hp
  · rw [volume_point_image]
    exact SofaUniqueness.Draft.volume_translate (c 0) S

/-- The volume-only consequence used to compare the two supremum problems. -/
theorem paper_to_canonical {S : Set CoordinatePlane}
    (hS : MovingSofa.Paper.IsMovingSofa S) :
    ∃ s : Set Point, (∃ m, MovingSofa.IsMovingSofa s m) ∧ volume s = volume S := by
  obtain ⟨v, hv, hvol⟩ := paper_to_canonical_placement hS
  exact ⟨point '' ((fun p => p + v) '' S), hv, hvol⟩

/-- The paper problem's supremum in exact ENNReal volume. -/
def paperConstant : ℝ≥0∞ :=
  ⨆ (S : Set CoordinatePlane) (_ : MovingSofa.Paper.IsMovingSofa S), volume S

/-- Both presentations define precisely the same extremal value.
This theorem is independent of the uniqueness conjecture and Gerver's formulas. -/
theorem sofaConstant_eq_paperConstant : MovingSofa.sofaConstant = paperConstant := by
  apply le_antisymm
  · unfold MovingSofa.sofaConstant
    refine iSup_le fun s => iSup_le fun hs => ?_
    rw [← volume_coordinates_image s]
    exact le_iSup₂ (α := ℝ≥0∞) (coordinates '' s) (canonical_to_paper hs)
  · unfold paperConstant
    refine iSup_le fun S => iSup_le fun hS => ?_
    obtain ⟨s, hs, hvol⟩ := paper_to_canonical hS
    rw [← hvol]
    exact MovingSofa.Canonical.volume_le_constant hs

end SofaUniqueness.Bridge
