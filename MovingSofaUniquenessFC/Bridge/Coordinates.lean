module

public import MovingSofaUniquenessFC.Model
public import MovingSofaUniqueness.Rigid

/-!
# One coordinate bridge for the paper and formal-conjectures presentations

Both sets of definitions coexist in this ordinary Lean module. The paper's
kernel names are qualified explicitly; no source relocation, textual insertion,
or runtime generation is required. The map is a homeomorphism and preserves
Lebesgue volume. It is not an isometry for the ordinary product norm.

Uncompiled proof scripts; no admitted statements in this module.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory
open scoped EuclideanGeometry

namespace MovingSofaUniquenessFC.Bridge

open MovingSofaUniqueness

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev CoordinatePlane := ℝ × ℝ
abbrev Motion := Point ≃ᵃⁱ[ℝ] Point

def coordinates (p : Point) : CoordinatePlane := (p 0, p 1)
def point (p : CoordinatePlane) : Point := !₂[p.1, p.2]

@[simp] theorem coordinates_point (p : CoordinatePlane) :
    coordinates (point p) = p := by
  rcases p with ⟨x, y⟩
  rfl

@[simp] theorem point_coordinates (p : Point) : point (coordinates p) = p := by
  ext i
  fin_cases i <;> rfl

theorem coordinates_injective : Function.Injective coordinates := by
  intro p q h
  have he := congrArg point h
  simpa using he

theorem coordinates_continuous : Continuous coordinates := by
  unfold coordinates
  fun_prop

theorem point_continuous : Continuous point := by
  unfold point
  fun_prop

/-- The coordinate equivalence preserves the topology, not the product norm. -/
def coordinatesHomeomorph : Point ≃ₜ CoordinatePlane where
  toFun := coordinates
  invFun := point
  left_inv := point_coordinates
  right_inv := coordinates_point
  continuous_toFun := coordinates_continuous
  continuous_invFun := point_continuous

/-- The canonical measure equivalence used for the volume calculation. -/
def coordinatesMeasurableEquiv : Point ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem coordinates_measurePreserving :
    MeasurePreserving coordinates (volume : Measure Point) volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

@[simp] theorem point_coordinates_image (s : Set Point) :
    point '' (coordinates '' s) = s := by
  rw [Set.image_image]
  simp only [point_coordinates, Set.image_id']

@[simp] theorem coordinates_point_image (s : Set CoordinatePlane) :
    coordinates '' (point '' s) = s := by
  rw [Set.image_image]
  simp only [coordinates_point, Set.image_id']

theorem volume_coordinates_image (s : Set Point) :
    volume (coordinates '' s) = volume s := by
  have h := coordinates_measurePreserving.measure_preimage_emb
    coordinatesMeasurableEquiv.measurableEmbedding (coordinates '' s)
  rw [Set.preimage_image_eq s coordinates_injective] at h
  exact h.symm

theorem volume_point_image (s : Set CoordinatePlane) :
    volume (point '' s) = volume s := by
  have h := volume_coordinates_image (point '' s)
  rw [coordinates_point_image] at h
  exact h.symm

theorem coordinates_image_closed {s : Set Point} (hs : IsClosed s) :
    IsClosed (coordinates '' s) := by
  have he : coordinates '' s = point ⁻¹' s := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨point p, hp, coordinates_point p⟩
  rw [he]
  exact hs.preimage point_continuous

theorem point_image_closed {s : Set CoordinatePlane} (hs : IsClosed s) :
    IsClosed (point '' s) := by
  have he : point '' s = coordinates ⁻¹' s := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨coordinates p, hp, point_coordinates p⟩
  rw [he]
  exact hs.preimage coordinates_continuous

theorem coordinates_mem_horizontal (p : Point) :
    coordinates p ∈ MovingSofaOptimality.horizSide ↔ p ∈ MovingSofa.horizontalHallway := by
  rw [MovingSofa.Canonical.mem_horizontal_iff]
  rfl

theorem coordinates_mem_vertical (p : Point) :
    coordinates p ∈ MovingSofaOptimality.vertSide ↔ p ∈ MovingSofa.verticalHallway := by
  rw [MovingSofa.Canonical.mem_vertical_iff]
  rfl

theorem coordinates_mem_hallway (p : Point) :
    coordinates p ∈ MovingSofaOptimality.hallway ↔ p ∈ MovingSofa.hallway := by
  simp only [MovingSofaOptimality.hallway, MovingSofa.hallway, Set.mem_union,
    coordinates_mem_horizontal, coordinates_mem_vertical]

end MovingSofaUniquenessFC.Bridge
