module

public import MovingSofaUniquenessFC.Bridge.ReferenceRotation
public import MovingSofaUniquenessFC.ReferencePath

/-!
# Equality of the two concrete Gerver definitions

This bridge follows the actual upstream definitions through coordinates,
including the orientation, the before-rotation translation, every interior
hallway, and both endpoint hallways. The result is equality with the paper
Gerver set after the canonical coordinate identification, not just congruence
or equality of volume. No sofa-uniqueness theorem is imported or used.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa MovingSofaOptimality
open scoped EuclideanGeometry

namespace MovingSofaUniquenessFC.Bridge

open MovingSofaUniqueness

/-- The explicit-parameter model has the literal reference's radius. -/
theorem reference_radius (t : ℝ) : GerversSofa.referenceData.radius t = GerversSofa.r t := rfl

theorem reference_boundaryX (t : ℝ) : GerversSofa.referenceData.boundaryX t = GerversSofa.x t := rfl

theorem reference_boundaryY (t : ℝ) : GerversSofa.referenceData.boundaryY t = GerversSofa.y t := rfl

/-- No identity between the two paths is assumed in this definitional step. -/
theorem reference_prePath (t : ℝ) :
    coordinates (GerversSofa.p t) = GerversSofa.referenceData.prePath t := rfl

/-- Membership in the image of any one of the reference's actual hallways. -/
private theorem reference_image_iff (t : ℝ) (q : Point)
    (A : Set Point) (B : Set CoordinatePlane)
    (hAB : ∀ p, coordinates p ∈ B ↔ p ∈ A) :
    q ∈ MovingSofa.rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' A ↔
      coordinates q ∈ Reference.rotateTranslatePair t
        (GerversSofa.referenceData.prePath t) '' B := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordinates p, (hAB p).mpr hp, ?_⟩
    rw [reference_rotateTranslate_coordinates, reference_prePath]
    rfl
  · rintro ⟨p, hp, heq⟩
    refine ⟨point p, (hAB (point p)).mp (by simpa using hp), ?_⟩
    apply coordinates_injective
    rw [reference_rotateTranslate_coordinates, reference_prePath, coordinates_point]
    exact heq

/-- The two special endpoint intersections are transferred separately. -/
theorem mem_reference_iff (q : Point) :
    q ∈ MovingSofa.gerversSofa ↔ coordinates q ∈ GerversSofa.referenceData.shape := by
  have hH := reference_image_iff 0 q MovingSofa.horizontalHallway MovingSofaOptimality.horizSide
    coordinates_mem_horizontal
  have hV := reference_image_iff (π / 2) q MovingSofa.verticalHallway MovingSofaOptimality.vertSide
    coordinates_mem_vertical
  have hL := fun t => reference_image_iff t q MovingSofa.hallway MovingSofaOptimality.hallway
    coordinates_mem_hallway
  simp only [MovingSofa.gerversSofa, MovingSofa.sofaOfRotateTranslatePath,
    Reference.Data.shape, Reference.shapeFromPrePath, mem_inter_iff, mem_iInter] at ⊢
  constructor
  · rintro ⟨⟨hh, hv⟩, hall⟩
    exact ⟨⟨hH.mp hh, hV.mp hv⟩, fun t ht => (hL t).mp (hall t ht)⟩
  · rintro ⟨⟨hh, hv⟩, hall⟩
    exact ⟨⟨hH.mpr hh, hV.mpr hv⟩, fun t ht => (hL t).mpr (hall t ht)⟩

theorem coordinates_reference_shape :
    coordinates '' MovingSofa.gerversSofa = GerversSofa.referenceData.shape := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_reference_iff p).mp hp
  · intro hq
    refine ⟨point q, (mem_reference_iff (point q)).mpr (by simpa using hq), coordinates_point q⟩

/-- Main concrete bridge: the EXACT upstream set is the paper's Gerver sofa
in canonical pair coordinates, for every valid paper parameter witness. -/
theorem coordinates_gerversSofa_eq_paper {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    coordinates '' MovingSofa.gerversSofa = MovingSofaOptimality.gerverSofa P := by
  rw [coordinates_reference_shape]
  exact Reference.Data.shape_eq_paper_witness GerversSofa.referenceData_valid hP hbox

/-- The inverse-coordinate version used in Euclidean-space statements. -/
theorem gerversSofa_eq_point_paper {P : MovingSofaOptimality.GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofa.gerversSofa = point '' MovingSofaOptimality.gerverSofa P := by
  have h := congrArg (fun S : Set CoordinatePlane => point '' S)
    (coordinates_gerversSofa_eq_paper hP hbox)
  simpa only [point_coordinates_image] using h

/-- The concrete upstream initial translation vanishes, as required to leave
the horizontal endpoint hallway in its original position. -/
theorem reference_p_zero : GerversSofa.p 0 = 0 := by
  apply coordinates_injective
  rw [reference_prePath]
  exact Reference.Data.prePath_zero_of_valid GerversSofa.referenceData_valid

/-- Membership in the initial hallway is obtained from its exact definition. -/
theorem gerversSofa_subset_horizontal :
    MovingSofa.gerversSofa ⊆ MovingSofa.horizontalHallway := by
  intro q hq
  have hstart : q ∈ MovingSofa.rotateTranslate 0 (GerversSofa.p 0) '' MovingSofa.horizontalHallway :=
    hq.1.1
  rcases hstart with ⟨p, hp, rfl⟩
  simpa only [reference_p_zero, MovingSofa.rotateTranslate_apply, add_zero,
    Orientation.rotation_zero, LinearIsometryEquiv.coe_refl, id] using hp

end MovingSofaUniquenessFC.Bridge
