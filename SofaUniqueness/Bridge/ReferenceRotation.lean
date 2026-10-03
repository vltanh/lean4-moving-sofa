module

public import SofaSubmission.ReferenceDefs
public import SofaUniqueness.Bridge.EuclideanRigid
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# The actual oriented rotation used in the upstream concrete reference

Constructing an arbitrary Euclidean isometry was sufficient for transporting
motions, but not for identifying the specific reference's `rotateTranslate`.
Here the sign of its canonical orientation is proved from the determinant of
the standard orthonormal basis. Its right-angle rotation sends e0 to e1 and
e1 to -e0; therefore its coordinate matrix is exactly the paper rotation.

No orientation correspondence is postulated. Uncompiled source.
-/

@[expose] public section
noncomputable section

open Module Set Real
open scoped EuclideanGeometry RealInnerProductSpace

namespace SofaUniqueness.Bridge

private def referenceBasis : OrthonormalBasis (Fin 2) ℝ Point :=
  EuclideanSpace.basisFun (Fin 2) ℝ

private theorem referenceBasis_orientation :
    referenceBasis.toBasis.orientation = EuclideanGeometry.o := by
  rfl

private theorem referenceBasis_area :
    EuclideanGeometry.o.areaForm (referenceBasis 0) (referenceBasis 1) = 1 := by
  rw [Orientation.areaForm_to_volumeForm,
    Orientation.volumeForm_robust _ referenceBasis referenceBasis_orientation]
  have he : ![referenceBasis 0, referenceBasis 1] = (referenceBasis : Fin 2 → Point) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact referenceBasis.toBasis.det_self

private theorem reference_quarterTurn_zero :
    EuclideanGeometry.o.rightAngleRotation (referenceBasis 0) = referenceBasis 1 := by
  apply PiLp.ext
  intro i
  fin_cases i
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_self (referenceBasis 0)
    change inner ℝ (EuclideanGeometry.o.rightAngleRotation (referenceBasis 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 0 at h
    rw [EuclideanSpace.inner_basisFun] at h
    simpa [referenceBasis, EuclideanSpace.basisFun_apply] using h
  · have h := EuclideanGeometry.o.inner_rightAngleRotation_left
      (referenceBasis 0) (referenceBasis 1)
    rw [referenceBasis_area] at h
    change inner ℝ (EuclideanGeometry.o.rightAngleRotation (referenceBasis 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 1 at h
    rw [EuclideanSpace.inner_basisFun] at h
    simpa [referenceBasis, EuclideanSpace.basisFun_apply] using h

private theorem reference_quarterTurn_one :
    EuclideanGeometry.o.rightAngleRotation (referenceBasis 1) = -referenceBasis 0 := by
  have h := EuclideanGeometry.o.rightAngleRotation_rightAngleRotation (referenceBasis 0)
  rwa [reference_quarterTurn_zero] at h

private theorem referenceBasis_expansion (q : Point) :
    q = q 0 • referenceBasis 0 + q 1 • referenceBasis 1 := by
  ext i
  fin_cases i <;> simp [referenceBasis, EuclideanSpace.basisFun_apply]

/-- Quarter-turn coordinates for the SAME orientation used in the definition. -/
theorem reference_quarterTurn_coordinates (q : Point) :
    coordinates (EuclideanGeometry.o.rightAngleRotation q) = (-(q 1), q 0) := by
  conv_lhs => rw [referenceBasis_expansion q]
  rw [map_add, map_smul, map_smul, reference_quarterTurn_zero, reference_quarterTurn_one]
  ext <;> simp [coordinates, referenceBasis, EuclideanSpace.basisFun_apply]

/-- Canonical oriented rotation equals the paper's coordinate rotation. -/
theorem reference_rotation_coordinates (t : ℝ) (q : Point) :
    coordinates (EuclideanGeometry.o.rotation (t : Real.Angle) q) =
      MovingSofa.rot t (coordinates q) := by
  rw [Orientation.rotation_apply, coordinates_add, coordinates_smul, coordinates_smul,
    reference_quarterTurn_coordinates]
  ext <;> simp [MovingSofa.rot, coordinates] <;> ring

/-- This is the exact upstream map, not a replacement realization. -/
theorem reference_rotateTranslate_coordinates (t : ℝ) (p q : Point) :
    coordinates (MovingSofa.rotateTranslate (t : Real.Angle) p q) =
      MovingSofa.rot t (coordinates q + coordinates p) := by
  rw [MovingSofa.rotateTranslate_apply, reference_rotation_coordinates, coordinates_add]

end SofaUniqueness.Bridge
