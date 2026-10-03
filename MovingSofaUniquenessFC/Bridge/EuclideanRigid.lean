module

public import MovingSofaUniquenessFC.Bridge.Coordinates
public import Mathlib.Topology.Algebra.ContinuousAffineMap.Topology

/-!
# Explicit Euclidean realization of the paper's rigid maps

The target asks for an affine isometry, not for a particular construction of
that isometry. We construct the usual rotation matrix directly on Euclidean
space instead of using Mathlib's oriented rotation, so its coordinate formula
is definitional; preservation of the Euclidean norm is proved algebraically.

Continuity is proved into the exact induced topology used by the canonical
motion model, using the value at zero and the continuous linear part, without
replacing that topology by pointwise convergence.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory
open scoped EuclideanGeometry

namespace MovingSofaUniquenessFC.Bridge

open MovingSofaUniqueness

@[simp] theorem coordinates_add (p q : Point) :
    coordinates (p + q) = coordinates p + coordinates q := rfl

@[simp] theorem coordinates_smul (a : ℝ) (p : Point) :
    coordinates (a • p) = a • coordinates p := rfl

@[simp] theorem coordinates_zero : coordinates (0 : Point) = 0 := rfl

/-- Squared Euclidean norm in the two standard coordinates. -/
theorem norm_sq_coordinates (p : Point) : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (∑ i : Fin 2, p i * p i) = (p 0) ^ 2 + (p 1) ^ 2
  simp [Fin.sum_univ_two, pow_two]

def euclideanRotate (t : ℝ) (p : Point) : Point :=
  !₂[cos t * p 0 - sin t * p 1, sin t * p 0 + cos t * p 1]

@[simp] theorem euclideanRotate_coordinates (t : ℝ) (p : Point) :
    coordinates (euclideanRotate t p) = MovingSofaOptimality.rot t (coordinates p) := rfl

/-- This uses the Euclidean norm; no product-norm isometry is asserted. -/
theorem euclideanRotate_norm (t : ℝ) (p : Point) :
    ‖euclideanRotate t p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coordinates, norm_sq_coordinates]
  change (cos t * p 0 - sin t * p 1) ^ 2 +
      (sin t * p 0 + cos t * p 1) ^ 2 = (p 0) ^ 2 + (p 1) ^ 2
  calc
    _ = (sin t ^ 2 + cos t ^ 2) * ((p 0) ^ 2 + (p 1) ^ 2) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq, one_mul]

def rotationLinearEquiv (t : ℝ) : Point ≃ₗ[ℝ] Point where
  toFun := euclideanRotate t
  invFun := euclideanRotate (-t)
  left_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, MovingSofaOptimality.rot_neg_rot]
  right_inv p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, MovingSofaOptimality.rot_rot_neg]
  map_add' p q := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, coordinates_add, MovingSofaOptimality.rot_add_vec]
  map_smul' a p := by
    apply coordinates_injective
    simp only [euclideanRotate_coordinates, coordinates_smul, MovingSofaOptimality.rot_smul,
      RingHom.id_apply]

def rotation (t : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  { rotationLinearEquiv t with norm_map' := euclideanRotate_norm t }

/-- Rotate first and then translate, matching the paper convention. -/
def realization (ac : ℝ × CoordinatePlane) : Motion :=
  (rotation ac.1).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ (point ac.2))

/-- The coordinate action is the specified rotation and translation. -/
theorem realization_coordinates (ac : ℝ × CoordinatePlane) (p : Point) :
    coordinates (realization ac p) = MovingSofaOptimality.rot ac.1 (coordinates p) + ac.2 := by
  change coordinates (euclideanRotate ac.1 p + point ac.2) = _
  rw [coordinates_add, euclideanRotate_coordinates, coordinates_point]

/-- A fixed quarter-turn as a continuous linear map. -/
def quarterTurn : Point →L[ℝ] Point where
  toFun p := !₂[-p 1, p 0]
  map_add' p q := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp
  cont := by fun_prop

/-- Decomposition into the value at zero and the continuous linear part. -/
theorem realization_toContinuousAffineMap (ac : ℝ × CoordinatePlane) :
    (realization ac).toAffineIsometry.toContinuousAffineMap =
      (ContinuousAffineMap.decompHomeomorph ℝ Point Point).symm
        (point ac.2, cos ac.1 • (ContinuousLinearMap.id ℝ Point) +
          sin ac.1 • quarterTurn) := by
  ext p : 1
  apply coordinates_injective
  change coordinates (realization ac p) = _
  rw [realization_coordinates,
    ContinuousAffineMap.decompHomeomorph_symm_apply]
  change MovingSofaOptimality.rot ac.1 (coordinates p) + ac.2 =
    coordinates ((cos ac.1 • p + sin ac.1 • quarterTurn p) + point ac.2)
  ext <;> simp [MovingSofaOptimality.rot, coordinates, quarterTurn, point] <;> ring

/-- Continuity uses precisely the canonical model's induced topology. -/
theorem realization_continuous : Continuous realization := by
  apply continuous_induced_rng.mpr
  change Continuous (fun ac : ℝ × CoordinatePlane =>
    (realization ac).toAffineIsometry.toContinuousAffineMap)
  simp_rw [realization_toContinuousAffineMap]
  apply (ContinuousAffineMap.decompHomeomorph ℝ Point Point).symm.continuous.comp
  exact (point_continuous.comp continuous_snd).prodMk
    (((Real.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.continuous_sin.comp continuous_fst).smul continuous_const))

/-- The library's coordinate rigid map as an actual Euclidean affine isometry. -/
def realizeRigid (g : MovingSofaUniqueness.Rigid) : Motion :=
  realization (g.angle, g.shift)

theorem realizeRigid_coordinates (g : MovingSofaUniqueness.Rigid) (p : Point) :
    coordinates (realizeRigid g p) = g (coordinates p) :=
  realization_coordinates (g.angle, g.shift) p

/-- Transfer actual set equality in the direction requested upstream. -/
theorem congruent_of_coordinates {s t : Set Point} (g : MovingSofaUniqueness.Rigid)
    (h : coordinates '' s = g '' (coordinates '' t)) : s = realizeRigid g '' t := by
  have he : point '' (g '' (coordinates '' t)) = realizeRigid g '' t := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext p
    apply coordinates_injective
    simp only [coordinates_point, realizeRigid_coordinates]
  have hp := congrArg (fun u : Set CoordinatePlane => point '' u) h
  rw [point_coordinates_image, he] at hp
  exact hp

end MovingSofaUniquenessFC.Bridge
