module

public import MovingSofaStability.PunctureTopology
public import MovingSofaStability.InteriorBalls
public import MovingSofaBridge.Motion
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Euclidean disks in the repository's product coordinates

The product metric is not used for disk radii or areas. The existing
measure-preserving coordinate bridge supplies the exact Euclidean disk area,
while a homeomorphism transports connectedness.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory Metric
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev EuclideanPoint := EuclideanSpace ℝ (Fin 2)

/-- The existing coordinate equivalence, equipped with its proved topology. -/
def diskCoordinates : EuclideanPoint ≃ₜ Point where
  toFun := MovingSofaBridge.coordinates
  invFun := MovingSofaBridge.point
  left_inv := MovingSofaBridge.point_coordinates
  right_inv := MovingSofaBridge.coordinates_point
  continuous_toFun := MovingSofaBridge.coordinates_continuous
  continuous_invFun := MovingSofaBridge.point_continuous

@[simp] theorem euclideanDist_coordinates (p q : EuclideanPoint) :
    euclideanDist (diskCoordinates p) (diskCoordinates q) = dist p q := by
  rw [euclideanDist, dist_eq_norm]
  apply (sq_eq_sq₀ (norm2_nonneg _) (norm_nonneg _)).mp
  rw [norm2_sq, MovingSofaBridge.norm_sq_coordinates]
  change dot (MovingSofaBridge.coordinates p - MovingSofaBridge.coordinates q)
    (MovingSofaBridge.coordinates p - MovingSofaBridge.coordinates q) = _
  simp only [MovingSofaBridge.coordinates, dot, Prod.fst_sub, Prod.snd_sub, PiLp.sub_apply]
  ring

@[simp] theorem dist_inverse_coordinates (p q : Point) :
    dist (diskCoordinates.symm p) (diskCoordinates.symm q) = euclideanDist p q := by
  rw [← euclideanDist_coordinates]
  simp

/-- An open Euclidean disk; `euclideanBall` in the recovery files is closed. -/
def openEuclideanBall (p : Point) (r : ℝ) : Set Point :=
  {q | euclideanDist p q < r}

def euclideanSphere (p : Point) (r : ℝ) : Set Point :=
  {q | euclideanDist p q = r}

/-- The punctured set retains the circle. -/
def puncture (S : Set Point) (p : Point) (r : ℝ) : Set Point :=
  S \ openEuclideanBall p r

@[simp] theorem coordinates_image_ball (p : Point) (r : ℝ) :
    diskCoordinates '' ball (diskCoordinates.symm p) r = openEuclideanBall p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) < r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) < r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

@[simp] theorem coordinates_image_closedBall (p : Point) (r : ℝ) :
    diskCoordinates '' closedBall (diskCoordinates.symm p) r = euclideanBall p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) ≤ r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) ≤ r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

@[simp] theorem coordinates_image_sphere (p : Point) (r : ℝ) :
    diskCoordinates '' sphere (diskCoordinates.symm p) r = euclideanSphere p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    change euclideanDist p (diskCoordinates x) = r
    rw [← diskCoordinates.apply_symm_apply p, euclideanDist_coordinates, dist_comm]
    exact hx
  · intro hq
    refine ⟨diskCoordinates.symm q, ?_, by simp⟩
    change dist (diskCoordinates.symm q) (diskCoordinates.symm p) = r
    rw [dist_inverse_coordinates, euclideanDist_comm]
    exact hq

theorem openEuclideanBall_isOpen (p : Point) (r : ℝ) : IsOpen (openEuclideanBall p r) := by
  rw [← coordinates_image_ball]
  exact diskCoordinates.isOpenMap _ isOpen_ball

theorem euclideanBall_isCompact (p : Point) (r : ℝ) : IsCompact (euclideanBall p r) := by
  rw [← coordinates_image_closedBall]
  exact (isCompact_closedBall _ _).image diskCoordinates.continuous

/-- Exact area, with no sup-norm disk substitution. -/
theorem area_openEuclideanBall (p : Point) {r : ℝ} (hr : 0 ≤ r) :
    area (openEuclideanBall p r) = π * r ^ 2 := by
  rw [← coordinates_image_ball]
  change (volume (MovingSofaBridge.coordinates '' ball (diskCoordinates.symm p) r)).toReal = _
  rw [MovingSofaBridge.volume_coordinates_image, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal pi_pos.le]
  ring

theorem euclideanSphere_connected (p : Point) {r : ℝ} (hr : 0 ≤ r) :
    IsConnected (euclideanSphere p r) := by
  rw [← coordinates_image_sphere]
  exact (isConnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by simp) : 1 < Module.rank ℝ EuclideanPoint)
    (diskCoordinates.symm p) hr).image _ diskCoordinates.continuous.continuousOn

theorem puncture_isCompact {S : Set Point} (hS : IsCompact S) (p : Point) (r : ℝ) :
    IsCompact (puncture S p r) := hS.diff (openEuclideanBall_isOpen p r)

/-- This uses connectedness, not a stronger unproved path-connectedness hypothesis. -/
theorem puncture_connected {S : Set Point} (hS : IsClosed S) (hconn : IsConnected S)
    {p : Point} {r : ℝ} (hr : 0 < r) (hball : euclideanBall p r ⊆ S) :
    IsConnected (puncture S p r) := by
  let T := diskCoordinates.symm '' S
  have hTclosed : IsClosed T := diskCoordinates.symm.isClosedMap _ hS
  have hTconn : IsConnected T := hconn.image _ diskCoordinates.symm.continuous.continuousOn
  have hTball : closedBall (diskCoordinates.symm p) r ⊆ T := by
    intro q hq
    have hq' : diskCoordinates q ∈ euclideanBall p r := by
      rw [← coordinates_image_closedBall]
      exact mem_image_of_mem _ hq
    exact ⟨diskCoordinates q, hball hq', by simp⟩
  have h := connected_sdiff_ball
    (Module.one_lt_rank_of_one_lt_finrank (by simp) : 1 < Module.rank ℝ EuclideanPoint)
    hTclosed hTconn hr hTball
  have he : diskCoordinates '' (T \ ball (diskCoordinates.symm p) r) = puncture S p r := by
    rw [image_sdiff diskCoordinates.injective, coordinates_image_ball]
    simp only [T, image_image, Homeomorph.apply_symm_apply, image_id', puncture]
  rw [← he]
  exact h.image _ diskCoordinates.continuous.continuousOn

/-- The circle supplies a point on every positive-radius puncture. -/
theorem puncture_nonempty {S : Set Point} {p : Point} {r : ℝ} (hr : 0 ≤ r)
    (hball : euclideanBall p r ⊆ S) : (puncture S p r).Nonempty := by
  obtain ⟨q, hq⟩ := (euclideanSphere_connected p hr).nonempty
  exact ⟨q, hball (show euclideanDist p q ≤ r from hq.le),
    fun h => (show euclideanDist p q < r from h).ne hq⟩

/-- The missing area is exactly the disk area. All measures involved are finite. -/
theorem puncture_area_loss {S : Set Point} (hS : IsCompact S)
    {p : Point} {r : ℝ} (hr : 0 ≤ r) (hball : euclideanBall p r ⊆ S) :
    area S - area (puncture S p r) = π * r ^ 2 := by
  have hsub : openEuclideanBall p r ⊆ S := fun q hq =>
    hball (show euclideanDist p q ≤ r from (show euclideanDist p q < r from hq).le)
  have hi : S ∩ openEuclideanBall p r = openEuclideanBall p r := inter_eq_right.mpr hsub
  have hpart := area_inter_add_sdiff (openEuclideanBall_isOpen p r).measurableSet
    hS.isBounded.measure_lt_top.ne
  rw [hi, area_openEuclideanBall p hr] at hpart
  change area S - area (S \ openEuclideanBall p r) = _
  linarith

end MovingSofaStability
