/- UNCOMPILED INSERTION FRAGMENT.
Insert inside the upstream `namespace MovingSofa`, before the open uniqueness
theorem. The exporter adds imports and relocates the old library to SofaLegacy.
Do not import the original library and the upstream file into the same namespace.
-/

namespace UniquenessDraft

open Set Real MeasureTheory
open scoped unitInterval EuclideanGeometry

abbrev CoordinatePlane := ℝ × ℝ

def coordinates (p : ℝ²) : CoordinatePlane := (p 0, p 1)
def point (p : CoordinatePlane) : ℝ² := !₂[p.1, p.2]

@[simp] theorem coordinates_point (p : CoordinatePlane) : coordinates (point p) = p := by
  rcases p with ⟨x, y⟩
  rfl

@[simp] theorem point_coordinates (p : ℝ²) : point (coordinates p) = p := by
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

/-- This is a measurable equivalence, NOT an isometry for the product norm. -/
def coordinatesMeasurableEquiv : ℝ² ≃ᵐ CoordinatePlane :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem coordinates_measurePreserving :
    MeasurePreserving coordinates (volume : Measure ℝ²) volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

@[simp] theorem point_coordinates_image (s : Set ℝ²) :
    point '' (coordinates '' s) = s := by
  rw [Set.image_image]
  simpa only [Function.comp_def, point_coordinates] using Set.image_id s

@[simp] theorem coordinates_point_image (s : Set CoordinatePlane) :
    coordinates '' (point '' s) = s := by
  rw [Set.image_image]
  simpa only [Function.comp_def, coordinates_point] using Set.image_id s

theorem volume_coordinates_image (s : Set ℝ²) : volume (coordinates '' s) = volume s := by
  have h := coordinates_measurePreserving.measure_preimage_emb
    coordinatesMeasurableEquiv.measurableEmbedding (coordinates '' s)
  rw [Set.preimage_image_eq s coordinates_injective] at h
  exact h.symm

theorem volume_point_image (s : Set CoordinatePlane) : volume (point '' s) = volume s := by
  have h := volume_coordinates_image (point '' s)
  rw [coordinates_point_image] at h
  exact h.symm

theorem coordinates_image_closed {s : Set ℝ²} (hs : IsClosed s) :
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

theorem coordinates_mem_horizontal (p : ℝ²) :
    coordinates p ∈ SofaLegacy.horizSide ↔ p ∈ horizontalHallway := by
  constructor
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy

theorem coordinates_mem_vertical (p : ℝ²) :
    coordinates p ∈ SofaLegacy.vertSide ↔ p ∈ verticalHallway := by
  constructor
  · intro hp
    exact ⟨p 0, p 1, hp, by ext i; fin_cases i <;> rfl⟩
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy

theorem coordinates_mem_hallway (p : ℝ²) :
    coordinates p ∈ SofaLegacy.hallway ↔ p ∈ hallway := by
  simp only [SofaLegacy.hallway, hallway, Set.mem_union,
    coordinates_mem_horizontal, coordinates_mem_vertical]

/-- Rotation FIRST, then translation. This intentionally differs from the
upstream `rotateTranslate`, which translates first. -/
def realization (ac : ℝ × CoordinatePlane) : E(2) :=
  (EuclideanGeometry.o.rotation (ac.1 : Real.Angle)).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ (point ac.2))

/-- DRAFT-B2: coordinate formula for the canonical oriented Euclidean rotation.
Expand `o.rotation` on the two standard basis vectors and prove the formula;
check that the chosen orientation gives the displayed counterclockwise sign.
This is not a comparison of the two Gerver path parameterizations. -/
theorem realization_coordinates (ac : ℝ × CoordinatePlane) (p : ℝ²) :
    coordinates (realization ac p) =
      SofaLegacy.rot ac.1 (coordinates p) + ac.2 := by
  sorry

/-- DRAFT-B3: continuity into the EXACT upstream induced topology on E(2).
Use the continuous matrix entries and translation coordinates in
ContinuousAffineMap; do not silently substitute a different topological-space
instance for the affine isometry equivalences. -/
theorem realization_continuous : Continuous realization := by
  sorry

/-- DRAFT-B1: lift an identity-start path of affine isometries to a continuous
REAL rotation angle, normalized to zero initially.
First prove that the determinant stays +1 by connectedness of I and m(0)=id.
Then lift the resulting circle/SO(2) path; translations are evaluations at zero.
A pointwise `arg` is not a continuous lift. The conclusion is independent of
sofas, optimality and the open theorem. -/
theorem real_angle_lift (m : I → E(2)) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ ℝ²) :
    ∃ (θ : I → ℝ) (c : I → CoordinatePlane), Continuous θ ∧ Continuous c ∧
      θ 0 = 0 ∧ c 0 = 0 ∧ ∀ t p,
        coordinates (m t p) = SofaLegacy.rot (θ t) (coordinates p) + c t := by
  sorry

/-- A coordinate rigid map is realized as a genuine Euclidean affine isometry. -/
def realizeRigid (g : SofaUniqueness.Draft.Rigid) : E(2) :=
  realization (g.angle, g.shift)

theorem realizeRigid_coordinates (g : SofaUniqueness.Draft.Rigid) (p : ℝ²) :
    coordinates (realizeRigid g p) = g (coordinates p) :=
  realization_coordinates (g.angle, g.shift) p

/-- Transport an equality of actual sets, in the target's requested direction. -/
theorem congruent_of_coordinates {s t : Set ℝ²} (g : SofaUniqueness.Draft.Rigid)
    (h : coordinates '' s = g '' (coordinates '' t)) : s = realizeRigid g '' t := by
  have he : point '' (g '' (coordinates '' t)) = realizeRigid g '' t := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext p
    apply coordinates_injective
    simp only [Function.comp_apply, coordinates_point, realizeRigid_coordinates]
  have hp := congrArg (fun u : Set CoordinatePlane => point '' u) h
  rw [point_coordinates_image, he] at hp
  exact hp

end UniquenessDraft
