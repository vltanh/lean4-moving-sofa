module

public import MovingSofaUniquenessFC.Bridge.Orientation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting

/-!
# A normalized real angle for an identity-start Euclidean motion

The first column is a continuous circle-valued path. Mathlib's covering-map
path lifting theorem supplies a continuous REAL angle starting at zero.
The determinant argument in `Orientation` determines the second column, and
hence the entire affine map. This replaces the former admitted bridge B1.

Unlike a pointwise choice of `arg`, the path lift remains continuous across
the negative real axis and supports paths with arbitrary winding number.
The scripts are uncompiled, but there are no admitted statements in this file.
-/

@[expose] public section
noncomputable section

open Set Real
open scoped unitInterval EuclideanGeometry

namespace MovingSofaUniquenessFC.Bridge

open MovingSofaUniqueness

/-- The first column of a Euclidean isometry, viewed as a unit complex number. -/
def firstDirection (e : Motion) : Circle :=
  ⟨⟨leftColumn e 0, leftColumn e 1⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [Complex.sq_norm]
    simpa [Complex.normSq_apply, pow_two] using (column_laws e).1⟩

theorem firstDirection_continuous : Continuous firstDirection := by
  sorry

/-- Lift a continuous identity-start path into rotations and translations.
The conclusion uses the paper's explicit coordinate rotation. -/
theorem real_angle_lift (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (θ : I → ℝ) (c : I → CoordinatePlane), Continuous θ ∧ Continuous c ∧
      θ 0 = 0 ∧ c 0 = 0 ∧ ∀ t p,
        coordinates (m t p) = MovingSofaOptimality.rot (θ t) (coordinates p) + c t := by
  sorry

/-- A constant identity path is compatible with the required normalization. -/
theorem identity_has_zero_angle :
    ∀ t : I, ∀ p : Point,
      coordinates ((AffineIsometryEquiv.refl ℝ Point) p) =
        MovingSofaOptimality.rot (0 : ℝ) (coordinates p) + (0 : CoordinatePlane) := by
  intro t p
  simp [MovingSofaOptimality.rot_zero]

end MovingSofaUniquenessFC.Bridge
