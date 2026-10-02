module

public import SofaUniqueness.Bridge.Orientation
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

namespace SofaUniqueness.Bridge

/-- The first column of a Euclidean isometry, viewed as a unit complex number. -/
def firstDirection (e : Motion) : Circle :=
  ⟨⟨leftColumn e 0, leftColumn e 1⟩, by
    apply Metric.mem_sphere_zero_iff_norm.mpr
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [Complex.sq_norm]
    simpa [Complex.normSq_apply, pow_two] using (column_laws e).1⟩

theorem firstDirection_continuous : Continuous firstDirection := by
  have hx := continuous_linear_eval basisX
  unfold firstDirection leftColumn
  apply Continuous.subtype_mk
  fun_prop

/-- Lift a continuous identity-start path into rotations and translations.
The conclusion uses the paper's explicit coordinate rotation. -/
theorem real_angle_lift (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (θ : I → ℝ) (c : I → CoordinatePlane), Continuous θ ∧ Continuous c ∧
      θ 0 = 0 ∧ c 0 = 0 ∧ ∀ t p,
        coordinates (m t p) = MovingSofa.rot (θ t) (coordinates p) + c t := by
  let γ : C(I, Circle) :=
    ⟨fun t => firstDirection (m t), firstDirection_continuous.comp hm⟩
  have hγ0 : γ 0 = Circle.exp 0 := by
    apply Circle.ext
    simp [γ, firstDirection, leftColumn, basisX, hzero]
  obtain ⟨θ, hθ, hθ0⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ 0 hγ0
  refine ⟨θ, fun t => coordinates (m t 0), θ.continuous,
    coordinates_continuous.comp ((continuous_motion_eval 0).comp hm),
    hθ0, ?_, ?_⟩
  · rw [hzero]
    rfl
  · intro t p
    have hexp : Circle.exp (θ t) = firstDirection (m t) := congrFun hθ t
    have hc : leftColumn (m t) 0 = cos (θ t) := by
      have h := congrArg (fun z : Circle => Complex.re (z : ℂ)) hexp
      simpa [firstDirection, Circle.coe_exp, Complex.exp_mul_I] using h.symm
    have hs : leftColumn (m t) 1 = sin (θ t) := by
      have h := congrArg (fun z : Circle => Complex.im (z : ℂ)) hexp
      simpa [firstDirection, Circle.coe_exp, Complex.exp_mul_I] using h.symm
    rw [SofaUniqueness.affineIsometry_apply_eq,
      linear_eq_euclideanRotate (determinant_eq_one_on_path m hm hzero t) hc hs p,
      coordinates_add, euclideanRotate_coordinates]

/-- A constant identity path is compatible with the required normalization. -/
theorem identity_has_zero_angle :
    ∀ t : I, ∀ p : Point,
      coordinates ((AffineIsometryEquiv.refl ℝ Point) p) =
        MovingSofa.rot (0 : ℝ) (coordinates p) + (0 : CoordinatePlane) := by
  intro t p
  simp [MovingSofa.rot_zero]

end SofaUniqueness.Bridge
