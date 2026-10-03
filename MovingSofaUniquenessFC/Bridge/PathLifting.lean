module

public import MovingSofaUniquenessFC.Bridge.Orientation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting

/-!
# A normalized real angle for an identity-start Euclidean motion

The first column is a continuous circle-valued path. Mathlib's covering-map
path lifting theorem supplies a continuous REAL angle starting at zero.
The determinant argument in `Orientation` determines the second column, and
hence the entire affine map.

Unlike a pointwise choice of `arg`, the path lift remains continuous across
the negative real axis and supports paths with arbitrary winding number.
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
  have hx := continuous_linear_eval basisX
  have h0 : Continuous (fun e : Motion => leftColumn e 0) := by
    unfold leftColumn
    fun_prop
  have h1 : Continuous (fun e : Motion => leftColumn e 1) := by
    unfold leftColumn
    fun_prop
  apply Continuous.subtype_mk
  exact Complex.equivRealProdCLM.symm.continuous.comp (h0.prodMk h1)

/-- Lift a continuous identity-start path into rotations and translations.
The conclusion uses the paper's explicit coordinate rotation. -/
theorem real_angle_lift (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (θ : I → ℝ) (c : I → CoordinatePlane), Continuous θ ∧ Continuous c ∧
      θ 0 = 0 ∧ c 0 = 0 ∧ ∀ t p,
        coordinates (m t p) = MovingSofaOptimality.rot (θ t) (coordinates p) + c t := by
  let γ : C(I, Circle) :=
    ⟨fun t => firstDirection (m t), firstDirection_continuous.comp hm⟩
  have hlin (p : Point) : (AffineIsometryEquiv.refl ℝ Point).linearIsometryEquiv p = p := by
    rw [linear_apply_eq_sub]
    simp
  have hγ0 : γ 0 = Circle.exp 0 := by
    change firstDirection (m 0) = Circle.exp 0
    rw [hzero, Circle.exp_zero]
    apply Circle.ext
    simp [firstDirection, leftColumn, basisX, hlin, Complex.ext_iff]
  obtain ⟨θ, hθ, hθ0⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ 0 hγ0
  refine ⟨θ, fun t => coordinates (m t 0), θ.continuous,
    coordinates_continuous.comp ((continuous_motion_eval 0).comp hm),
    hθ0, ?_, ?_⟩
  · change coordinates (m 0 0) = 0
    rw [hzero]
    rfl
  · intro t p
    have hexp : Circle.exp (θ t) = firstDirection (m t) := congrFun hθ t
    have hc : leftColumn (m t) 0 = cos (θ t) := by
      have h := congrArg (fun z : Circle => Complex.re (z : ℂ)) hexp
      simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] at h
      exact h.symm
    have hs : leftColumn (m t) 1 = sin (θ t) := by
      have h := congrArg (fun z : Circle => Complex.im (z : ℂ)) hexp
      simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] at h
      exact h.symm
    rw [MovingSofaUniquenessFC.affineIsometry_apply_eq,
      linear_eq_euclideanRotate (determinant_eq_one_on_path m hm hzero t) hc hs p,
      coordinates_add, euclideanRotate_coordinates]

/-- A constant identity path is compatible with the required normalization. -/
theorem identity_has_zero_angle :
    ∀ _t : I, ∀ p : Point,
      coordinates ((AffineIsometryEquiv.refl ℝ Point) p) =
        MovingSofaOptimality.rot (0 : ℝ) (coordinates p) + (0 : CoordinatePlane) := by
  intro _ p
  simp [MovingSofaOptimality.rot_zero]

end MovingSofaUniquenessFC.Bridge
