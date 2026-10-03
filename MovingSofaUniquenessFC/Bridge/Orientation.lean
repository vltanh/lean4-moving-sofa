module

public import MovingSofaUniquenessFC.Bridge.EuclideanRigid
public import MovingSofaUniquenessFC.AffineRecovery
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Orientation of an identity-start planar isometry path

The sign of the two-by-two determinant is obtained from continuity and the
intermediate value theorem. No pointwise choice of an angle or discontinuous
argument function is used.

The proofs use only the Euclidean norm, linearity, and elementary real algebra.
-/

@[expose] public section
noncomputable section

open Set Real
open scoped unitInterval EuclideanGeometry

namespace MovingSofaUniquenessFC.Bridge

open MovingSofaUniqueness

def basisX : Point := !₂[1, 0]
def basisY : Point := !₂[0, 1]
def leftColumn (e : Motion) : Point := e.linearIsometryEquiv basisX
def rightColumn (e : Motion) : Point := e.linearIsometryEquiv basisY

def determinant (e : Motion) : ℝ :=
  leftColumn e 0 * rightColumn e 1 - leftColumn e 1 * rightColumn e 0

/-- Evaluation is continuous for the model's declared induced topology. -/
theorem continuous_motion_eval (p : Point) : Continuous (fun e : Motion => e p) := by
  have h : Continuous (fun e : Motion =>
      e.toAffineIsometry.toContinuousAffineMap) := continuous_induced_dom
  have h2 : Continuous (fun f : Point →ᴬ[ℝ] Point => f p) := continuous_eval_const p
  exact h2.comp h

theorem linear_apply_eq_sub (e : Motion) (p : Point) :
    e.linearIsometryEquiv p = e p - e 0 := by
  apply eq_sub_iff_add_eq.mpr
  exact (MovingSofaUniquenessFC.affineIsometry_apply_eq e p).symm

/-- The linear evaluation is a difference of two continuous affine evaluations. -/
theorem continuous_linear_eval (p : Point) :
    Continuous (fun e : Motion => e.linearIsometryEquiv p) := by
  simp_rw [linear_apply_eq_sub]
  exact (continuous_motion_eval p).sub (continuous_motion_eval 0)

/-- The two columns are orthonormal. This is proved through squared norms. -/
theorem column_laws (e : Motion) :
    (leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2 = 1 ∧
    (rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2 = 1 ∧
    leftColumn e 0 * rightColumn e 0 + leftColumn e 1 * rightColumn e 1 = 0 := by
  have hx : (leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (e.linearIsometryEquiv.norm_map basisX)
    rw [norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [leftColumn, basisX] using h
  have hy : (rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (e.linearIsometryEquiv.norm_map basisY)
    rw [norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [rightColumn, basisY] using h
  have hsum : (leftColumn e 0 + rightColumn e 0) ^ 2 +
      (leftColumn e 1 + rightColumn e 1) ^ 2 = 2 := by
    have h := congrArg (fun r : ℝ => r ^ 2)
      (e.linearIsometryEquiv.norm_map (basisX + basisY))
    rw [e.linearIsometryEquiv.map_add, norm_sq_coordinates, norm_sq_coordinates] at h
    simpa [leftColumn, rightColumn, basisX, basisY, one_add_one_eq_two] using h
  exact ⟨hx, hy, by nlinarith⟩

/-- The determinant cannot vanish: its square is one. -/
theorem determinant_sq (e : Motion) : determinant e ^ 2 = 1 := by
  obtain ⟨hx, hy, hxy⟩ := column_laws e
  calc
    _ = ((leftColumn e 0) ^ 2 + (leftColumn e 1) ^ 2) *
        ((rightColumn e 0) ^ 2 + (rightColumn e 1) ^ 2) -
        (leftColumn e 0 * rightColumn e 0 +
          leftColumn e 1 * rightColumn e 1) ^ 2 := by
      unfold determinant
      ring
    _ = 1 := by rw [hx, hy, hxy]; norm_num

theorem determinant_continuous : Continuous determinant := by
  have hx := continuous_linear_eval basisX
  have hy := continuous_linear_eval basisY
  unfold determinant leftColumn rightColumn
  fun_prop

/-- A continuous path from the identity has determinant +1 at every time. -/
theorem determinant_eq_one_on_path (m : I → Motion) (hm : Continuous m)
    (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    determinant (m t) = 1 := by
  have hd0 : determinant (m 0) = 1 := by
    have hlin (p : Point) : (AffineIsometryEquiv.refl ℝ Point).linearIsometryEquiv p = p := by
      rw [linear_apply_eq_sub]
      simp
    rw [hzero]
    norm_num [determinant, leftColumn, rightColumn, hlin, basisX, basisY]
  have hc := determinant_continuous.comp hm
  have hpos : 0 < determinant (m t) := by
    by_contra h
    have hle : determinant (m t) ≤ 0 := le_of_not_gt h
    obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hc
      (show (0 : ℝ) ∈ Icc (determinant (m t)) (determinant (m 0)) from
        ⟨hle, by rw [hd0]; norm_num⟩)
    have hs := determinant_sq (m u)
    rw [show determinant (m u) = 0 from hu] at hs
    norm_num at hs
  have hs := determinant_sq (m t)
  nlinarith

/-- For determinant +1, the second column is the first column rotated by pi/2. -/
theorem rightColumn_of_determinant_one {e : Motion} (he : determinant e = 1) :
    rightColumn e 0 = -leftColumn e 1 ∧ rightColumn e 1 = leftColumn e 0 := by
  obtain ⟨hx, hy, _⟩ := column_laws e
  unfold determinant at he
  have hsum : (rightColumn e 0 + leftColumn e 1) ^ 2 +
      (rightColumn e 1 - leftColumn e 0) ^ 2 = 0 := by nlinarith
  have h0 : (rightColumn e 0 + leftColumn e 1) ^ 2 = 0 :=
    le_antisymm (by nlinarith [sq_nonneg (rightColumn e 1 - leftColumn e 0)])
      (sq_nonneg _)
  have h1 : (rightColumn e 1 - leftColumn e 0) ^ 2 = 0 :=
    le_antisymm (by nlinarith [sq_nonneg (rightColumn e 0 + leftColumn e 1)])
      (sq_nonneg _)
  have h0' := sq_eq_zero_iff.mp h0
  have h1' := sq_eq_zero_iff.mp h1
  constructor <;> linarith

/-- The first column and positive orientation determine the linear isometry. -/
theorem linear_eq_euclideanRotate {e : Motion} {t : ℝ}
    (he : determinant e = 1) (hc : leftColumn e 0 = cos t)
    (hs : leftColumn e 1 = sin t) (p : Point) :
    e.linearIsometryEquiv p = euclideanRotate t p := by
  obtain ⟨h0, h1⟩ := rightColumn_of_determinant_one he
  have hp : p = (p 0) • basisX + (p 1) • basisY := by
    ext i
    fin_cases i <;> simp [basisX, basisY]
  have hl : e.linearIsometryEquiv p =
      (p 0) • leftColumn e + (p 1) • rightColumn e := by
    calc
      _ = e.linearIsometryEquiv ((p 0) • basisX + (p 1) • basisY) :=
        congrArg e.linearIsometryEquiv hp
      _ = _ := by simp only [map_add, map_smul, leftColumn, rightColumn]
  rw [hl]
  ext i
  fin_cases i <;> simp [euclideanRotate, h0, h1, hc, hs] <;> ring

end MovingSofaUniquenessFC.Bridge
