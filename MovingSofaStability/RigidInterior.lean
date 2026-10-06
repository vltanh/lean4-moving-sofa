module

public import MovingSofaStability.PunctureMetric
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Interior retention on a compact rigid orbit

Uncompiled proof source. The conclusion is special to rigid copies of one fixed
compact set. It is false for arbitrary Hausdorff-close compact sets.

The proof takes subsequences of the cosine/sine coefficients and translations,
not of unrestricted real angles. No trivial-stabilizer assumption is needed.
-/

@[expose] public section
noncomputable section

open Real Set Filter Topology Metric
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

abbrev RotationShift := Point × Point

def rotationShift (g : Rigid) : RotationShift := ((cos g.angle, sin g.angle), g.shift)

def coefficientApply (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * p.1 - z.1.2 * p.2 + z.2.1, z.1.2 * p.1 + z.1.1 * p.2 + z.2.2)

def coefficientInverse (z : RotationShift) (p : Point) : Point :=
  (z.1.1 * (p.1 - z.2.1) + z.1.2 * (p.2 - z.2.2),
    -z.1.2 * (p.1 - z.2.1) + z.1.1 * (p.2 - z.2.2))

@[simp] theorem coefficientApply_rotationShift (g : Rigid) (p : Point) :
    coefficientApply (rotationShift g) p = g p := rfl

@[simp] theorem coefficientInverse_rotationShift (g : Rigid) (p : Point) :
    coefficientInverse (rotationShift g) p = g.symm p := by
  ext <;> simp only [coefficientInverse, rotationShift, Rigid.symm, Rigid.apply,
    rot, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, cos_neg, sin_neg] <;> ring

/-- The limit of the matrix coefficients still defines a homeomorphism. -/
def coefficientHomeomorph (z : RotationShift) (h : z.1.1 ^ 2 + z.1.2 ^ 2 = 1) : Point ≃ₜ Point where
  toFun := coefficientApply z
  invFun := coefficientInverse z
  left_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination p.1 * h
    · linear_combination p.2 * h
  right_inv p := by
    ext <;> dsimp only [coefficientApply, coefficientInverse]
    · linear_combination (p.1 - z.2.1) * h
    · linear_combination (p.2 - z.2.2) * h
  continuous_toFun := by unfold coefficientApply; fun_prop
  continuous_invFun := by unfold coefficientInverse; fun_prop

/-- A closed set contains a limiting point approximated by points of that set. -/
theorem closed_mem_of_euclidean_near {X : Set Point} (hX : IsClosed X) (hne : X.Nonempty)
    {x : ℕ → Point} {p : Point} {δ : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 p)) (hδ : Tendsto δ atTop (𝓝 0))
    (hnear : ∀ n, ∃ q ∈ X, euclideanDist (x n) q ≤ δ n) : p ∈ X := by
  have hupper : ∀ n, infDist (x n) X ≤ δ n := by
    intro n
    obtain ⟨q, hq, hd⟩ := hnear n
    have hm : dist (x n) q ≤ euclideanDist (x n) q := by
      rw [dist_eq_norm]
      exact product_norm_le_norm2 _
    exact (infDist_le_dist_of_mem hq).trans (hm.trans hd)
  have hzero : Tendsto (fun n => infDist (x n) X) atTop (𝓝 0) :=
    squeeze_zero (fun _ => infDist_nonneg) hupper hδ
  have hlim := ((lipschitz_infDist_pt X).continuous.tendsto p).comp hx
  have he : infDist p X = 0 := tendsto_nhds_unique hlim hzero
  rw [← hX.closure_eq]
  exact (mem_closure_iff_infDist_zero hne).mpr he

/-- Closeness of a rigid image bounds its translation uniformly. -/
theorem rigid_shift_bound {X : Set Point} {R δ : ℝ} (hne : X.Nonempty)
    (hR : ∀ x ∈ X, ‖x‖ ≤ R) (hδ : δ ≤ 1) {g : Rigid}
    (hclose : EuclideanClose δ X (g '' X)) : ‖g.shift‖ ≤ 4 * R + 1 := by
  sorry

/-- Every fixed interior point is retained by sufficiently close rigid copies.
No restriction on rotation angle, translation, or symmetries of X is imposed. -/
theorem rigid_copies_retain_interior {X : Set Point} (hX : IsCompact X)
    {p : Point} (hp : p ∈ interior X) :
    ∃ η : ℝ, 0 < η ∧ ∀ g : Rigid, ∀ δ : ℝ,
      δ < η → EuclideanClose δ X (g '' X) → p ∈ g '' X := by
  sorry

end MovingSofaStability
