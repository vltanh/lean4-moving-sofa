module

public import MovingSofaUniquenessFC.AffineRecovery
public import MovingSofaUniquenessFC.Coordinates
public import MovingSofaUniqueness.Rigidity.SquareGap
import Mathlib

/-!
# Regression examples for the uniqueness foundations

The final example has the affine-isometry type required by formal-conjectures,
but retains the explicit geometric containment hypothesis of
`volume_eq_iff_congruent_of_containment`.
-/

@[expose] public section

open Real Set MeasureTheory
open scoped ENNReal

namespace MovingSofaUniquenessFC.Tests

open MovingSofaUniqueness

/-- Exact recovery applies to a closed full-measure subset of a real interval. -/
example {s : Set ℝ} (hs : IsClosed s) (hsub : s ⊆ Icc (0 : ℝ) 1)
    (hv : volume s = volume (Icc (0 : ℝ) 1)) : s = Icc (0 : ℝ) 1 := by
  apply eq_of_subset_of_measure_eq hs hsub ?_ ?_ hv
  · rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  · simp

/-- Dropping closedness would make set recovery false. -/
example : volume (Ioo (0 : ℝ) 1) = volume (Icc (0 : ℝ) 1) ∧
    Ioo (0 : ℝ) 1 ≠ Icc (0 : ℝ) 1 := by
  constructor
  · simp
  · intro h
    have hz : (0 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      rw [h]
      norm_num
    norm_num at hz

/-- Equal infinite measures do not suffice, even for a closed subset. -/
example : IsClosed (Ici (0 : ℝ)) ∧ Ici (0 : ℝ) ⊆ univ ∧
    volume (Ici (0 : ℝ)) = volume (univ : Set ℝ) ∧ Ici (0 : ℝ) ≠ univ := by
  refine ⟨isClosed_Ici, subset_univ _, ?_, ?_⟩
  · simp
  · intro h
    have hx : (-1 : ℝ) ∈ Ici (0 : ℝ) := by
      rw [h]
      exact mem_univ _
    norm_num at hx

/-- The coordinate inverse really reads both coordinates. -/
example (x y : ℝ) :
    planeToPair.symm (x, y) 0 = x ∧ planeToPair.symm (x, y) 1 = y :=
  ⟨rfl, rfl⟩

/-- The coordinate bridge transports canonical volume, not an arbitrary scalar
multiple of it. -/
example (s : Set EuclideanPlane) : volume (planeToPair '' s) = volume s :=
  volume_image_planeToPair s

/-- A nonzero scalar energy sanity check. -/
example : halfSquareIntegral (Measure.dirac (0 : ℝ)) (fun _ => (2 : ℝ)) = 2 := by
  norm_num [halfSquareIntegral]

/-- The square gap is strictly positive for genuinely different displacements. -/
example :
    (1 / 2 : ℝ) * halfSquareIntegral (Measure.dirac (0 : ℝ)) (fun _ => (1 : ℝ)) +
      (1 / 2 : ℝ) * halfSquareIntegral (Measure.dirac (0 : ℝ)) (fun _ => (2 : ℝ)) -
      halfSquareIntegral (Measure.dirac (0 : ℝ)) (fun _ => (3 / 2 : ℝ)) = 1 / 8 := by
  norm_num [halfSquareIntegral]

/-- A cosine is a nonzero solution of every tangent-translation equation. -/
theorem cosine_tangent_equation (T t : ℝ) :
    sin (T - t) * (-sin t) + cos (T - t) * cos t = cos T := by
  have h := Real.cos_add (T - t) t
  rw [sub_add_cancel] at h
  nlinarith

/-- All affine isometries, including reflections, preserve volume. -/
example (g : EuclideanPlane ≃ᵃⁱ[ℝ] EuclideanPlane) (G : Set EuclideanPlane) :
    volume (g '' G) = volume G :=
  volume_image_affineIsometry g G

/-- The target's exact type of congruence is accepted by the recovery lemma.
The still-needed geometric containment is an explicit argument. -/
example {s G : Set EuclideanPlane} {c : ℝ≥0∞}
    (hs : IsClosed s) (hregular : closure (interior G) = G)
    (hfinite : volume G ≠ ⊤) (hc : c = volume G)
    (hcontain : volume s = c →
      ∃ g : EuclideanPlane ≃ᵃⁱ[ℝ] EuclideanPlane, g '' s ⊆ G) :
    volume s = c ↔ ∃ g : EuclideanPlane ≃ᵃⁱ[ℝ] EuclideanPlane, s = g '' G :=
  volume_eq_iff_congruent_of_containment hs hregular hfinite hc hcontain

end MovingSofaUniquenessFC.Tests
