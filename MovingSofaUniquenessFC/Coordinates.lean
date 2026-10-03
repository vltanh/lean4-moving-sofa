module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Coordinates for the formal-conjectures plane

`EuclideanSpace ℝ (Fin 2)` and `ℝ × ℝ` have the same coordinate topology and
Lebesgue measure, but their default norms are different. This module provides a
homeomorphism and a measure-preserving equivalence. It intentionally does NOT
claim that the coordinate map is an isometry for the product's default norm.

This is a coordinate bridge, not a bridge between the two moving-sofa predicates
or between the two parameterizations of Gerver's sofa.
-/

@[expose] public section

open MeasureTheory Set

namespace SofaUniqueness

/-- The type denoted by `ℝ²` in the formal-conjectures target. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- Read Euclidean coordinates as a pair. -/
noncomputable def planeToPair : EuclideanPlane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

@[simp]
theorem planeToPair_apply (p : EuclideanPlane) : planeToPair p = (p 0, p 1) := rfl

@[simp]
theorem planeToPair_symm_apply_zero (p : ℝ × ℝ) : planeToPair.symm p 0 = p.1 := rfl

@[simp]
theorem planeToPair_symm_apply_one (p : ℝ × ℝ) : planeToPair.symm p 1 = p.2 := rfl

/-- The inverse map in explicit coordinates. -/
theorem planeToPair_symm_apply (p : ℝ × ℝ) :
    planeToPair.symm p = (WithLp.toLp 2 ![p.1, p.2] : EuclideanPlane) := by
  ext i
  fin_cases i <;> rfl

/-- The coordinate map is continuous, without identifying the two norms. -/
theorem continuous_planeToPair : Continuous planeToPair := by
  change Continuous (fun p : EuclideanPlane => (p 0, p 1))
  fun_prop

/-- Continuity of the inverse coordinate map. -/
theorem continuous_planeToPair_symm : Continuous planeToPair.symm := by
  have he : (planeToPair.symm : (ℝ × ℝ) → EuclideanPlane) =
      fun p => WithLp.toLp 2 ![p.1, p.2] :=
    funext planeToPair_symm_apply
  rw [he]
  fun_prop

/-- A homeomorphism sharing its underlying equivalence with `planeToPair`. -/
noncomputable def planeToPairHomeomorph : EuclideanPlane ≃ₜ (ℝ × ℝ) where
  toEquiv := planeToPair.toEquiv
  continuous_toFun := continuous_planeToPair
  continuous_invFun := continuous_planeToPair_symm

/-- The coordinate map preserves canonical volume exactly; there is no
normalization factor. -/
theorem planeToPair_measurePreserving :
    MeasurePreserving planeToPair (volume : Measure EuclideanPlane) volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))

/-- The inverse also preserves volume. -/
theorem planeToPair_symm_measurePreserving :
    MeasurePreserving planeToPair.symm (volume : Measure (ℝ × ℝ)) volume :=
  MeasurePreserving.symm planeToPair planeToPair_measurePreserving

/-- Transfer the volume of any set to pair coordinates. -/
theorem volume_image_planeToPair (s : Set EuclideanPlane) :
    volume (planeToPair '' s) = volume s := by
  have h := planeToPair_measurePreserving.measure_preimage_equiv (planeToPair '' s)
  rw [Set.preimage_image_eq s planeToPair.injective] at h
  exact h.symm

/-- Transfer the volume of any set to Euclidean coordinates. -/
theorem volume_image_planeToPair_symm (s : Set (ℝ × ℝ)) :
    volume (planeToPair.symm '' s) = volume s := by
  have h := planeToPair_symm_measurePreserving.measure_preimage_equiv (planeToPair.symm '' s)
  rw [Set.preimage_image_eq s planeToPair.symm.injective] at h
  exact h.symm

/-- Closedness of a sofa is preserved by changing coordinates. -/
theorem isClosed_image_planeToPair {s : Set EuclideanPlane} (hs : IsClosed s) :
    IsClosed (planeToPair '' s) :=
  planeToPairHomeomorph.isClosedMap s hs

/-- Connectedness of a sofa is preserved by changing coordinates. -/
theorem isConnected_image_planeToPair {s : Set EuclideanPlane} (hs : IsConnected s) :
    IsConnected (planeToPair '' s) :=
  hs.image planeToPair continuous_planeToPair.continuousOn

end SofaUniqueness
