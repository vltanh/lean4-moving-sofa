module

public import SofaUniqueness.ReferenceContacts

/-!
# The two concrete Gerver paths and shapes agree in coordinates

The upstream p(t) is a translation BEFORE rotation. Its coordinates are
exactly the two rotating-frame projections of the paper's AFTER-rotation
translation x(t). Thus R_t p(t)=x(t), not p(t)=x(t).

This module proves equality of the sets with the two special endpoint
hallways retained. It does not use the uniqueness theorem for moving sofas.
All scripts remain uncompiled.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa MovingSofa.GerverParams

namespace SofaUniqueness.Reference.Data

private theorem contactA_projection (D : Data) (t : ℝ) :
    dot (contactA D.toPaper.path t) (uvec t) = dot (D.toPaper.path t) (uvec t) + 1 := by
  rw [contactA, dot_add_left, dot_add_left, dot_smul_left,
    dot_vvec_uvec, dot_uvec_self]
  ring

private theorem contactC_projection (D : Data) (t : ℝ) :
    dot (contactC D.toPaper.path t) (vvec t) = dot (D.toPaper.path t) (vvec t) + 1 := by
  rw [contactC, dot_add_left, dot_sub_left, dot_smul_left,
    dot_uvec_vvec, dot_vvec_self]
  ring

/-- The literal upstream pre-rotation translation, including all branch cases. -/
theorem prePath_eq_projections {D : Data} (hD : D.Valid) (t : ℝ) :
    D.prePath t = (dot (D.toPaper.path t) (uvec t), dot (D.toPaper.path t) (vvec t)) := by
  have hA := contactA_projection D t
  have hC := contactC_projection D t
  ext
  · change (if t ≤ D.φ then cos t - 1 else
        D.boundaryX (π / 2 - t) * cos t + D.boundaryY (π / 2 - t) * sin t - 1) = _
    by_cases ht : t ≤ D.φ
    · rw [if_pos ht]
      rw [contactA_first hD ht] at hA
      simp only [dot, uvec, mul_one, one_mul, zero_mul, add_zero] at hA
      linarith
    · rw [if_neg ht]
      rw [contactA_integral_coordinates hD] at hA
      change D.boundaryX (π / 2 - t) * cos t + D.boundaryY (π / 2 - t) * sin t =
        dot (D.toPaper.path t) (uvec t) + 1 at hA
      linarith
  · change (if t ≤ π / 2 - D.φ then
        D.boundaryY t * cos t - (4 * D.boundaryX 0 - 2 - D.boundaryX t) * sin t - 1
      else -(4 * D.boundaryX 0 - 3) * sin t - 1) = _
    by_cases ht : t ≤ π / 2 - D.φ
    · rw [if_pos ht]
      rw [contactC_integral_coordinates hD, horizontal_normalization hD] at hC
      change (4 * D.boundaryX 0 - 2 - D.boundaryX t) * (-sin t) +
        D.boundaryY t * cos t = dot (D.toPaper.path t) (vvec t) + 1 at hC
      nlinarith
    · rw [if_neg ht]
      rw [contactC_last hD (lt_of_not_ge ht).le, horizontal_normalization hD] at hC
      change (4 * D.boundaryX 0 - 2 - 1) * (-sin t) + 0 * cos t =
        dot (D.toPaper.path t) (vvec t) + 1 at hC
      nlinarith

/-- Exact conversion of the two translation conventions, for every parameter. -/
theorem rotated_prePath {D : Data} (hD : D.Valid) (t : ℝ) :
    rot t (D.prePath t) = D.toPaper.path t := by
  rw [prePath_eq_projections hD, rotate_dot_coordinates]

/-- The initial hallway is not displaced in the reference construction. -/
theorem prePath_zero_of_valid {D : Data} (hD : D.Valid) : D.prePath 0 = 0 := by
  have h := rotated_prePath hD 0
  rw [rot_zero, gs_path_zero hD.paper_solution.1] at h
  exact h

/-- Exact set equality with the paper construction, not merely equal area. -/
theorem shape_eq_gerverSofa {D : Data} (hD : D.Valid) :
    D.shape = gerverSofa D.toPaper := by
  exact shape_eq_of_rotated_path (prePath_zero_of_valid hD)
    (fun t _ => rotated_prePath hD t)

/-- The same statement for ANY specified solution of the paper system in its
box. Global parameter uniqueness identifies the parameters; shape uniqueness
plays no role in the correspondence. -/
theorem shape_eq_paper_witness {D : Data} (hD : D.Valid) {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) : D.shape = gerverSofa P := by
  rw [shape_eq_gerverSofa hD, hD.eq_ofPaper hP hbox, ofPaper_toPaper hP]

end SofaUniqueness.Reference.Data
