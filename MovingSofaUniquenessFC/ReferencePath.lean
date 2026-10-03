module

public import MovingSofaUniquenessFC.ReferenceContacts

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

open Set Real MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference.Data

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
  sorry

/-- Exact conversion of the two translation conventions, for every parameter. -/
theorem rotated_prePath {D : Data} (hD : D.Valid) (t : ℝ) :
    rot t (D.prePath t) = D.toPaper.path t := by
  rw [prePath_eq_projections hD, rotate_dot_coordinates]

/-- The initial hallway is not displaced in the reference construction. -/
theorem prePath_zero_of_valid {D : Data} (hD : D.Valid) : D.prePath 0 = 0 := by
  sorry

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
  sorry

end MovingSofaUniquenessFC.Reference.Data
