module

public import MovingSofaUniquenessFC.ReferenceEquations
public import MovingSofaOptimality.Gerver.Frame

/-!
# The integral Gerver reference, with explicit parameters

`Data.radius`, `boundaryX`, `boundaryY`, and `prePath` are the mathematical
bodies of the formal-conjectures definitions `r`, `x`, `y`, and `p`, with their
four constants made explicit. No parameter-selection theorem is assumed here.
The choices of `<=` at the breakpoints and the two special endpoint hallways
are retained. The Euclidean coordinate wrapper is a separate bridge.

In particular, the reference translates BEFORE rotating. The paper uses a
translation AFTER rotating. `shape_eq_of_rotated_path` proves the exact
conversion, including the initial hallway; merely equating the two paths
without rotating the translation would be wrong.

Uncompiled source. No decision procedure or external proof script is used.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofaOptimality

namespace MovingSofaUniquenessFC.Reference

structure Data where
  A : ℝ
  B : ℝ
  φ : ℝ
  θ : ℝ

namespace Data

variable (D : Data)

def Valid : Prop := Spec D.A D.B D.φ D.θ

def radius (t : ℝ) : ℝ :=
  if t ≤ D.φ then 1 / 2
  else if t ≤ D.θ then (1 + D.A + t - D.φ) / 2
  else if t ≤ π / 2 - D.θ then D.A + t - D.φ
  else if t ≤ π / 2 - D.φ then
    D.B - (π / 2 - t - D.φ) * (1 + D.A) / 2 - (π / 2 - t - D.φ) ^ 2 / 4
  else 0

def boundaryY (t : ℝ) : ℝ :=
  ∫ s in t..π / 2 - D.φ, D.radius s * sin s

def boundaryX (t : ℝ) : ℝ :=
  1 - ∫ s in t..π / 2 - D.φ, D.radius s * cos s

def prePath (t : ℝ) : ℝ × ℝ :=
  (if t ≤ D.φ then cos t - 1
   else D.boundaryX (π / 2 - t) * cos t +
     D.boundaryY (π / 2 - t) * sin t - 1,
   if t ≤ π / 2 - D.φ then
     D.boundaryY t * cos t - (4 * D.boundaryX 0 - 2 - D.boundaryX t) * sin t - 1
   else -(4 * D.boundaryX 0 - 3) * sin t - 1)

@[simp] theorem boundaryX_end : D.boundaryX (π / 2 - D.φ) = 1 := by
  simp [boundaryX]

@[simp] theorem boundaryY_end : D.boundaryY (π / 2 - D.φ) = 0 := by
  simp [boundaryY]

/-- The initial translation is zero once the integral height is one.
This identity is not assumed from the reference's name. -/
theorem prePath_zero (hφ : 0 ≤ D.φ) (hφL : D.φ ≤ π / 2)
    (hy : D.boundaryY 0 = 1) : D.prePath 0 = 0 := by
  sorry

end Data

/-- The coordinate version of upstream `rotateTranslate`. -/
def rotateTranslatePair (t : ℝ) (p q : ℝ × ℝ) : ℝ × ℝ := rot t (q + p)

/-- The special endpoint hallway intersections are part of the definition. -/
def shapeFromPrePath (p : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  rotateTranslatePair 0 (p 0) '' horizSide ∩
  rotateTranslatePair (π / 2) (p (π / 2)) '' vertSide ∩
  ⋂ t ∈ Icc 0 (π / 2), rotateTranslatePair t (p t) '' MovingSofaOptimality.hallway

def Data.shape (D : Data) : Set (ℝ × ℝ) := shapeFromPrePath D.prePath

/-- The rotating-frame coordinates uniquely determine the translation. -/
theorem rotate_dot_coordinates (t : ℝ) (q : ℝ × ℝ) :
    rot t (dot q (uvec t), dot q (vvec t)) = q := by
  sorry

/-- Convert the whole reference shape, not just its intermediate hallways.
The horizontal start is fixed only because `p 0 = 0` is proved separately. -/
theorem shape_eq_of_rotated_path {p x : ℝ → ℝ × ℝ}
    (hzero : p 0 = 0)
    (hpath : ∀ t ∈ Icc 0 (π / 2), rot t (p t) = x t) :
    shapeFromPrePath p = shapeOfPath x := by
  sorry

end MovingSofaUniquenessFC.Reference
