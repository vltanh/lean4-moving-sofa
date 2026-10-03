module

public import Mathlib
public import MovingSofaUniquenessFC.ReferenceExistence

/-!
# The definitions of the Challenge

The definitions that `Challenge.lean` states its theorems with: those of Baek's paper, in the
namespace `MovingSofaChallenge`, and those of formal-conjectures, in its namespace `MovingSofa`.
`scripts/sync_challenge_defs.py` copies the two marked blocks verbatim into `Challenge.lean`, which
may not import the project. The Solution and the libraries use these constants, so Comparator sees
the same constants in the Challenge and in the Solution. Only `ABφθSpec.existsUnique`, between the
blocks, differs: the Challenge states it, and this module proves it with the analytic argument of
`MovingSofaUniquenessFC.Reference.spec_existsUnique`.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS 1
open Real Set MeasureTheory

namespace MovingSofaChallenge

/-- The counterclockwise rotation of the plane by the angle `t`. -/
noncomputable def rot (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cos t * p.1 - sin t * p.2, sin t * p.1 + cos t * p.2)

/-- The horizontal side `H_L = (-∞, 1] × [0, 1]` of the hallway. -/
def horizSide : Set (ℝ × ℝ) := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- The vertical side `V_L = [0, 1] × (-∞, 1]` of the hallway. -/
def vertSide : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- The hallway `L = H_L ∪ V_L`. -/
def hallway : Set (ℝ × ℝ) := horizSide ∪ vertSide

/-- A moving sofa: a nonempty, connected, closed set that a continuous rigid motion moves inside the
hallway from its horizontal side to its vertical side. -/
def IsMovingSofa (S : Set (ℝ × ℝ)) : Prop :=
  IsClosed S ∧ IsConnected S ∧
    ∃ (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ), ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
      θ 0 = 0 ∧ (∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway) ∧
      (∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide)

/-- The unit vector `u_t = (cos t, sin t)`. -/
noncomputable def uvec (t : ℝ) : ℝ × ℝ := (cos t, sin t)

/-- The unit vector `v_t = (-sin t, cos t)`. -/
noncomputable def vvec (t : ℝ) : ℝ × ℝ := (-sin t, cos t)

/-- The dot product. -/
def dot (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- The parameters of Romik's description of Gerver's sofa. -/
structure GerverParams where
  φ : ℝ
  θ : ℝ
  a₁ : ℝ
  a₂ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  c₁ : ℝ
  c₂ : ℝ
  d₁ : ℝ
  d₂ : ℝ
  e₁ : ℝ
  e₂ : ℝ
  κ₁ : ℝ × ℝ
  κ₂ : ℝ × ℝ
  κ₃ : ℝ × ℝ
  κ₄ : ℝ × ℝ
  κ₅ : ℝ × ℝ

namespace GerverParams

variable (P : GerverParams)

/-- Romik's solution (SOL1) on the first phase. -/
noncomputable def x₁ (t : ℝ) : ℝ × ℝ :=
  rot t (P.a₁ * cos t + P.a₂ * sin t - 1, -P.a₂ * cos t + P.a₁ * sin t - 1 / 2) + P.κ₁
/-- Romik's solution (SOL2) on the second phase. -/
noncomputable def x₂ (t : ℝ) : ℝ × ℝ :=
  rot t (-t ^ 2 / 4 + P.b₁ * t + P.b₂, t / 2 - P.b₁ - 1) + P.κ₂
/-- Romik's solution (SOL3) on the third phase. -/
noncomputable def x₃ (t : ℝ) : ℝ × ℝ := rot t (P.c₁ - t, P.c₂ + t) + P.κ₃
/-- Romik's solution (SOL4) on the fourth phase. -/
noncomputable def x₄ (t : ℝ) : ℝ × ℝ :=
  rot t (-t / 2 + P.d₁ - 1, -t ^ 2 / 4 + P.d₁ * t + P.d₂) + P.κ₄
/-- Romik's solution (SOL5) on the fifth phase. -/
noncomputable def x₅ (t : ℝ) : ℝ × ℝ :=
  rot t (P.e₁ * cos t + P.e₂ * sin t - 1 / 2, -P.e₂ * cos t + P.e₁ * sin t - 1) + P.κ₅

/-- Gerver's rotation path (Romik's Equation (25)). -/
noncomputable def path (t : ℝ) : ℝ × ℝ :=
  if t < P.φ then P.x₁ t
  else if t < P.θ then P.x₂ t
  else if t ≤ π / 2 - P.θ then P.x₃ t
  else if t ≤ π / 2 - P.φ then P.x₄ t
  else P.x₅ t

/-- The contact path `𝐁(t) = 𝐱(t) + ⟨𝐱'(t), u_t⟩ v_t` (Romik's Equation (10)). -/
noncomputable def contactB (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ := x t + dot (deriv x t) (uvec t) • vvec t

/-- The contact path `𝐃(t) = 𝐱(t) - ⟨𝐱'(t), v_t⟩ u_t` (Romik's Equation (12)). -/
noncomputable def contactD (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ := x t - dot (deriv x t) (vvec t) • uvec t

/-- Romik's equations (27)–(44), with `0 < φ < θ < π/4`. -/
def IsSolution : Prop :=
  0 < P.φ ∧ P.φ < P.θ ∧ P.θ < π / 4 ∧
  P.e₁ = P.a₁ ∧ P.e₂ = -P.a₂ ∧ P.d₁ = π / 4 - P.b₁ ∧
  P.d₂ = P.b₂ + π / 4 * (2 * P.b₁ - π / 4) ∧ P.c₂ = P.c₁ - π / 2 ∧
  P.κ₁.1 = 1 - P.a₁ ∧ P.κ₁.2 = 1 / 4 ∧ P.a₂ = -1 / 4 ∧
  P.x₁ P.φ = P.x₂ P.φ ∧ deriv P.x₁ P.φ = deriv P.x₂ P.φ ∧
  P.x₂ P.θ = P.x₃ P.θ ∧ deriv P.x₂ P.θ = deriv P.x₃ P.θ ∧
  P.x₃ (π / 2 - P.θ) = P.x₄ (π / 2 - P.θ) ∧ deriv P.x₃ (π / 2 - P.θ) = deriv P.x₄ (π / 2 - P.θ) ∧
  P.x₄ (π / 2 - P.φ) = P.x₅ (π / 2 - P.φ) ∧ deriv P.x₄ (π / 2 - P.φ) = deriv P.x₅ (π / 2 - P.φ) ∧
  P.x₁ P.φ = contactB P.x₄ (π / 2 - P.θ) ∧ P.x₅ (π / 2 - P.φ) = contactD P.x₂ P.θ

/-- The range of parameters: `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`. -/
def InBox : Prop := P.φ ∈ Icc (0.039 : ℝ) 0.04 ∧ P.θ ∈ Icc (0.68 : ℝ) 0.69

end GerverParams

/-- The shape of a rotation path `𝐱` (Romik's Equation (8)). -/
def shapeOfPath (x : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  horizSide ∩ (⋂ t ∈ Icc 0 (π / 2), (fun p => x t + rot t p) '' hallway) ∩
    (fun p => x (π / 2) + rot (π / 2) p) '' vertSide

/-- Gerver's sofa. -/
def gerverSofa (P : GerverParams) : Set (ℝ × ℝ) := shapeOfPath P.path

end MovingSofaChallenge

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable section

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology of formal-conjectures on `E(2)` (an anonymous instance there). -/
instance instTopologicalSpaceAffineIsometryEquivRealEuclideanSpaceFinOfNatNat :
    TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- A connected closed set `s` is a **moving sofa** according to a rigid motion `m : I → E(2)` if
it is initially in the horizontal side of the hallway and ends up in the vertical side. -/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/-- The rigid motion that translates by `p` and then rotates counterclockwise by `α`. -/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/-- The sofa of a rotation path `p : [0, π/2] → ℝ²`: the intersection over `α ∈ [0, π/2]` of the
hallways translated by `p α` and then rotated by `α`, with the horizontal side at `0` and the
vertical side at `π/2`. -/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-- Equations (1)–(4) of Romik (2018), which specify Gerver's constants `A`, `B`, `φ`, `θ`. -/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0
-- END SHARED DEFINITIONS 1

/-- There exist unique constants `A`, `B`, `φ` and `θ` satisfying the system. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 := by
  exact MovingSofaUniquenessFC.Reference.spec_existsUnique

-- BEGIN SHARED DEFINITIONS 2
def A : ℝ := ABφθSpec.existsUnique.choose.1
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

end MovingSofa

end
-- END SHARED DEFINITIONS 2
