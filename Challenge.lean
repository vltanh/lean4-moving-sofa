module

public import Mathlib

/-!
# The moving sofa problem: Gerver's sofa has maximum area, is the only such sofa, and is stable

Statements of record, in Mathlib's vocabulary only, in three groups.

* `Baek`: the definitions of Jineon Baek, *Optimality of Gerver's Sofa* (arXiv:2411.19826v1), the
  paper's main theorem (Theorem 1.1.1), and the uniqueness of the optimal sofa up to rigid motions and
  its stability, which the paper does not prove (the arguments are in
  `docs/archive/uniqueness/20-complete-paper-proof.md` and `docs/stability.md`).
* `FormalConjectures.MovingSofa`: the definitions and statements of Google DeepMind's
  formal-conjectures, including its uniqueness statement, which it lists as open.
* `Bridge`: the two sets of definitions describe the same objects. Formal-conjectures' statements
  follow from Baek's through these three theorems.

## Baek's definitions (namespace `Baek`)

**The plane** is `ℝ × ℝ`, and the area of a set is its Lebesgue measure `volume`. **The hallway**
`L = H_L ∪ V_L` is the union of its horizontal side `H_L = (-∞, 1] × [0, 1]` and its vertical side
`V_L = [0, 1] × (-∞, 1]`.

**A moving sofa** is a nonempty, connected, closed set `S ⊆ ℝ²` that can be moved inside `L` by a
continuous rigid motion from `H_L` to `V_L`: there are a continuous angle `θ` and a continuous
translation `c` on `[0, 1]` such that, writing `Φ_s(p) = R_{θ(s)} p + c(s)` with `R_θ` the
counterclockwise rotation by `θ`, the map `Φ_0` is a translation (`θ(0) = 0`), `Φ_0(S) ⊆ H_L`,
`Φ_s(S) ⊆ L` for all `s ∈ [0, 1]`, and `Φ_1(S) ⊆ V_L`.

**Gerver's sofa** is given by Romik's description (*Differential equations and exact solutions in the
moving sofa problem*, Experimental Mathematics 2018, Section 4): its rotation path `𝐱 : [0, π/2] → ℝ²`
is glued from the five explicit families `𝐱_1, …, 𝐱_5` below on the phases `[0, φ)`, `[φ, θ)`,
`[θ, π/2 - θ]`, `(π/2 - θ, π/2 - φ]` and `(π/2 - φ, π/2]`, whose 22 parameters satisfy Romik's
equations (27)–(44): left-right symmetry, `𝐀(0) = (1, 0)` and `𝐱(0) = 0`, continuous
differentiability at the phase boundaries, and the two contact conditions
`𝐱_1(φ) = 𝐁(π/2 - θ)` and `𝐱_5(π/2 - φ) = 𝐃(θ)` for the contact paths
`𝐁(t) = 𝐱(t) + ⟨𝐱'(t), u_t⟩ v_t` and `𝐃(t) = 𝐱(t) - ⟨𝐱'(t), v_t⟩ u_t`, where `u_t = (cos t, sin t)`
and `v_t = (-sin t, cos t)`. Gerver's sofa is the shape
`S_𝐱 = H_L ∩ ⋂_{t ∈ [0, π/2]} (𝐱(t) + R_t(L)) ∩ (𝐱(π/2) + R_{π/2}(V_L))` of this rotation path
(Romik's Equation (8)). Romik's numerical solution has `φ = 0.03917…` and `θ = 0.68130…`; we consider
the solutions with `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`, and state that there is exactly one.

**The theorems.** `gerver_params_exists` and `gerver_params_unique`: Romik's system has exactly one
solution in this range, so Gerver's sofa is well defined. `gerver_sofa_area`: its area is between
`2.2192` and `2.2199`, which identifies the shape with the sofa of area `2.21953…` that Gerver found.
`gerver_sofa_optimal`: Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. `gerver_sofa_unique`: a rotation about the origin followed by a translation maps
every moving sofa with the area of Gerver's sofa exactly onto Gerver's sofa.

**Stability.** The deficit `sofaDeficit P S` of a moving sofa `S` is the area of Gerver's sofa minus
the area of `S`. `normalizedSofa P S` translates `S` so that its highest point has height `1` and its
leftmost point the abscissa of the leftmost point of Gerver's sofa. `EuclideanClose r S T` says that
every point of each set lies within Euclidean distance `r` of a point of the other, and
`IsMovingSofaWithAngle S ω` that `S` is a moving sofa whose motion turns it clockwise by `ω`.
`gerver_sofa_stable`: there are constants `C`, `C'`, `ε₀ > 0` such that a moving sofa of deficit
`ε < ε₀`, once normalized, lies within Euclidean Hausdorff distance `C √ε` of Gerver's sofa, and the
symmetric difference of the two has area at most `C' √ε`. `gerver_sofa_angle_stable`: such a sofa
that turns clockwise by `ω ∈ [arccos (5/11), π/2]` has `π/2 - ω ≤ C ε`. `gerver_sofa_stability_exponent`:
no exponent larger than `1/2` can replace the square root, even if Gerver's sofa may be rotated and
translated in any way.

## Formal-conjectures' definitions (namespace `FormalConjectures.MovingSofa`)

Google DeepMind's formal-conjectures (`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`, Apache-2.0, Copyright 2026 The Formal Conjectures
Authors) states the problem with its own definitions, restated here verbatim inside the namespace
`FormalConjectures`, with an explicit name for the topology instance on `E(2)`, which it leaves
anonymous. Its test lemmas are left out, and so is its `sofaConstant_eq`, the statement of
`sofaConstant_eq_volume_gerversSofa` inside formal-conjectures' `answer` marker.

**The plane** is `ℝ² = EuclideanSpace ℝ (Fin 2)`. **A moving sofa** `s` with motion `m` is connected
and closed, `m` is a continuous path in the affine isometries `E(2)` with `m 0` the identity, `s` lies
in the horizontal side, every `m t '' s` in the hallway, and `m 1 '' s` in the vertical side.
**The sofa constant** is the supremum of the areas of moving sofas. **Gerver's sofa** `gerversSofa`
is the shape of the rotation path `GerversSofa.p`, defined by integrals from Gerver's four constants
`A, B, φ, θ`, the solution of the system `ABφθSpec`; `rotateTranslate α p` translates by `p` and then
rotates by `α`.

**The theorems.** `ABφθSpec.existsUnique`: the system has exactly one solution.
`isMovingSofa_gerversSofa` and `sofaConstant_eq_volume_gerversSofa`: Gerver's sofa is a moving sofa
whose area is the sofa constant (marked solved in formal-conjectures).
`volume_eq_sofaConstant_iff_congruent_gerversSofa`: a moving sofa has area the sofa constant if and
only if an isometry maps Gerver's sofa onto it (marked open in formal-conjectures).

## The bridge (namespace `Bridge`)

The coordinates of `p : ℝ²` are `(p 0, p 1) ∈ ℝ × ℝ`. `isMovingSofa_iff`: a set `s ⊆ ℝ²` is a moving
sofa of formal-conjectures if and only if it lies in the horizontal side and its coordinates form a
moving sofa of Baek's (the motions of formal-conjectures start at the identity, Baek's at a
translation). `sofaConstant_eq`: the sofa constant is the supremum of the areas of Baek's moving
sofas. `gerversSofa_eq`: in coordinates, formal-conjectures' Gerver's sofa, defined from Gerver's
four constants, is Baek's, defined from Romik's parameters.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS 1
open Real Set MeasureTheory

namespace Baek

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

/-- A moving sofa that turns clockwise by the angle `ω`: a motion as in `IsMovingSofa` that ends
with the rotation by `-ω`. -/
def IsMovingSofaWithAngle (S : Set (ℝ × ℝ)) (ω : ℝ) : Prop :=
  IsClosed S ∧ IsConnected S ∧
    ∃ (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ), ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
      θ 0 = 0 ∧ θ 1 = -ω ∧ (∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway) ∧
      (∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide)

/-- The area deficit `|G| - |S|` of a set `S`, where `G` is Gerver's sofa. -/
noncomputable def sofaDeficit (P : GerverParams) (S : Set (ℝ × ℝ)) : ℝ :=
  (volume (gerverSofa P)).toReal - (volume S).toReal

/-- The translate of `S` whose highest point has height `1` and whose leftmost point has the
abscissa of the leftmost point of Gerver's sofa. -/
noncomputable def normalizedSofa (P : GerverParams) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun p => p + (sInf (Prod.fst '' gerverSofa P) - sInf (Prod.fst '' S), 1 - sSup (Prod.snd '' S)))
    '' S

/-- The Euclidean distance between two points of the plane. -/
noncomputable def euclideanDist (p q : ℝ × ℝ) : ℝ := √((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- Every point of each of the sets `S` and `T` lies within Euclidean distance `r` of a point of the
other. For nonempty compact sets, their Euclidean Hausdorff distance is then at most `r`. -/
def EuclideanClose (r : ℝ) (S T : Set (ℝ × ℝ)) : Prop :=
  (∀ p ∈ S, ∃ q ∈ T, euclideanDist p q ≤ r) ∧ (∀ q ∈ T, ∃ p ∈ S, euclideanDist q p ≤ r)

end Baek

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable section

namespace FormalConjectures.MovingSofa

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
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  sorry

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

end FormalConjectures.MovingSofa

end
-- END SHARED DEFINITIONS 2

namespace Baek

/-- Romik's system has a solution in the stated range. -/
theorem gerver_params_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox := by
  sorry

/-- Romik's system has at most one solution in the stated range. -/
theorem gerver_params_unique (P Q : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q := by
  sorry

/-- Gerver's sofa has area `2.219…`: between `2.2192` and `2.2199`. (Gerver's and Romik's value is
`2.21953…`.) -/
theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199 := by
  sorry

/-- **Theorem 1.1.1.** Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. -/
theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  sorry

/-- **Uniqueness** (not in Baek's paper). Every moving sofa with the area of Gerver's sofa is
congruent to Gerver's sofa: a rotation about the origin followed by a translation maps it onto
Gerver's sofa. -/
theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P := by
  sorry

open scoped symmDiff in
/-- **Stability** (not in Baek's paper). There are constants `C`, `C'` and `ε₀ > 0` such that every
moving sofa `S` whose area is less than the area of Gerver's sofa by `ε < ε₀`, once normalized, lies
within Euclidean Hausdorff distance `C √ε` of Gerver's sofa, and the symmetric difference of the two
has area at most `C' √ε`. -/
theorem gerver_sofa_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C C' ε₀ : ℝ, 0 < C ∧ 0 < C' ∧ 0 < ε₀ ∧
      ∀ S, IsMovingSofa S → sofaDeficit P S < ε₀ →
        EuclideanClose (C * √(sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        (volume (normalizedSofa P S ∆ gerverSofa P)).toReal ≤ C' * √(sofaDeficit P S) := by
  sorry

/-- **Stability of the rotation angle** (not in Baek's paper). There are constants `C` and `ε₀ > 0`
such that a moving sofa whose area is less than the area of Gerver's sofa by `ε < ε₀`, and whose
motion turns it clockwise by an angle `ω ∈ [arccos (5/11), π/2]`, has `π/2 - ω ≤ C ε`. -/
theorem gerver_sofa_angle_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ S ω, IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
        sofaDeficit P S < ε₀ → π / 2 - ω ≤ C * sofaDeficit P S := by
  sorry

/-- **The exponent `1/2` is optimal** (not in Baek's paper). For every exponent `a > 1/2`, every
constant `C` and every `ε₀ > 0`, there is a moving sofa `S` whose deficit `ε` satisfies `0 < ε < ε₀`
and which lies within Euclidean Hausdorff distance `C εᵃ` of no image of Gerver's sofa by a rotation
about the origin followed by a translation. -/
theorem gerver_sofa_stability_exponent (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (a C ε₀ : ℝ) (ha : 1 / 2 < a) (hε₀ : 0 < ε₀) :
    ∃ S, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ (θ : ℝ) (v : ℝ × ℝ),
        ¬ EuclideanClose (C * sofaDeficit P S ^ a) S ((fun p => rot θ p + v) '' gerverSofa P) := by
  sorry

end Baek

namespace Bridge

/-- **The two notions of moving sofa agree.** A set `s ⊆ ℝ²` is a moving sofa of formal-conjectures
if and only if it lies in the horizontal side of the hallway and its coordinates form a moving sofa
of Baek's paper. -/
theorem isMovingSofa_iff (s : Set ℝ²) :
    (∃ m, FormalConjectures.MovingSofa.IsMovingSofa s m) ↔
      s ⊆ FormalConjectures.MovingSofa.horizontalHallway ∧
        Baek.IsMovingSofa ((fun p : ℝ² => (p 0, p 1)) '' s) := by
  sorry

/-- **The two optimal areas agree.** The sofa constant of formal-conjectures is the supremum of the
areas of the moving sofas of Baek's paper. -/
theorem sofaConstant_eq :
    FormalConjectures.MovingSofa.sofaConstant =
      ⨆ (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S), volume S := by
  sorry

/-- **The two Gerver's sofas agree.** In coordinates, the Gerver's sofa of formal-conjectures,
defined from Gerver's four constants, is the Gerver's sofa of Baek's paper, defined from Romik's
parameters. -/
theorem gerversSofa_eq (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    (fun p : ℝ² => (p 0, p 1)) '' FormalConjectures.MovingSofa.gerversSofa = Baek.gerverSofa P := by
  sorry

end Bridge

namespace FormalConjectures.MovingSofa

/-- Gerver's concrete sofa admits a valid hallway motion. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m := by
  sorry

/-- Gerver's sofa attains the sofa constant. -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  sorry

/-- Gerver's sofa is the unique sofa that attains the sofa constant, up to a rigid motion. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  sorry

end FormalConjectures.MovingSofa
