module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# The moving sofa problem: Gerver's sofa has maximum area, and is the only such sofa

Statements of record, in Mathlib's vocabulary only, of Jineon Baek, *Optimality of Gerver's Sofa*
(arXiv:2411.19826v1), Theorem 1.1.1, and of the uniqueness of the optimal sofa up to rigid motions,
which that paper does not prove (the argument is in `docs/uniqueness/20-complete-paper-proof.md`).

**The plane** is `ℝ × ℝ`, and the area of a set is its Lebesgue measure `volume`.

**The hallway** `L = H_L ∪ V_L` is the union of its horizontal side `H_L = (-∞, 1] × [0, 1]` and its
vertical side `V_L = [0, 1] × (-∞, 1]`.

**A moving sofa** is a nonempty, connected, closed set `S ⊆ ℝ²` that can be moved inside `L` by a
continuous rigid motion from `H_L` to `V_L`: there are a continuous angle `θ` and a continuous
translation `c` on `[0, 1]` such that, writing `Φ_s(p) = R_{θ(s)} p + c(s)` with `R_θ` the
counterclockwise rotation by `θ`, the map `Φ_0` is a translation (`θ(0) = 0`), `Φ_0(S) ⊆ H_L`,
`Φ_s(S) ⊆ L` for all `s ∈ [0, 1]`, and `Φ_1(S) ⊆ V_L`. (A continuous curve in the group of
orientation-preserving isometries of the plane always has this form, by lifting its rotation part.)

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
solution in this range, so Gerver's sofa is well defined. `gerver_sofa_area`: its area is `2.219…`
(between `2.2192` and `2.2199`), which identifies the shape with the sofa of area `2.21953…` that
Gerver found. `gerver_sofa_optimal`: Gerver's sofa is a moving sofa, and every moving sofa has area at
most the area of Gerver's sofa. `gerver_sofa_unique`: every moving sofa with the area of Gerver's sofa
is congruent to it, as a set: a rotation `R_θ` about the origin followed by a translation by a vector
`v` maps it exactly onto Gerver's sofa. So Gerver's sofa is, up to rigid motions, the only moving sofa
of maximum area.
-/

@[expose] public section

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

/-- **Uniqueness.** Every moving sofa with the area of Gerver's sofa is congruent to Gerver's sofa: a
rotation about the origin followed by a translation maps it onto Gerver's sofa. -/
theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P := by
  sorry

end MovingSofaChallenge
