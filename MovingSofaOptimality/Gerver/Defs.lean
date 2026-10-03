module

public import MovingSofaOptimality.Convex.Mamikon

/-!
# Gerver's sofa

The paper takes Gerver's sofa `G`, its rotation path `𝐱` and the angles `φ, θ` from Section 4 of
Romik, *Differential equations and exact solutions in the moving sofa problem* (Experimental
Mathematics, 2018), Equations (25)–(44) (Definitions 8.1.2, 8.4.1–8.4.3).

Romik's rotation path is glued from the general solutions (SOL1)–(SOL5) of his ODEs on the five
phases `[0, φ)`, `[φ, θ)`, `[θ, π/2 - θ]`, `(π/2 - θ, π/2 - φ]`, `(π/2 - φ, π/2]`, with 22 real
parameters `φ, θ, a_i, b_i, c_i, d_i, e_i, κ_j` subject to the equations (27)–(44): left-right
symmetry, `𝐀(0) = (1, 0)` and `𝐱(0) = 0`, continuous differentiability at the phase boundaries, and
the two contact conditions. Gerver's sofa is the shape `S_𝐱` of Romik's Equation (8).

Romik solves the system numerically (his Table 1: `φ = 0.0391773…`, `θ = 0.6813015…`) and states,
without proof, that the solution with `0 < φ < θ < π/4` is unique. We state results for every
solution with `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]` (the paper quotes `φ ∈ [0.039, 0.040]`).
-/

@[expose] public section

open Real Set

namespace MovingSofaOptimality

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

/-- Gerver's rotation path `𝐱` (Romik's Equation (25), the paper's Definition 8.4.2). -/
noncomputable def path (t : ℝ) : ℝ × ℝ :=
  if t < P.φ then P.x₁ t
  else if t < P.θ then P.x₂ t
  else if t ≤ π / 2 - P.θ then P.x₃ t
  else if t ≤ π / 2 - P.φ then P.x₄ t
  else P.x₅ t

/-- The contact path `𝐀(t) = 𝐱(t) + ⟨𝐱'(t), u_t⟩ v_t + u_t` of a rotation path (Romik's
Equation (9)). -/
noncomputable def contactA (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  x t + dot (deriv x t) (uvec t) • vvec t + uvec t
/-- The contact path `𝐁(t) = 𝐱(t) + ⟨𝐱'(t), u_t⟩ v_t` (Romik's Equation (10)). -/
noncomputable def contactB (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  x t + dot (deriv x t) (uvec t) • vvec t
/-- The contact path `𝐂(t) = 𝐱(t) - ⟨𝐱'(t), v_t⟩ u_t + v_t` (Romik's Equation (11)). -/
noncomputable def contactC (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  x t - dot (deriv x t) (vvec t) • uvec t + vvec t
/-- The contact path `𝐃(t) = 𝐱(t) - ⟨𝐱'(t), v_t⟩ u_t` (Romik's Equation (12)). -/
noncomputable def contactD (x : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  x t - dot (deriv x t) (vvec t) • uvec t

/-- Romik's system of equations (27)–(44) for the parameters of Gerver's sofa, with
`0 < φ < θ < π/4`. -/
def IsSolution : Prop :=
  0 < P.φ ∧ P.φ < P.θ ∧ P.θ < π / 4 ∧
  -- (27)–(31): left-right symmetry
  P.e₁ = P.a₁ ∧ P.e₂ = -P.a₂ ∧ P.d₁ = π / 4 - P.b₁ ∧
  P.d₂ = P.b₂ + π / 4 * (2 * P.b₁ - π / 4) ∧ P.c₂ = P.c₁ - π / 2 ∧
  -- (32)–(34): `𝐀(0) = (1, 0)` and `𝐱(0) = (0, 0)`
  P.κ₁.1 = 1 - P.a₁ ∧ P.κ₁.2 = 1 / 4 ∧ P.a₂ = -1 / 4 ∧
  -- (35)–(42): continuous differentiability at the phase boundaries
  P.x₁ P.φ = P.x₂ P.φ ∧ deriv P.x₁ P.φ = deriv P.x₂ P.φ ∧
  P.x₂ P.θ = P.x₃ P.θ ∧ deriv P.x₂ P.θ = deriv P.x₃ P.θ ∧
  P.x₃ (π / 2 - P.θ) = P.x₄ (π / 2 - P.θ) ∧ deriv P.x₃ (π / 2 - P.θ) = deriv P.x₄ (π / 2 - P.θ) ∧
  P.x₄ (π / 2 - P.φ) = P.x₅ (π / 2 - P.φ) ∧ deriv P.x₄ (π / 2 - P.φ) = deriv P.x₅ (π / 2 - P.φ) ∧
  -- (43)–(44): the transitions between the contact phases
  P.x₁ P.φ = contactB P.x₄ (π / 2 - P.θ) ∧ P.x₅ (π / 2 - P.φ) = contactD P.x₂ P.θ

/-- The box of parameters considered: `φ ∈ [0.039, 0.04]` and `θ ∈ [0.68, 0.69]`. -/
def InBox : Prop := P.φ ∈ Icc (0.039 : ℝ) 0.04 ∧ P.θ ∈ Icc (0.68 : ℝ) 0.69

end GerverParams

/-- The shape `S_𝐱 = H_L ∩ ⋂_{t ∈ [0, π/2]} (𝐱(t) + R_t(L)) ∩ (𝐱(π/2) + R_{π/2}(V_L))` of a
rotation path (Romik's Equation (8)). -/
def shapeOfPath (x : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  horizSide ∩ (⋂ t ∈ Icc 0 (π / 2), (fun p => x t + rot t p) '' hallway) ∩
    (fun p => x (π / 2) + rot (π / 2) p) '' vertSide

/-- Gerver's sofa `G` (the shape of Gerver's rotation path). -/
def gerverSofa (P : GerverParams) : Set (ℝ × ℝ) := shapeOfPath P.path

end MovingSofaOptimality
