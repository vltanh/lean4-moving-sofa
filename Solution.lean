module

public import MovingSofa.Main

/-!
# Solution: the main results, proved from the development

This module restates the definitions and theorems of `Challenge.lean` verbatim, in the namespace
`MovingSofaChallenge`, and proves the theorems from the library `MovingSofa`. The bridge lemmas
`isMovingSofa_iff`, `GerverParams.toLib_isSolution`, `GerverParams.toLib_inBox` and
`gerverSofa_eq` translate between the two vocabularies.
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

/-! ### Bridges to the library -/

/-- Moving sofas in the Challenge's vocabulary are moving sofas of the library. -/
theorem isMovingSofa_iff (S : Set (ℝ × ℝ)) : IsMovingSofa S ↔ MovingSofa.IsMovingSofa S := by
  constructor
  · rintro ⟨hc, hconn, θ, c, h1, h2, h3, h4, h5, h6⟩
    exact ⟨-θ 1, hc, hconn, θ, c, ⟨h1, h2, h3, (neg_neg _).symm, h4, h5, h6⟩⟩
  · rintro ⟨w, hc, hconn, θ, c, hm⟩
    exact ⟨hc, hconn, θ, c, hm.continuousOn_angle, hm.continuousOn_shift, hm.angle_zero, hm.start,
      hm.inside, hm.finish⟩

/-- The library's version of a parameter tuple. -/
def GerverParams.toLib (P : GerverParams) : MovingSofa.GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂, P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

/-- The Challenge's version of a library parameter tuple. -/
def GerverParams.ofLib (P : MovingSofa.GerverParams) : GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂, P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

theorem GerverParams.toLib_isSolution (P : GerverParams) : P.toLib.IsSolution ↔ P.IsSolution :=
  Iff.rfl

theorem GerverParams.toLib_inBox (P : GerverParams) : P.toLib.InBox ↔ P.InBox :=
  Iff.rfl

theorem gerverSofa_eq (P : GerverParams) : gerverSofa P = MovingSofa.gerverSofa P.toLib :=
  rfl

/-! ### The theorems -/

/-- Romik's system has a solution in the stated range. -/
theorem gerver_params_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox := by
  obtain ⟨P, hP, hb⟩ := MovingSofa.definition8_1_2_exists
  exact ⟨GerverParams.ofLib P, (GerverParams.toLib_isSolution _).1 hP,
    (GerverParams.toLib_inBox _).1 hb⟩

/-- Romik's system has at most one solution in the stated range. -/
theorem gerver_params_unique (P Q : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q := by
  have h := MovingSofa.definition8_1_2_unique ((GerverParams.toLib_isSolution P).2 hP)
    ((GerverParams.toLib_inBox P).2 hPb) ((GerverParams.toLib_isSolution Q).2 hQ)
    ((GerverParams.toLib_inBox Q).2 hQb)
  cases P; cases Q
  simp only [GerverParams.toLib, MovingSofa.GerverParams.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rfl

/-- Gerver's sofa has area `2.219…`: between `2.2192` and `2.2199`. (Gerver's and Romik's value is
`2.21953…`.) -/
theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199 := by
  have hP' := (GerverParams.toLib_isSolution P).2 hP
  have hb' := (GerverParams.toLib_inBox P).2 hPb
  have h := MovingSofa.gerverSofa_area_mem hP' hb'
  have hfin := MovingSofa.gerverSofa_volume_ne_top hP' hb'
  rw [gerverSofa_eq, ← ENNReal.ofReal_toReal hfin]
  exact ⟨ENNReal.ofReal_le_ofReal h.1, ENNReal.ofReal_le_ofReal h.2⟩

/-- **Theorem 1.1.1.** Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. -/
theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  have h := MovingSofa.theorem1_1_1 ((GerverParams.toLib_isSolution P).2 hP)
    ((GerverParams.toLib_inBox P).2 hPb)
  rw [gerverSofa_eq, isMovingSofa_iff]
  exact ⟨h.1, fun S hS => h.2 S ((isMovingSofa_iff S).1 hS)⟩

end MovingSofaChallenge
