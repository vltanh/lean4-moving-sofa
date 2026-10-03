module

public import ChallengeDefs
public import MovingSofaOptimality.Main
public import MovingSofaUniqueness.Main
public import MovingSofaUniquenessFC.Final

/-!
# Solution: the main results, proved from the development

This module restates the theorems of `Challenge.lean` about Baek's paper verbatim, in the namespace
`MovingSofaChallenge`, with the Challenge's definitions from `ChallengeDefs`, and proves them from the libraries `MovingSofaOptimality` (Baek's paper)
and `MovingSofaUniqueness` (the uniqueness of the optimal sofa). The bridge lemmas
`isMovingSofa_iff`, `GerverParams.toLib_isSolution`, `GerverParams.toLib_inBox` and
`gerverSofa_eq` translate between the two vocabularies.
-/

@[expose] public section

open Real Set MeasureTheory

namespace MovingSofaChallenge

/-! ### Bridges to the library -/

/-- Moving sofas in the Challenge's vocabulary are moving sofas of the library. -/
theorem isMovingSofa_iff (S : Set (ℝ × ℝ)) : IsMovingSofa S ↔ MovingSofaOptimality.IsMovingSofa S := by
  constructor
  · rintro ⟨hc, hconn, θ, c, h1, h2, h3, h4, h5, h6⟩
    exact ⟨-θ 1, hc, hconn, θ, c, ⟨h1, h2, h3, (neg_neg _).symm, h4, h5, h6⟩⟩
  · rintro ⟨w, hc, hconn, θ, c, hm⟩
    exact ⟨hc, hconn, θ, c, hm.continuousOn_angle, hm.continuousOn_shift, hm.angle_zero, hm.start,
      hm.inside, hm.finish⟩

/-- The library's version of a parameter tuple. -/
def GerverParams.toLib (P : GerverParams) : MovingSofaOptimality.GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂, P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

/-- The Challenge's version of a library parameter tuple. -/
def GerverParams.ofLib (P : MovingSofaOptimality.GerverParams) : GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂, P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

theorem GerverParams.toLib_isSolution (P : GerverParams) : P.toLib.IsSolution ↔ P.IsSolution :=
  Iff.rfl

theorem GerverParams.toLib_inBox (P : GerverParams) : P.toLib.InBox ↔ P.InBox :=
  Iff.rfl

theorem gerverSofa_eq (P : GerverParams) : gerverSofa P = MovingSofaOptimality.gerverSofa P.toLib :=
  rfl

/-! ### The theorems -/

/-- Romik's system has a solution in the stated range. -/
theorem gerver_params_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox := by
  obtain ⟨P, hP, hb⟩ := MovingSofaOptimality.definition8_1_2_exists
  exact ⟨GerverParams.ofLib P, (GerverParams.toLib_isSolution _).1 hP,
    (GerverParams.toLib_inBox _).1 hb⟩

/-- Romik's system has at most one solution in the stated range. -/
theorem gerver_params_unique (P Q : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q := by
  have h := MovingSofaOptimality.definition8_1_2_unique ((GerverParams.toLib_isSolution P).2 hP)
    ((GerverParams.toLib_inBox P).2 hPb) ((GerverParams.toLib_isSolution Q).2 hQ)
    ((GerverParams.toLib_inBox Q).2 hQb)
  cases P; cases Q
  simp only [GerverParams.toLib, MovingSofaOptimality.GerverParams.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rfl

/-- Gerver's sofa has area `2.219…`: between `2.2192` and `2.2199`. (Gerver's and Romik's value is
`2.21953…`.) -/
theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199 := by
  have hP' := (GerverParams.toLib_isSolution P).2 hP
  have hb' := (GerverParams.toLib_inBox P).2 hPb
  have h := MovingSofaOptimality.gerverSofa_area_mem hP' hb'
  have hfin := MovingSofaOptimality.gerverSofa_volume_ne_top hP' hb'
  rw [gerverSofa_eq, ← ENNReal.ofReal_toReal hfin]
  exact ⟨ENNReal.ofReal_le_ofReal h.1, ENNReal.ofReal_le_ofReal h.2⟩

/-- **Theorem 1.1.1.** Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. -/
theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  have h := MovingSofaOptimality.theorem1_1_1 ((GerverParams.toLib_isSolution P).2 hP)
    ((GerverParams.toLib_inBox P).2 hPb)
  rw [gerverSofa_eq, isMovingSofa_iff]
  exact ⟨h.1, fun S hS => h.2 S ((isMovingSofa_iff S).1 hS)⟩

/-- **Uniqueness.** Every moving sofa with the area of Gerver's sofa is congruent to Gerver's sofa: a
rotation about the origin followed by a translation maps it onto Gerver's sofa. -/
theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P := by
  obtain ⟨g, hg⟩ := MovingSofaUniqueness.image_eq_gerver_of_volume_eq
    ((GerverParams.toLib_isSolution P).2 hP) ((GerverParams.toLib_inBox P).2 hPb)
    ((isMovingSofa_iff S).1 hS) (by rw [← gerverSofa_eq]; exact harea)
  exact ⟨g.angle, g.shift, by rw [gerverSofa_eq]; exact hg⟩

end MovingSofaChallenge
