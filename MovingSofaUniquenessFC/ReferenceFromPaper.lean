module

public import MovingSofaUniquenessFC.ReferenceSolution

/-!
# From a paper solution to the four-constant reference

The conversion is proved from the phase-matching equations, without using
shape uniqueness or global uniqueness of either parameter system. The
reference contact-error identity then recovers equations one and two.
Nonnegativity of the two coefficients is supplied by the paper's already
proved parameter enclosures only at the final `ofPaper_valid` step.

Uncompiled source.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaUniquenessFC.Reference

/-- The four original constants, read from a paper parameter tuple. -/
def ofPaper (P : GerverParams) : Data where
  A := P.φ - 1 - 2 * P.b₁
  B := 1 / 2 - P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂
  φ := P.φ
  θ := P.θ

/-- First derivative matching yields the two rotating-frame identities. -/
theorem ofPaper_frame {P : GerverParams} (hP : P.IsSolution) :
    2 * P.a₁ * sin P.φ = (ofPaper P).A + (1 - cos P.φ) / 2 ∧
    2 * P.a₁ * cos P.φ = (ofPaper P).B + 1 + sin P.φ / 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ha₂, _, hd12, _⟩ := hP
  rw [(rom_hasDerivAt_x₁ _ _).deriv, (rom_hasDerivAt_x₂ _ _).deriv] at hd12
  have hd := rom_rot_inj hd12
  have hx := congrArg Prod.fst hd
  have hy := congrArg Prod.snd hd
  simp only [ha₂] at hx hy
  constructor <;> simp only [ofPaper] <;> linarith

/-- The fourth reference equation is the second derivative match at theta. -/
theorem ofPaper_eq4 {P : GerverParams} (hP : P.IsSolution) :
    eq4 (ofPaper P).A (ofPaper P).B P.φ P.θ = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hc₂, _, _, _, _, _, _, hd23, _⟩ := hP
  rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hd23
  have hd := rom_rot_inj hd23
  have hx := congrArg Prod.fst hd
  have hy := congrArg Prod.snd hd
  simp only [hc₂] at hx
  unfold eq4 ofPaper
  nlinarith

/-- Cancel a1 using the two frame equations and the unit-circle identity. -/
theorem ofPaper_eq3 {P : GerverParams} (hP : P.IsSolution) :
    eq3 (ofPaper P).A (ofPaper P).B P.φ P.θ = 0 := by
  obtain ⟨hs, hc⟩ := ofPaper_frame hP
  unfold eq3
  linear_combination sin P.φ * hc - cos P.φ * hs +
    (1 / 2 : ℝ) * (sin_sq_add_cos_sq P.φ)

/-- Reconstruction of the paper coefficients does not need the contact equations. -/
theorem ofPaper_coefficients {P : GerverParams} (hP : P.IsSolution) :
    (ofPaper P).a1 = P.a₁ ∧ (ofPaper P).b1 = P.b₁ ∧ (ofPaper P).b2 = P.b₂ ∧
    (ofPaper P).toPaper.c₁ = P.c₁ ∧ (ofPaper P).toPaper.c₂ = P.c₂ := by
  sorry

/-- All phase translations are fixed by continuity once the coefficients agree. -/
theorem ofPaper_toPaper {P : GerverParams} (hP : P.IsSolution) :
    (ofPaper P).toPaper = P := by
  sorry

/-- A paper solution in its certified box gives an actual full-domain reference solution. -/
theorem ofPaper_valid {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (ofPaper P).Valid := by
  sorry

end MovingSofaUniquenessFC.Reference
