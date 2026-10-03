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
  obtain ⟨hs, hc⟩ := ofPaper_frame hP
  have ha : (ofPaper P).a1 = P.a₁ := by
    show (((ofPaper P).A + 1 / 2) * sin P.φ + ((ofPaper P).B + 1) * cos P.φ) / 2 = P.a₁
    linear_combination P.a₁ * (sin_sq_add_cos_sq P.φ) -
      (sin P.φ / 2) * hs - (cos P.φ / 2) * hc
  have hb : (ofPaper P).b1 = P.b₁ := by simp only [Data.b1, ofPaper]; ring
  have hb' : (ofPaper P).b2 = P.b₂ := by
    show (ofPaper P).B - 1 / 2 - (ofPaper P).b1 * P.φ + P.φ ^ 2 / 4 = P.b₂
    rw [hb]
    simp only [ofPaper]
    ring
  obtain ⟨_, _, _, _, _, _, _, hc₂, _, _, _, _, _, _, hd23, _⟩ := hP
  rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hd23
  have hx := congrArg Prod.fst (rom_rot_inj hd23)
  refine ⟨ha, hb, hb', ?_, ?_⟩
  · simp only [Data.toPaper, ofPaper]
    linarith
  · simp only [Data.toPaper, ofPaper]
    linarith

/-- All phase translations are fixed by continuity once the coefficients agree. -/
theorem ofPaper_toPaper {P : GerverParams} (hP : P.IsSolution) :
    (ofPaper P).toPaper = P := by
  let D := ofPaper P
  have hcoef := ofPaper_coefficients hP
  obtain ⟨hs, hc⟩ := ofPaper_frame hP
  obtain ⟨_, _, _, he₁, he₂, hd₁, hd₂, hc₂, hk₁x, hk₁y, ha₂,
    h12, hd12, h23, hd23, h34, hd34, h45, hd45, hc1, hc2⟩ := hP
  have ha : D.a1 = P.a₁ := hcoef.1
  have hb : D.b1 = P.b₁ := hcoef.2.1
  have hb' : D.b2 = P.b₂ := hcoef.2.2.1
  have hc' : D.toPaper.c₁ = P.c₁ := hcoef.2.2.2.1
  have hc'' : D.toPaper.c₂ = P.c₂ := hcoef.2.2.2.2
  have hd' : D.toPaper.d₁ = P.d₁ := by
    simpa only [Data.toPaper, hb] using hd₁.symm
  have hd'' : D.toPaper.d₂ = P.d₂ := by
    simpa only [Data.toPaper, hb, hb'] using hd₂.symm
  have he' : D.toPaper.e₁ = P.e₁ := by
    simpa only [Data.toPaper, ha] using he₁.symm
  have he'' : D.toPaper.e₂ = P.e₂ := by
    simp only [Data.toPaper, he₂, ha₂]
    norm_num
  have hk1 : D.k1 = P.κ₁ := by
    ext <;> simp only [Data.k1, ha] <;> linarith
  have hw1 : (P.a₁ * cos P.φ + P.a₂ * sin P.φ - 1,
      -P.a₂ * cos P.φ + P.a₁ * sin P.φ - 1 / 2) =
      (D.B - 1 / 2, (D.A - 1) / 2) + (-D.B / 2, 1 / 4) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, ha₂] <;> linarith
  have hw2 : (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂,
      P.φ / 2 - P.b₁ - 1) = (D.B - 1 / 2, (D.A - 1) / 2) := by
    ext <;> simp only [D, ofPaper] <;> ring
  have hk2 : D.k2 = P.κ₂ := by
    have hmatch := h12
    unfold GerverParams.x₁ GerverParams.x₂ at hmatch
    rw [hw1, hw2, rot_add_vec, add_assoc] at hmatch
    show D.k1 + rot P.φ (-D.B / 2, 1 / 4) = P.κ₂
    rw [hk1, add_comm P.κ₁]
    exact add_left_cancel hmatch
  have hX1 : D.toPaper.x₁ = P.x₁ := by
    funext t
    simp only [GerverParams.x₁, Data.toPaper, ha, hk1, ha₂]
  have hX2 : D.toPaper.x₂ = P.x₂ := by
    funext t
    simp only [GerverParams.x₂, Data.toPaper, hb, hb', hk2]
  have hw3 : (-P.θ ^ 2 / 4 + P.b₁ * P.θ + P.b₂,
      P.θ / 2 - P.b₁ - 1) = (P.c₁ - P.θ, P.c₂ + P.θ) +
        (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2) := by
    have hdc := hd23
    rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hdc
    have hx := congrArg Prod.fst (rom_rot_inj hdc)
    have hy := congrArg Prod.snd (rom_rot_inj hdc)
    ext <;> simp only [Prod.fst_add, Prod.snd_add, D, ofPaper] <;> linarith
  have hk3 : D.k3 = P.κ₃ := by
    have hmatch := h23
    unfold GerverParams.x₂ GerverParams.x₃ at hmatch
    rw [hw3, rot_add_vec, add_assoc] at hmatch
    show D.k2 + rot P.θ (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2) = P.κ₃
    rw [hk2, add_comm P.κ₂]
    exact add_left_cancel hmatch
  have hX3 : D.toPaper.x₃ = P.x₃ := by
    funext t
    change rot t (D.toPaper.c₁ - t, D.toPaper.c₂ + t) + D.k3 = _
    rw [hc', hc'', hk3]
    rfl
  have hD23 : D.toPaper.x₂ D.θ = D.toPaper.x₃ D.θ := by
    rw [hX2, hX3]
    exact h23
  have hD12 : D.toPaper.x₁ D.φ = D.toPaper.x₂ D.φ := by
    rw [hX1, hX2]
    exact h12
  have hD34 : D.toPaper.x₃ (π / 2 - D.θ) = D.toPaper.x₄ (π / 2 - D.θ) := by
    rw [Data.x3_reflection, Data.x4_reflection, hD23]
  have hk4 : D.toPaper.κ₄ = P.κ₄ := by
    have hh : D.toPaper.x₄ (π / 2 - D.θ) = P.x₄ (π / 2 - P.θ) := by
      rw [← hD34, hX3]
      exact h34
    unfold GerverParams.x₄ at hh
    rw [hd', hd''] at hh
    exact add_left_cancel hh
  have hX4 : D.toPaper.x₄ = P.x₄ := by
    funext t
    unfold GerverParams.x₄
    rw [hd', hd'', hk4]
  have hD45 : D.toPaper.x₄ (π / 2 - D.φ) = D.toPaper.x₅ (π / 2 - D.φ) := by
    rw [Data.x4_reflection, Data.x5_reflection, hD12]
  have hk5 : D.toPaper.κ₅ = P.κ₅ := by
    have hh : D.toPaper.x₅ (π / 2 - D.φ) = P.x₅ (π / 2 - P.φ) := by
      rw [← hD45, hX4]
      exact h45
    unfold GerverParams.x₅ at hh
    rw [he', he''] at hh
    exact add_left_cancel hh
  have hfields :
      D.toPaper.φ = P.φ ∧ D.toPaper.θ = P.θ ∧ D.toPaper.a₁ = P.a₁ ∧
      D.toPaper.a₂ = P.a₂ ∧ D.toPaper.b₁ = P.b₁ ∧ D.toPaper.b₂ = P.b₂ ∧
      D.toPaper.c₁ = P.c₁ ∧ D.toPaper.c₂ = P.c₂ ∧ D.toPaper.d₁ = P.d₁ ∧
      D.toPaper.d₂ = P.d₂ ∧ D.toPaper.e₁ = P.e₁ ∧ D.toPaper.e₂ = P.e₂ ∧
      D.toPaper.κ₁ = P.κ₁ ∧ D.toPaper.κ₂ = P.κ₂ ∧ D.toPaper.κ₃ = P.κ₃ ∧
      D.toPaper.κ₄ = P.κ₄ ∧ D.toPaper.κ₅ = P.κ₅ :=
    ⟨rfl, rfl, ha, ha₂.symm, hb, hb', hc', hc'', hd', hd'', he', he'', hk1, hk2, hk3, hk4, hk5⟩
  change D.toPaper = P
  generalize hQ : D.toPaper = Q at hfields ⊢
  cases P
  cases Q
  simpa only [GerverParams.mk.injEq] using hfields

/-- A paper solution in its certified box gives an actual full-domain reference solution. -/
theorem ofPaper_valid {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (ofPaper P).Valid := by
  let D := ofPaper P
  have hback : D.toPaper = P := ofPaper_toPaper hP
  have herror := Data.contact_error D
  rw [hback] at herror
  obtain ⟨hφ0, hφθ, hθ4, _, _, _, _, _, _, _, _, h12, _, _, _, _, _, _, _, hcontact, _⟩ :=
    id hP
  have hc : P.x₂ D.φ = contactB P.x₄ (π / 2 - D.θ) := h12.symm.trans hcontact
  rw [hc, sub_self, eq_comm, Prod.mk_eq_zero] at herror
  obtain ⟨he2, he1⟩ := herror
  have h1 : eq1 D.A D.B D.φ D.θ = 0 := by linarith
  have h2 : eq2 D.A D.B D.φ D.θ = 0 := by linarith
  have hb1 := rom_b1_mem hP hbox
  have hb2 := rom_b2_mem hP hbox
  have hφhi : P.φ ≤ (0.04 : ℝ) := hbox.1.2
  have hA : 0 ≤ D.A := by
    show 0 ≤ P.φ - 1 - 2 * P.b₁
    linarith [hb1.2]
  have hB : 0 ≤ D.B := by
    show 0 ≤ 1 / 2 - P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂
    have hb1' : (-53 / 100 : ℝ) ≤ P.b₁ := by linarith [hb1.1]
    have hprod : (-53 / 100 : ℝ) * P.φ ≤ P.b₁ * P.φ :=
      mul_le_mul_of_nonneg_right hb1' hφ0.le
    have hsq : P.φ ^ 2 ≤ 1 / 100 := by nlinarith
    linarith [hb2.1]
  exact spec_iff.mpr ⟨hφ0.le, hφθ.le, hθ4.le, hA, hB, h1, h2, ofPaper_eq3 hP, ofPaper_eq4 hP⟩

end MovingSofaUniquenessFC.Reference
