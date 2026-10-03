module

public import MovingSofaBridge.GerverConstants
public import MovingSofaOptimality.Gerver.Frame
public import MovingSofaOptimality.External.Romik

/-!
# Gerver's four constants and Romik's parameters

Baek's paper takes Gerver's sofa from Romik's description: 22 parameters of a five-phase rotation
path, subject to Romik's equations (27)–(44). Formal-conjectures takes it from Gerver's four
constants `A`, `B`, `φ`, `θ`. `ofRomik` reads the four constants off Romik's parameters, and
`toRomik` rebuilds Romik's parameters from them. A solution of Romik's system in the box
`φ ∈ [0.039, 0.04]`, `θ ∈ [0.68, 0.69]` gives a solution of Gerver's system (`ofRomik_valid`), with
`toRomik (ofRomik P) = P` (`ofRomik_toRomik`). With `spec_unique`, Gerver's system has exactly one
solution (`spec_existsUnique`), and Romik's parameters built from it solve Romik's system in the
box (`romik_solution`).
-/

@[expose] public section
noncomputable section

open Set Real MovingSofaOptimality MovingSofaOptimality.GerverParams

namespace MovingSofaBridge.GerverConstants

/-!
## From Gerver's constants to Romik's parameters
-/

section

variable (D : GerverConstants)

def a1 : ℝ := ((D.A + 1 / 2) * sin D.φ + (D.B + 1) * cos D.φ) / 2

def b1 : ℝ := (D.φ - 1 - D.A) / 2

def b2 : ℝ := D.B - 1 / 2 - D.b1 * D.φ + D.φ ^ 2 / 4

def k1 : ℝ × ℝ := (1 - D.a1, 1 / 4)

def k2 : ℝ × ℝ := D.k1 + rot D.φ (-D.B / 2, 1 / 4)

def k3 : ℝ × ℝ := D.k2 + rot D.θ (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2)

def toRomik : GerverParams where
  φ := D.φ
  θ := D.θ
  a₁ := D.a1
  a₂ := -1 / 4
  b₁ := D.b1
  b₂ := D.b2
  c₁ := π / 2 + D.A - D.φ - 1
  c₂ := D.A - D.φ - 1
  d₁ := π / 4 - D.b1
  d₂ := D.b2 + π / 4 * (2 * D.b1 - π / 4)
  e₁ := D.a1
  e₂ := 1 / 4
  κ₁ := D.k1
  κ₂ := D.k2
  κ₃ := D.k3
  κ₄ := (2 * D.k3.1 - D.k2.1, D.k2.2)
  κ₅ := (2 * D.k3.1 - 1 + D.a1, 1 / 4)

variable {D}

/-- The second phase at `φ`. -/
theorem x2_phi (D : GerverConstants) :
    D.toRomik.x₂ D.φ = rot D.φ (D.B - 1 / 2, (D.A - 1) / 2) + D.k2 := by
  unfold GerverParams.x₂
  congr 2
  simp only [toRomik, b1, b2]
  ext <;> ring

/-- Gerver's second equation fixes the horizontal position of the third phase. -/
theorem k3_fst (h : D.Valid) : D.k3.1 = 1 - 4 * D.a1 / 3 := by
  have h2 := (spec_iff.mp h).2.2.2.2.2.2.1
  change eq2 D.A D.B D.φ D.θ = 0 at h2
  unfold eq2 at h2
  simp only [k3, k2, k1, rot, Prod.fst_add]
  unfold a1
  linear_combination h2 / 6

end

/-!
## The symmetry of the path

The last two phases of the path are the reflections of the first two about a vertical line
(`reflect`). The difference between the two sides of Romik's first contact condition is
`(-eq2/2, -eq1/2)` (`contact_error`).
-/

section

/-- The reflection about the vertical line through the middle of the path. -/
def reflect (D : GerverConstants) (q : ℝ × ℝ) : ℝ × ℝ := (2 * D.k3.1 - q.1, q.2)

theorem x5_reflection (D : GerverConstants) (t : ℝ) :
    D.toRomik.x₅ (π / 2 - t) = D.reflect (D.toRomik.x₁ t) := by
  ext <;> simp only [toRomik, GerverParams.x₅, GerverParams.x₁, reflect, k1,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

theorem x4_reflection (D : GerverConstants) (t : ℝ) :
    D.toRomik.x₄ (π / 2 - t) = D.reflect (D.toRomik.x₂ t) := by
  ext <;> simp only [toRomik, GerverParams.x₄, GerverParams.x₂, reflect,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

theorem x3_reflection (D : GerverConstants) (t : ℝ) :
    D.toRomik.x₃ (π / 2 - t) = D.reflect (D.toRomik.x₃ t) := by
  ext <;> simp only [toRomik, GerverParams.x₃, reflect,
    rot, sin_pi_div_two_sub, cos_pi_div_two_sub, Prod.fst_add, Prod.snd_add] <;> ring

/-- The inner contact point of the fourth phase. -/
theorem contactB_four (D : GerverConstants) (t : ℝ) :
    contactB D.toRomik.x₄ (π / 2 - t) =
      rot (π / 2 - t) ((D.A + t - D.φ - 1) / 2, -1 / 2) +
        (2 * D.k3.1 - D.k2.1, D.k2.2) := by
  rw [contactB, (rom_hasDerivAt_x₄ _ _).deriv, rom_dot_rot_uvec]
  ext <;> simp only [toRomik, GerverParams.x₄, b1, rot, vvec,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The difference between the two sides of the first contact condition. -/
theorem contact_error (D : GerverConstants) :
    D.toRomik.x₂ D.φ - contactB D.toRomik.x₄ (π / 2 - D.θ) =
      (-eq2 D.A D.B D.φ D.θ / 2, -eq1 D.A D.B D.φ D.θ / 2) := by
  rw [x2_phi, contactB_four]
  ext <;> simp only [k3, rot, sin_pi_div_two_sub, cos_pi_div_two_sub,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, eq1, eq2] <;> ring

end

/-!
## From Romik's parameters to Gerver's constants

The matching conditions of Romik's system give equations three and four of Gerver's system, and
the contact condition gives equations one and two; the bounds on Romik's parameters in the box give
`A, B ≥ 0` (`ofRomik_valid`).
-/

/-- Gerver's four constants, read off Romik's parameters. -/
def ofRomik (P : GerverParams) : GerverConstants where
  A := P.φ - 1 - 2 * P.b₁
  B := 1 / 2 - P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂
  φ := P.φ
  θ := P.θ

/-- The derivative matching at `φ`, in the rotating frame. -/
theorem ofRomik_frame {P : GerverParams} (hP : P.IsSolution) :
    2 * P.a₁ * sin P.φ = (ofRomik P).A + (1 - cos P.φ) / 2 ∧
    2 * P.a₁ * cos P.φ = (ofRomik P).B + 1 + sin P.φ / 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ha₂, _, hd12, _⟩ := hP
  rw [(rom_hasDerivAt_x₁ _ _).deriv, (rom_hasDerivAt_x₂ _ _).deriv] at hd12
  have hd := rom_rot_inj hd12
  have hx := congrArg Prod.fst hd
  have hy := congrArg Prod.snd hd
  simp only [ha₂] at hx hy
  constructor <;> simp only [ofRomik] <;> linarith

/-- The derivative matching at `θ` is Gerver's fourth equation. -/
theorem ofRomik_eq4 {P : GerverParams} (hP : P.IsSolution) :
    eq4 (ofRomik P).A (ofRomik P).B P.φ P.θ = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hc₂, _, _, _, _, _, _, hd23, _⟩ := hP
  rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hd23
  have hd := rom_rot_inj hd23
  have hx := congrArg Prod.fst hd
  have hy := congrArg Prod.snd hd
  simp only [hc₂] at hx
  unfold eq4 ofRomik
  nlinarith

/-- The derivative matching at `φ` gives Gerver's third equation. -/
theorem ofRomik_eq3 {P : GerverParams} (hP : P.IsSolution) :
    eq3 (ofRomik P).A (ofRomik P).B P.φ P.θ = 0 := by
  obtain ⟨hs, hc⟩ := ofRomik_frame hP
  unfold eq3
  linear_combination sin P.φ * hc - cos P.φ * hs +
    (1 / 2 : ℝ) * (sin_sq_add_cos_sq P.φ)

/-- `toRomik` recovers the coefficients of the first three phases. -/
theorem ofRomik_coefficients {P : GerverParams} (hP : P.IsSolution) :
    (ofRomik P).a1 = P.a₁ ∧ (ofRomik P).b1 = P.b₁ ∧ (ofRomik P).b2 = P.b₂ ∧
    (ofRomik P).toRomik.c₁ = P.c₁ ∧ (ofRomik P).toRomik.c₂ = P.c₂ := by
  obtain ⟨hs, hc⟩ := ofRomik_frame hP
  have ha : (ofRomik P).a1 = P.a₁ := by
    show (((ofRomik P).A + 1 / 2) * sin P.φ + ((ofRomik P).B + 1) * cos P.φ) / 2 = P.a₁
    linear_combination P.a₁ * (sin_sq_add_cos_sq P.φ) -
      (sin P.φ / 2) * hs - (cos P.φ / 2) * hc
  have hb : (ofRomik P).b1 = P.b₁ := by simp only [b1, ofRomik]; ring
  have hb' : (ofRomik P).b2 = P.b₂ := by
    show (ofRomik P).B - 1 / 2 - (ofRomik P).b1 * P.φ + P.φ ^ 2 / 4 = P.b₂
    rw [hb]
    simp only [ofRomik]
    ring
  obtain ⟨_, _, _, _, _, _, _, hc₂, _, _, _, _, _, _, hd23, _⟩ := hP
  rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hd23
  have hx := congrArg Prod.fst (rom_rot_inj hd23)
  refine ⟨ha, hb, hb', ?_, ?_⟩
  · simp only [toRomik, ofRomik]
    linarith
  · simp only [toRomik, ofRomik]
    linarith

/-- `toRomik` recovers Romik's parameters: the translations of the phases are determined by
continuity. -/
theorem ofRomik_toRomik {P : GerverParams} (hP : P.IsSolution) :
    (ofRomik P).toRomik = P := by
  let D := ofRomik P
  have hcoef := ofRomik_coefficients hP
  obtain ⟨hs, hc⟩ := ofRomik_frame hP
  obtain ⟨_, _, _, he₁, he₂, hd₁, hd₂, hc₂, hk₁x, hk₁y, ha₂,
    h12, hd12, h23, hd23, h34, hd34, h45, hd45, hc1, hc2⟩ := hP
  have ha : D.a1 = P.a₁ := hcoef.1
  have hb : D.b1 = P.b₁ := hcoef.2.1
  have hb' : D.b2 = P.b₂ := hcoef.2.2.1
  have hc' : D.toRomik.c₁ = P.c₁ := hcoef.2.2.2.1
  have hc'' : D.toRomik.c₂ = P.c₂ := hcoef.2.2.2.2
  have hd' : D.toRomik.d₁ = P.d₁ := by
    simpa only [toRomik, hb] using hd₁.symm
  have hd'' : D.toRomik.d₂ = P.d₂ := by
    simpa only [toRomik, hb, hb'] using hd₂.symm
  have he' : D.toRomik.e₁ = P.e₁ := by
    simpa only [toRomik, ha] using he₁.symm
  have he'' : D.toRomik.e₂ = P.e₂ := by
    simp only [toRomik, he₂, ha₂]
    norm_num
  have hk1 : D.k1 = P.κ₁ := by
    ext <;> simp only [k1, ha] <;> linarith
  have hw1 : (P.a₁ * cos P.φ + P.a₂ * sin P.φ - 1,
      -P.a₂ * cos P.φ + P.a₁ * sin P.φ - 1 / 2) =
      (D.B - 1 / 2, (D.A - 1) / 2) + (-D.B / 2, 1 / 4) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, ha₂] <;> linarith
  have hw2 : (-P.φ ^ 2 / 4 + P.b₁ * P.φ + P.b₂,
      P.φ / 2 - P.b₁ - 1) = (D.B - 1 / 2, (D.A - 1) / 2) := by
    ext <;> simp only [D, ofRomik] <;> ring
  have hk2 : D.k2 = P.κ₂ := by
    have hmatch := h12
    unfold GerverParams.x₁ GerverParams.x₂ at hmatch
    rw [hw1, hw2, rot_add_vec, add_assoc] at hmatch
    show D.k1 + rot P.φ (-D.B / 2, 1 / 4) = P.κ₂
    rw [hk1, add_comm P.κ₁]
    exact add_left_cancel hmatch
  have hX1 : D.toRomik.x₁ = P.x₁ := by
    funext t
    simp only [GerverParams.x₁, toRomik, ha, hk1, ha₂]
  have hX2 : D.toRomik.x₂ = P.x₂ := by
    funext t
    simp only [GerverParams.x₂, toRomik, hb, hb', hk2]
  have hw3 : (-P.θ ^ 2 / 4 + P.b₁ * P.θ + P.b₂,
      P.θ / 2 - P.b₁ - 1) = (P.c₁ - P.θ, P.c₂ + P.θ) +
        (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2) := by
    have hdc := hd23
    rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv] at hdc
    have hx := congrArg Prod.fst (rom_rot_inj hdc)
    have hy := congrArg Prod.snd (rom_rot_inj hdc)
    ext <;> simp only [Prod.fst_add, Prod.snd_add, D, ofRomik] <;> linarith
  have hk3 : D.k3 = P.κ₃ := by
    have hmatch := h23
    unfold GerverParams.x₂ GerverParams.x₃ at hmatch
    rw [hw3, rot_add_vec, add_assoc] at hmatch
    show D.k2 + rot P.θ (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2) = P.κ₃
    rw [hk2, add_comm P.κ₂]
    exact add_left_cancel hmatch
  have hX3 : D.toRomik.x₃ = P.x₃ := by
    funext t
    change rot t (D.toRomik.c₁ - t, D.toRomik.c₂ + t) + D.k3 = _
    rw [hc', hc'', hk3]
    rfl
  have hD23 : D.toRomik.x₂ D.θ = D.toRomik.x₃ D.θ := by
    rw [hX2, hX3]
    exact h23
  have hD12 : D.toRomik.x₁ D.φ = D.toRomik.x₂ D.φ := by
    rw [hX1, hX2]
    exact h12
  have hD34 : D.toRomik.x₃ (π / 2 - D.θ) = D.toRomik.x₄ (π / 2 - D.θ) := by
    rw [x3_reflection, x4_reflection, hD23]
  have hk4 : D.toRomik.κ₄ = P.κ₄ := by
    have hh : D.toRomik.x₄ (π / 2 - D.θ) = P.x₄ (π / 2 - P.θ) := by
      rw [← hD34, hX3]
      exact h34
    unfold GerverParams.x₄ at hh
    rw [hd', hd''] at hh
    exact add_left_cancel hh
  have hX4 : D.toRomik.x₄ = P.x₄ := by
    funext t
    unfold GerverParams.x₄
    rw [hd', hd'', hk4]
  have hD45 : D.toRomik.x₄ (π / 2 - D.φ) = D.toRomik.x₅ (π / 2 - D.φ) := by
    rw [x4_reflection, x5_reflection, hD12]
  have hk5 : D.toRomik.κ₅ = P.κ₅ := by
    have hh : D.toRomik.x₅ (π / 2 - D.φ) = P.x₅ (π / 2 - P.φ) := by
      rw [← hD45, hX4]
      exact h45
    unfold GerverParams.x₅ at hh
    rw [he', he''] at hh
    exact add_left_cancel hh
  have hfields :
      D.toRomik.φ = P.φ ∧ D.toRomik.θ = P.θ ∧ D.toRomik.a₁ = P.a₁ ∧
      D.toRomik.a₂ = P.a₂ ∧ D.toRomik.b₁ = P.b₁ ∧ D.toRomik.b₂ = P.b₂ ∧
      D.toRomik.c₁ = P.c₁ ∧ D.toRomik.c₂ = P.c₂ ∧ D.toRomik.d₁ = P.d₁ ∧
      D.toRomik.d₂ = P.d₂ ∧ D.toRomik.e₁ = P.e₁ ∧ D.toRomik.e₂ = P.e₂ ∧
      D.toRomik.κ₁ = P.κ₁ ∧ D.toRomik.κ₂ = P.κ₂ ∧ D.toRomik.κ₃ = P.κ₃ ∧
      D.toRomik.κ₄ = P.κ₄ ∧ D.toRomik.κ₅ = P.κ₅ :=
    ⟨rfl, rfl, ha, ha₂.symm, hb, hb', hc', hc'', hd', hd'', he', he'', hk1, hk2, hk3, hk4, hk5⟩
  change D.toRomik = P
  generalize hQ : D.toRomik = Q at hfields ⊢
  cases P
  cases Q
  simpa only [GerverParams.mk.injEq] using hfields

/-- A solution of Romik's system in the box gives a solution of Gerver's system. -/
theorem ofRomik_valid {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (ofRomik P).Valid := by
  let D := ofRomik P
  have hback : D.toRomik = P := ofRomik_toRomik hP
  have herror := contact_error D
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
  exact spec_iff.mpr ⟨hφ0.le, hφθ.le, hθ4.le, hA, hB, h1, h2, ofRomik_eq3 hP, ofRomik_eq4 hP⟩

/-!
## Gerver's system has exactly one solution
-/

/-- Gerver's system has a solution. -/
theorem spec_exists : ∃ A B φ θ : ℝ, Spec A B φ θ := by
  obtain ⟨P, hP, hbox⟩ := romik_exists
  exact ⟨(ofRomik P).A, (ofRomik P).B, P.φ, P.θ, ofRomik_valid hP hbox⟩

/-- Gerver's system has exactly one solution, in the form that formal-conjectures states. -/
theorem spec_existsUnique : ∃! q : ℝ × ℝ × ℝ × ℝ,
    Spec q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨A, B, φ, θ, h⟩ := spec_exists
  refine ⟨(A, B, φ, θ), h, ?_⟩
  rintro ⟨A', B', φ', θ'⟩ h'
  obtain ⟨ha, hb, hp, ht⟩ := spec_unique h' h
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hp, ht⟩

/-- Every solution of Gerver's system is read off every solution of Romik's system in the box. -/
theorem eq_ofRomik {D : GerverConstants} (hD : D.Valid) {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) : D = ofRomik P := by
  obtain ⟨ha, hb, hp, ht⟩ := spec_unique hD (ofRomik_valid hP hbox)
  cases D
  simp_all only [ofRomik]

/-- Romik's parameters built from a solution of Gerver's system solve Romik's system in the box. -/
theorem romik_solution {D : GerverConstants} (hD : D.Valid) :
    D.toRomik.IsSolution ∧ D.toRomik.InBox := by
  obtain ⟨P, hP, hbox⟩ := romik_exists
  rw [eq_ofRomik hD hP hbox, ofRomik_toRomik hP]
  exact ⟨hP, hbox⟩

end MovingSofaBridge.GerverConstants
