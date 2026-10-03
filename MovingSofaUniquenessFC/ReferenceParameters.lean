module

public import SofaUniqueness.ReferenceModel
public import SofaUniqueness.ReferenceBoundary
public import MovingSofa.External.Romik

/-!
# Explicit conversion of Gerver's four constants to the paper parameters

This is algebraic correspondence, not an appeal to uniqueness of optimal sofas.
`toPaper` constructs all 22 real coordinates of the five-phase presentation.
The first derivative matching condition is exactly the third reference equation;
the second is exactly its fourth equation. The two contact equations are handled
in `ReferenceSolution`.

No global root-localization or chosen-reference theorem is assumed. All proofs
are uncompiled source and use ordinary algebraic proof terms.
-/

@[expose] public section
noncomputable section

open Set Real MovingSofa MovingSofa.GerverParams

namespace SofaUniqueness.Reference.Data

variable (D : Data)

def a1 : ℝ := ((D.A + 1 / 2) * sin D.φ + (D.B + 1) * cos D.φ) / 2

def b1 : ℝ := (D.φ - 1 - D.A) / 2

def b2 : ℝ := D.B - 1 / 2 - D.b1 * D.φ + D.φ ^ 2 / 4

def k1 : ℝ × ℝ := (1 - D.a1, 1 / 4)

def k2 : ℝ × ℝ := D.k1 + rot D.φ (-D.B / 2, 1 / 4)

def k3 : ℝ × ℝ := D.k2 + rot D.θ (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2)

def toPaper : GerverParams where
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

/-- Read back the two original scalar coefficients exactly. -/
theorem coefficients_roundtrip :
    D.toPaper.φ - 1 - 2 * D.toPaper.b₁ = D.A ∧
    (1 / 2 - D.toPaper.φ ^ 2 / 4 + D.toPaper.b₁ * D.toPaper.φ + D.toPaper.b₂) = D.B := by
  simp only [toPaper, b1, b2]
  constructor <;> ring

/-- The two small-angle bounds are unchanged by the coordinate conversion. -/
theorem inBox_iff : D.toPaper.InBox ↔
    D.φ ∈ Icc (0.039 : ℝ) 0.04 ∧ D.θ ∈ Icc (0.68 : ℝ) 0.69 := Iff.rfl

variable {D}

/-- Equation three gives both rotating-frame derivative matching identities. -/
theorem a1_frame (h : D.Valid) :
    2 * D.a1 * sin D.φ = D.A + (1 - cos D.φ) / 2 ∧
    2 * D.a1 * cos D.φ = D.B + 1 + sin D.φ / 2 := by
  have h3 := (spec_iff.mp h).2.2.2.2.2.2.2.1
  change eq3 D.A D.B D.φ D.θ = 0 at h3
  unfold eq3 at h3
  constructor
  · unfold a1
    linear_combination (D.A + 1 / 2) * (sin_sq_add_cos_sq D.φ) - cos D.φ * h3
  · unfold a1
    linear_combination (D.B + 1) * (sin_sq_add_cos_sq D.φ) + sin D.φ * h3

/-- Equation four is exactly the radius relation at theta. -/
theorem theta_radius (h : D.Valid) :
    D.B - (D.θ - D.φ) * (1 + D.A) / 2 - (D.θ - D.φ) ^ 2 / 4 =
      D.A + π / 2 - D.φ - D.θ := by
  have h4 := (spec_iff.mp h).2.2.2.2.2.2.2.2
  change eq4 D.A D.B D.φ D.θ = 0 at h4
  unfold eq4 at h4
  linarith

/-- The second phase at the first breakpoint, without using any equation. -/
theorem x2_phi (D : Data) :
    D.toPaper.x₂ D.φ = rot D.φ (D.B - 1 / 2, (D.A - 1) / 2) + D.k2 := by
  unfold GerverParams.x₂
  congr 2 <;> simp only [toPaper, b1, b2] <;> ring

/-- Continuity at phi follows from equation three and the definition of k2. -/
theorem continuity_phi (h : D.Valid) : D.toPaper.x₁ D.φ = D.toPaper.x₂ D.φ := by
  obtain ⟨hs, hc⟩ := a1_frame h
  have hw : (D.a1 * cos D.φ + (-1 / 4 : ℝ) * sin D.φ - 1,
      -(-1 / 4 : ℝ) * cos D.φ + D.a1 * sin D.φ - 1 / 2) =
      (D.B - 1 / 2, (D.A - 1) / 2) + (-D.B / 2, 1 / 4) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith
  rw [x2_phi]
  change rot D.φ _ + D.k1 = _
  rw [hw, rot_add_vec]
  unfold k2
  abel

/-- Derivative matching at phi, in the exact derivative convention of IsSolution. -/
theorem derivative_phi (h : D.Valid) :
    deriv D.toPaper.x₁ D.φ = deriv D.toPaper.x₂ D.φ := by
  obtain ⟨hs, hc⟩ := a1_frame h
  rw [(rom_hasDerivAt_x₁ _ _).deriv, (rom_hasDerivAt_x₂ _ _).deriv]
  congr 1
  ext <;> simp only [toPaper, b1, b2] <;> nlinarith

/-- Continuity at theta follows from equation four and the definition of k3. -/
theorem continuity_theta (h : D.Valid) : D.toPaper.x₂ D.θ = D.toPaper.x₃ D.θ := by
  have hr := theta_radius h
  have hw : (-D.θ ^ 2 / 4 + D.b1 * D.θ + D.b2, D.θ / 2 - D.b1 - 1) =
      (π / 2 + D.A - D.φ - 1 - D.θ, D.A - D.φ - 1 + D.θ) +
        (1 / 2, (1 - D.A - (D.θ - D.φ)) / 2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, b1, b2] <;> nlinarith
  change rot D.θ _ + D.k2 = rot D.θ _ + D.k3
  rw [hw, rot_add_vec]
  unfold k3
  abel

/-- The derivative matching condition at theta is the same scalar equation. -/
theorem derivative_theta (h : D.Valid) :
    deriv D.toPaper.x₂ D.θ = deriv D.toPaper.x₃ D.θ := by
  have hr := theta_radius h
  rw [(rom_hasDerivAt_x₂ _ _).deriv, (rom_hasDerivAt_x₃ _ _).deriv]
  congr 1
  ext <;> simp only [toPaper, b1, b2] <;> nlinarith

/-- An important normalization identity: it is forced by equation two,
not silently built into the upstream path. -/
theorem k3_fst (h : D.Valid) : D.k3.1 = 1 - 4 * D.a1 / 3 := by
  have h2 := (spec_iff.mp h).2.2.2.2.2.2.1
  change eq2 D.A D.B D.φ D.θ = 0 at h2
  unfold eq2 at h2
  simp only [k3, k2, k1, rot, Prod.fst_add]
  unfold a1
  linear_combination h2 / 6

end SofaUniqueness.Reference.Data
