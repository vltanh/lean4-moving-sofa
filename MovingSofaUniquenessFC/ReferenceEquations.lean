module

public import Mathlib

/-!
# Algebraic reduction of the upstream Gerver parameter specification

The predicate `Spec` below is a literal mathematical copy of the upstream
`MovingSofa.GerversSofa.ABφθSpec` (Formal Conjectures Authors, Apache-2.0).
The elimination identities are those of Romik's four-equation system; compare
RuifengCao/sofa-formal, Sofa/GerverConst.lean. This module does not import that
reference implementation or its interval-certificate computations.

All algebra is proved with explicit identities and ordinary proof-producing
tactics. This is preparatory work for the exact-reference integration, NOT a
proof that the two reduced equations have a unique zero on their whole domain.
In particular there is no replacement of global uniqueness by small-box
uniqueness, and no upstream constants are chosen here.
-/

@[expose] public section
noncomputable section

open Real Set

namespace MovingSofaUniquenessFC.Reference

/-- The full upstream parameter domain and all four equations. -/
def Spec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

def eq1 (A B φ θ : ℝ) : ℝ :=
  A * (cos θ - cos φ) - 2 * B * sin φ +
    (θ - φ - 1) * cos θ - sin θ + cos φ + sin φ

def eq2 (A B φ θ : ℝ) : ℝ :=
  A * (3 * sin θ + sin φ) - 2 * B * cos φ +
    3 * (θ - φ - 1) * sin θ + 3 * cos θ - sin φ + cos φ

def eq3 (A B φ _θ : ℝ) : ℝ :=
  A * cos φ - (sin φ + 1 / 2 - cos φ / 2 + B * sin φ)

def eq4 (A B φ θ : ℝ) : ℝ :=
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4)

theorem spec_iff {A B φ θ : ℝ} : Spec A B φ θ ↔
    0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
      eq1 A B φ θ = 0 ∧ eq2 A B φ θ = 0 ∧
      eq3 A B φ θ = 0 ∧ eq4 A B φ θ = 0 := Iff.rfl

def den (φ θ : ℝ) : ℝ := 3 * cos φ - cos θ

def num (φ θ : ℝ) : ℝ :=
  (θ - φ) * cos θ + 3 * sin φ - sin θ - cos θ + 1

def slope (φ θ : ℝ) : ℝ := 1 + (θ - φ) / 2

def offset (φ θ : ℝ) : ℝ :=
  π / 2 - φ - θ + (θ - φ) / 2 + (θ - φ)^2 / 4

def reducedQ (φ θ : ℝ) : ℝ :=
  num φ θ * (cos φ - sin φ * slope φ θ) -
    den φ θ * (sin φ + 1 / 2 - cos φ / 2 + sin φ * offset φ θ)

def reducedR (φ θ : ℝ) : ℝ :=
  num φ θ * (3 * sin θ + sin φ - 2 * cos φ * slope φ θ) +
    den φ θ * (3 * (θ - φ - 1) * sin θ + 3 * cos θ - sin φ + cos φ -
      2 * cos φ * offset φ θ)

def reconstructedA (φ θ : ℝ) : ℝ := num φ θ / den φ θ

def reconstructedB (φ θ : ℝ) : ℝ := reconstructedA φ θ * slope φ θ + offset φ θ

/-- The denominator is positive on the ENTIRE upstream angle triangle. -/
theorem den_pos {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) : 0 < den φ θ := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hmono : cos θ ≤ cos φ :=
    cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_pos]) horder
  unfold den
  linarith

/-- Subtracting twice equation three from equation one eliminates B. -/
theorem eliminate_B (A B φ θ : ℝ) :
    eq1 A B φ θ - 2 * eq3 A B φ θ = num φ θ - A * den φ θ := by
  unfold eq1 eq3 num den
  ring

/-- Equation four determines B once A and the angles are known. -/
theorem eliminate_eq4 (A B φ θ : ℝ) :
    eq4 A B φ θ = A * slope φ θ + offset φ θ - B := by
  unfold eq4 slope offset
  ring

/-- An identity valid before assuming any of the four equations. -/
theorem reducedQ_identity (A B φ θ : ℝ) :
    reducedQ φ θ = den φ θ * (eq3 A B φ θ - sin φ * eq4 A B φ θ) +
      (cos φ - sin φ * slope φ θ) * (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  unfold reducedQ den num slope offset eq1 eq3 eq4
  ring

theorem reducedR_identity (A B φ θ : ℝ) :
    reducedR φ θ = den φ θ * (eq2 A B φ θ - 2 * cos φ * eq4 A B φ θ) +
      (3 * sin θ + sin φ - 2 * cos φ * slope φ θ) *
        (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  unfold reducedR den num slope offset eq1 eq2 eq3 eq4
  ring

/-- Every solution is a zero of the two reduced scalar equations. -/
theorem Spec.reduced_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    reducedQ φ θ = 0 ∧ reducedR φ θ = 0 := by
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4⟩ := spec_iff.mp h
  rw [reducedQ_identity A B, reducedR_identity A B, h1, h2, h3, h4]
  constructor <;> ring

/-- The two coefficients are uniquely reconstructed from the two angles. -/
theorem Spec.coefficients {A B φ θ : ℝ} (h : Spec A B φ θ) :
    A = reconstructedA φ θ ∧ B = reconstructedB φ θ := by
  obtain ⟨hφ, horder, hθ, _, _, h1, _, h3, h4⟩ := spec_iff.mp h
  have hD := den_pos hφ horder hθ
  have hid := eliminate_B A B φ θ
  rw [h1, h3] at hid
  have hmul : A * den φ θ = num φ θ := by linarith
  have hA : A = reconstructedA φ θ := by
    exact (eq_div_iff hD.ne').mpr hmul
  have hb := eliminate_eq4 A B φ θ
  rw [h4, hA] at hb
  exact ⟨hA, by unfold reconstructedB; linarith⟩

/-- Conversely, a reduced zero reconstructs a solution whenever its two
coefficients are nonnegative, exactly as required in the upstream domain. -/
theorem spec_of_reduced_zero {φ θ : ℝ} (hφ : 0 ≤ φ) (horder : φ ≤ θ)
    (hθ : θ ≤ π / 4) (hA : 0 ≤ reconstructedA φ θ)
    (hB : 0 ≤ reconstructedB φ θ) (hQ : reducedQ φ θ = 0)
    (hR : reducedR φ θ = 0) :
    Spec (reconstructedA φ θ) (reconstructedB φ θ) φ θ := by
  let A := reconstructedA φ θ
  let B := reconstructedB φ θ
  have hD := den_pos hφ horder hθ
  have hmul : A * den φ θ = num φ θ := by
    dsimp [A, reconstructedA]
    exact div_mul_cancel₀ _ hD.ne'
  have h4 : eq4 A B φ θ = 0 := by
    rw [eliminate_eq4]
    dsimp [B, reconstructedB, A]
    ring
  have hdifference : eq1 A B φ θ - 2 * eq3 A B φ θ = 0 := by
    rw [eliminate_B, hmul, sub_self]
  have h3mul : den φ θ * eq3 A B φ θ = 0 := by
    have hid := reducedQ_identity A B φ θ
    rw [hQ, h4, hdifference] at hid
    simpa only [mul_zero, sub_zero, add_zero] using hid.symm
  have h3 : eq3 A B φ θ = 0 :=
    (mul_eq_zero.mp h3mul).resolve_left hD.ne'
  have h1 : eq1 A B φ θ = 0 := by linarith
  have h2mul : den φ θ * eq2 A B φ θ = 0 := by
    have hid := reducedR_identity A B φ θ
    rw [hR, h4, hdifference] at hid
    simpa only [mul_zero, sub_zero, add_zero] using hid.symm
  have h2 : eq2 A B φ θ = 0 :=
    (mul_eq_zero.mp h2mul).resolve_left hD.ne'
  exact spec_iff.mpr ⟨hφ, horder, hθ, hA, hB, h1, h2, h3, h4⟩

/-- There cannot be two different coefficient pairs at the same angles. -/
theorem coefficients_unique {A B A' B' φ θ : ℝ}
    (h : Spec A B φ θ) (h' : Spec A' B' φ θ) : A = A' ∧ B = B' :=
  ⟨h.coefficients.1.trans h'.coefficients.1.symm,
    h.coefficients.2.trans h'.coefficients.2.symm⟩

end MovingSofaUniquenessFC.Reference
