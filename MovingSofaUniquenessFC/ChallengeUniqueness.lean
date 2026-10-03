module

public import Mathlib

/-!
# Independent statement: uniqueness of Gerver's sofa

Copyright 2026 The Formal Conjectures Authors. Apache-2.0.
Definitions are from FormalConjectures/Wikipedia/MovingSofa.lean, Git blob
59b6ed7eb42e11b208b09539c245da4d3f11ed00, using the Mathlib-only prelude of
RuifengCao/sofa-formal's SofaSubmission/Challenge.lean.

This Challenge deliberately does not import the solution or its dependencies.
Its three proof placeholders belong to the independent statement environment:
parameter existence and uniqueness, `one_le_sofaConstant`, and the target
theorem. The solution proves the first and the last
(`MovingSofa.GerversSofa.ABφθSpec.existsUnique` in `ReferenceDefs.lean`,
`MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa` in `Final.lean`)
and imports no Challenge module.

The target concerns the original connected closed set and its actual planar
volume. No smoothness, injectivity, regular-closedness, balancedness, or
congruence assumption is imposed on a competing sofa.
-/

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable section

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The horizontal side is `(-∞,1] × [0,1]`. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The vertical side is `[0,1] × (-∞,1]`. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/-- An identity-start continuous Euclidean motion through the hallway. -/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/-- The unit square, retained in the upstream definition order. -/
def unitSquare : Set ℝ² := parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)

private lemma mem_Icc_of_mem_unitSquare {p : ℝ²} (hp : p ∈ unitSquare) (i : Fin 2) :
    p i ∈ Set.Icc (0 : ℝ) 1 := by
  have h := parallelepiped_basis_eq (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [unitSquare, show parallelepiped ⇑(EuclideanSpace.basisFun (Fin 2) ℝ) =
    parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis by
      rw [OrthonormalBasis.coe_toBasis], h] at hp
  simpa using hp i

theorem isMovingSofa_unitSquare : ∃ m, IsMovingSofa unitSquare m := by
  refine ⟨fun _ => .refl ℝ ℝ², ?_, ?_, continuous_const, rfl, ?_, ?_, ?_⟩
  · unfold unitSquare parallelepiped
    refine ⟨⟨0, 0, by simp, by simp⟩, (convex_Icc _ _).isPreconnected.image _ ?_⟩
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).continuousOn
  · unfold unitSquare parallelepiped
    exact (isCompact_Icc.image
      (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).smul continuous_const)).isClosed
  · intro p hp
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.2.trans (by norm_num), h1.1, h1.2⟩,
      by ext i; fin_cases i <;> rfl⟩
  · rintro t q ⟨p, hp, rfl⟩
    rw [show (AffineIsometryEquiv.refl ℝ ℝ²) p = p from rfl]
    refine .inl ?_
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.2.trans (by norm_num), h1.1, h1.2⟩,
      by ext i; fin_cases i <;> rfl⟩
  · rintro q ⟨p, hp, rfl⟩
    rw [show (AffineIsometryEquiv.refl ℝ ℝ²) p = p from rfl]
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.1, h0.2, h1.2.trans (by norm_num)⟩,
      by ext i; fin_cases i <;> rfl⟩

/-- Translate first, then rotate; this is the upstream convention. -/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

theorem rotateTranslate_apply (α : Real.Angle) (p q : ℝ²) :
    rotateTranslate α p q = EuclideanGeometry.o.rotation α (q + p) := rfl

/-- The special endpoint hallways are part of the definition. -/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-- The upstream system for Gerver's four constants, with its full domain. -/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- Independent statement placeholder; the solution imports its existing proof. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 := by
  sorry

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
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ)^2 / 4
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

def gerversSofa : Set ℝ² := sofaOfRotateTranslatePath GerversSofa.p

open MeasureTheory
open scoped ENNReal

def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

theorem one_le_sofaConstant : 1 ≤ sofaConstant := by
  sorry

/-- Gerver's concrete sofa uniquely attains the sofa constant up to rigid motion. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  sorry

end MovingSofa
