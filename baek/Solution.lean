module

public import ChallengeDefs
public import MovingSofaOptimality.Main
public import MovingSofaUniqueness.Main
public import MovingSofaBridge.GerverSofa

/-!
# The solution of Baek's entry: the theorems of `baek/Challenge.lean`, proved

This module restates every theorem of `baek/Challenge.lean` (Baek's entry, `baek/comparator.json`)
and proves it, with the Challenge's definitions from `ChallengeDefs`:

* Baek's theorems (`Baek`), from the libraries `MovingSofaOptimality` (Baek's paper, with its
  Theorem 1.1.1) and `MovingSofaUniqueness` (the first proof of the uniqueness of the optimal
  sofa);
* the bridge theorems (`Bridge`), from the library `MovingSofaBridge`;
* formal-conjectures' theorems (`FormalConjectures.MovingSofa`), from the two groups above only: the
  bridge carries Baek's theorems over to formal-conjectures' definitions.

The solution of the certificate entry, the root's `Solution.lean`, proves the same theorems, with
optimality and uniqueness through the coercive certificate.
-/

@[expose] public section

open Real Set MeasureTheory
open scoped EuclideanGeometry

namespace Baek

/-! ### The Challenge's definitions are the library's -/

/-- Moving sofas in the Challenge's vocabulary are moving sofas of the library. -/
theorem isMovingSofa_iff_lib (S : Set (ℝ × ℝ)) :
    IsMovingSofa S ↔ MovingSofaOptimality.IsMovingSofa S := by
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

theorem gerverSofa_eq_lib (P : GerverParams) :
    gerverSofa P = MovingSofaOptimality.gerverSofa P.toLib :=
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
  simpa only [GerverParams.mk.injEq] using h

/-- Gerver's sofa has area `2.219…`: between `2.2192` and `2.2199`. (Gerver's and Romik's value is
`2.21953…`.) -/
theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199 := by
  have hP' := (GerverParams.toLib_isSolution P).2 hP
  have hb' := (GerverParams.toLib_inBox P).2 hPb
  have h := MovingSofaOptimality.gerverSofa_area_mem hP' hb'
  have hfin := MovingSofaOptimality.gerverSofa_volume_ne_top hP' hb'
  rw [gerverSofa_eq_lib, ← ENNReal.ofReal_toReal hfin]
  exact ⟨ENNReal.ofReal_le_ofReal h.1, ENNReal.ofReal_le_ofReal h.2⟩

/-- **Theorem 1.1.1.** Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. -/
theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) := by
  have h := MovingSofaOptimality.theorem1_1_1 ((GerverParams.toLib_isSolution P).2 hP)
    ((GerverParams.toLib_inBox P).2 hPb)
  rw [gerverSofa_eq_lib, isMovingSofa_iff_lib]
  exact ⟨h.1, fun S hS => h.2 S ((isMovingSofa_iff_lib S).1 hS)⟩

/-- **Uniqueness** (not in Baek's paper). Every moving sofa with the area of Gerver's sofa is
congruent to Gerver's sofa: a rotation about the origin followed by a translation maps it onto
Gerver's sofa. -/
theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P := by
  obtain ⟨g, hg⟩ := MovingSofaUniqueness.image_eq_gerver_of_volume_eq
    ((GerverParams.toLib_isSolution P).2 hP) ((GerverParams.toLib_inBox P).2 hPb)
    ((isMovingSofa_iff_lib S).1 hS) (by rw [← gerverSofa_eq_lib]; exact harea)
  exact ⟨g.angle, g.shift, by rw [gerverSofa_eq_lib]; exact hg⟩

end Baek

namespace Bridge

/-- **The two notions of moving sofa agree.** A set `s ⊆ ℝ²` is a moving sofa of formal-conjectures
if and only if it lies in the horizontal side of the hallway and its coordinates form a moving sofa
of Baek's paper. -/
theorem isMovingSofa_iff (s : Set ℝ²) :
    (∃ m, FormalConjectures.MovingSofa.IsMovingSofa s m) ↔
      s ⊆ FormalConjectures.MovingSofa.horizontalHallway ∧
        Baek.IsMovingSofa ((fun p : ℝ² => (p 0, p 1)) '' s) := by
  rw [Baek.isMovingSofa_iff_lib]
  exact MovingSofaBridge.isMovingSofa_iff s

/-- **The two optimal areas agree.** The sofa constant of formal-conjectures is the supremum of the
areas of the moving sofas of Baek's paper. -/
theorem sofaConstant_eq :
    FormalConjectures.MovingSofa.sofaConstant =
      ⨆ (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S), volume S :=
  MovingSofaBridge.sofaConstant_eq.trans
    (iSup_congr fun S => iSup_congr_Prop (Baek.isMovingSofa_iff_lib S).symm fun _ => rfl)

/-- **The two Gerver's sofas agree.** In coordinates, the Gerver's sofa of formal-conjectures,
defined from Gerver's four constants, is the Gerver's sofa of Baek's paper, defined from Romik's
parameters. -/
theorem gerversSofa_eq (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    (fun p : ℝ² => (p 0, p 1)) '' FormalConjectures.MovingSofa.gerversSofa = Baek.gerverSofa P := by
  rw [Baek.gerverSofa_eq_lib]
  exact MovingSofaBridge.gerversSofa_eq ((Baek.GerverParams.toLib_isSolution P).2 hP)
    ((Baek.GerverParams.toLib_inBox P).2 hPb)

end Bridge

namespace FormalConjectures.MovingSofa

/-! ### Formal-conjectures' theorems, from Baek's theorems and the bridge -/

/-- The sofa constant is the area of Baek's Gerver's sofa: Theorem 1.1.1 through
`Bridge.sofaConstant_eq`. -/
private theorem sofaConstant_eq_volume_baek (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) : sofaConstant = volume (Baek.gerverSofa P) := by
  have h := Baek.gerver_sofa_optimal P hP hPb
  rw [Bridge.sofaConstant_eq]
  exact le_antisymm (iSup₂_le h.2)
    (le_iSup₂ (f := fun (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S) => volume S) _ h.1)

/-- The two Gerver's sofas have the same area: `Bridge.gerversSofa_eq`. -/
private theorem volume_gerversSofa_eq_baek (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) :
    volume gerversSofa = volume (Baek.gerverSofa P) := by
  rw [← Bridge.gerversSofa_eq P hP hPb]
  exact (MovingSofaBridge.volume_coordinates_image gerversSofa).symm

/-- Gerver's concrete sofa admits a valid hallway motion. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m := by
  obtain ⟨P, hP, hPb⟩ := Baek.gerver_params_exists
  rw [Bridge.isMovingSofa_iff, Bridge.gerversSofa_eq P hP hPb]
  refine ⟨fun p hp => ?_, (Baek.gerver_sofa_optimal P hP hPb).1⟩
  have h : (fun p : ℝ² => (p 0, p 1)) p ∈ Baek.gerverSofa P := by
    rw [← Bridge.gerversSofa_eq P hP hPb]
    exact ⟨p, hp, rfl⟩
  exact (MovingSofaBridge.coordinates_mem_horizontal p).1 h.1.1

/-- Gerver's sofa attains the sofa constant. -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  obtain ⟨P, hP, hPb⟩ := Baek.gerver_params_exists
  rw [sofaConstant_eq_volume_baek P hP hPb, volume_gerversSofa_eq_baek P hP hPb]

/-- Gerver's sofa is the unique sofa that attains the sofa constant, up to a rigid motion. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  obtain ⟨P, hP, hPb⟩ := Baek.gerver_params_exists
  rw [sofaConstant_eq_volume_baek P hP hPb]
  constructor
  · intro hvol
    obtain ⟨θ, v, hθv⟩ := Baek.gerver_sofa_unique P hP hPb _ ((Bridge.isMovingSofa_iff s).1 hs).2
      ((MovingSofaBridge.volume_coordinates_image s).trans hvol)
    rw [← Bridge.gerversSofa_eq P hP hPb] at hθv
    refine ⟨(MovingSofaBridge.realization (θ, v)).symm, ?_⟩
    rw [← MovingSofaBridge.realization_image_eq θ v hθv]
    simp [Set.image_image]
  · rintro ⟨g, rfl⟩
    rw [MovingSofaBridge.volume_image_affineIsometry, volume_gerversSofa_eq_baek P hP hPb]

end FormalConjectures.MovingSofa
