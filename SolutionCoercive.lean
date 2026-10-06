module

public import ChallengeDefs
public import MovingSofaExtremal.Uniqueness
public import MovingSofaBridge.GerverSofa

/-!
# A second solution of the unchanged Challenge

Uncompiled proof source. This module deliberately does not import Solution or
MovingSofaUniqueness.Main. It uses the same ChallengeDefs and bridge, but its
optimality and uniqueness inputs come from MovingSofaExtremal.

The declaration names live in CoerciveSolution so both solutions can coexist in
one environment. The separate audit compares the twelve statement types with
the canonical solution. No duplicate global theorem names or altered Challenge
statements are used to simulate a second solution.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open scoped EuclideanGeometry
open FormalConjectures

namespace CoerciveSolution

theorem movingSofa_iff_lib (S : Set (ℝ × ℝ)) :
    Baek.IsMovingSofa S ↔ MovingSofaOptimality.IsMovingSofa S := by
  constructor
  · rintro ⟨hc, hconn, θ, c, h1, h2, h3, h4, h5, h6⟩
    exact ⟨-θ 1, hc, hconn, θ, c, ⟨h1, h2, h3, (neg_neg _).symm, h4, h5, h6⟩⟩
  · rintro ⟨w, hc, hconn, θ, c, hm⟩
    exact ⟨hc, hconn, θ, c, hm.continuousOn_angle, hm.continuousOn_shift, hm.angle_zero,
      hm.start, hm.inside, hm.finish⟩

def toLib (P : Baek.GerverParams) : MovingSofaOptimality.GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂,
    P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

def ofLib (P : MovingSofaOptimality.GerverParams) : Baek.GerverParams :=
  ⟨P.φ, P.θ, P.a₁, P.a₂, P.b₁, P.b₂, P.c₁, P.c₂, P.d₁, P.d₂, P.e₁, P.e₂,
    P.κ₁, P.κ₂, P.κ₃, P.κ₄, P.κ₅⟩

theorem toLib_isSolution (P : Baek.GerverParams) : (toLib P).IsSolution ↔ P.IsSolution := Iff.rfl

theorem toLib_inBox (P : Baek.GerverParams) : (toLib P).InBox ↔ P.InBox := Iff.rfl

theorem gerverSofa_eq_lib (P : Baek.GerverParams) :
    Baek.gerverSofa P = MovingSofaOptimality.gerverSofa (toLib P) := rfl

/-- Same statement as Baek.gerver_params_exists. -/
theorem gerver_params_exists : ∃ P : Baek.GerverParams, P.IsSolution ∧ P.InBox := by
  obtain ⟨P, hP, hb⟩ := MovingSofaOptimality.definition8_1_2_exists
  exact ⟨ofLib P, (toLib_isSolution _).1 hP, (toLib_inBox _).1 hb⟩

theorem gerver_params_unique (P Q : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q := by
  have he := MovingSofaOptimality.definition8_1_2_unique ((toLib_isSolution P).2 hP)
    ((toLib_inBox P).2 hPb) ((toLib_isSolution Q).2 hQ) ((toLib_inBox Q).2 hQb)
  cases P
  cases Q
  simp only [toLib, MovingSofaOptimality.GerverParams.mk.injEq] at he
  simpa only [Baek.GerverParams.mk.injEq] using he

theorem gerver_sofa_area (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (Baek.gerverSofa P) ∧
      volume (Baek.gerverSofa P) ≤ ENNReal.ofReal 2.2199 := by
  have hP' := (toLib_isSolution P).2 hP
  have hb' := (toLib_inBox P).2 hPb
  have he := MovingSofaOptimality.gerverSofa_area_mem hP' hb'
  have hfin := MovingSofaOptimality.gerverSofa_volume_ne_top hP' hb'
  rw [gerverSofa_eq_lib, ← ENNReal.ofReal_toReal hfin]
  exact ⟨ENNReal.ofReal_le_ofReal he.1, ENNReal.ofReal_le_ofReal he.2⟩

/-- Same statement; the proof source is the coercive extremal theorem. -/
theorem gerver_sofa_optimal (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    Baek.IsMovingSofa (Baek.gerverSofa P) ∧
      ∀ S, Baek.IsMovingSofa S → volume S ≤ volume (Baek.gerverSofa P) := by
  have he := MovingSofaExtremal.gerver_sofa_optimal ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb)
  rw [gerverSofa_eq_lib, movingSofa_iff_lib]
  exact ⟨he.1, fun S hS => he.2 S ((movingSofa_iff_lib S).1 hS)⟩

theorem gerver_sofa_unique (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (S : Set (ℝ × ℝ)) (hS : Baek.IsMovingSofa S)
    (harea : volume S = volume (Baek.gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => Baek.rot θ p + v) '' S = Baek.gerverSofa P := by
  obtain ⟨g, hg⟩ := MovingSofaExtremal.image_eq_gerver_of_volume_eq
    ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb) ((movingSofa_iff_lib S).1 hS)
    (by rw [← gerverSofa_eq_lib]; exact harea)
  exact ⟨g.angle, g.shift, by rw [gerverSofa_eq_lib]; exact hg⟩

/-- The three bridge statements are unchanged and use the same bridge library. -/
theorem bridge_isMovingSofa_iff (s : Set ℝ²) :
    (∃ m, MovingSofa.IsMovingSofa s m) ↔
      s ⊆ MovingSofa.horizontalHallway ∧ Baek.IsMovingSofa ((fun p : ℝ² => (p 0, p 1)) '' s) := by
  rw [movingSofa_iff_lib]
  exact MovingSofaBridge.isMovingSofa_iff s

theorem bridge_sofaConstant_eq :
    MovingSofa.sofaConstant = ⨆ (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S), volume S :=
  MovingSofaBridge.sofaConstant_eq.trans
    (iSup_congr fun S => iSup_congr_Prop (movingSofa_iff_lib S).symm fun _ => rfl)

theorem bridge_gerversSofa_eq (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    (fun p : ℝ² => (p 0, p 1)) '' MovingSofa.gerversSofa = Baek.gerverSofa P := by
  rw [gerverSofa_eq_lib]
  exact MovingSofaBridge.gerversSofa_eq ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb)

/-- The twelfth Challenge result is already proved in the shared definitions module. -/
theorem gerver_constants_existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    MovingSofa.GerversSofa.ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  MovingSofa.GerversSofa.ABφθSpec.existsUnique

private theorem sofaConstant_eq_volume_baek (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) : MovingSofa.sofaConstant = volume (Baek.gerverSofa P) := by
  have he := gerver_sofa_optimal P hP hPb
  rw [bridge_sofaConstant_eq]
  exact le_antisymm (iSup₂_le he.2)
    (le_iSup₂ (f := fun (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S) => volume S) _ he.1)

private theorem volume_gerversSofa_eq_baek (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) : volume MovingSofa.gerversSofa = volume (Baek.gerverSofa P) := by
  rw [← bridge_gerversSofa_eq P hP hPb]
  exact (MovingSofaBridge.volume_coordinates_image MovingSofa.gerversSofa).symm

theorem formal_isMovingSofa_gerversSofa : ∃ m, MovingSofa.IsMovingSofa MovingSofa.gerversSofa m := by
  obtain ⟨P, hP, hPb⟩ := gerver_params_exists
  rw [bridge_isMovingSofa_iff, bridge_gerversSofa_eq P hP hPb]
  refine ⟨fun p hp => ?_, (gerver_sofa_optimal P hP hPb).1⟩
  have he : (fun p : ℝ² => (p 0, p 1)) p ∈ Baek.gerverSofa P := by
    rw [← bridge_gerversSofa_eq P hP hPb]
    exact ⟨p, hp, rfl⟩
  exact (MovingSofaBridge.coordinates_mem_horizontal p).1 he.1.1

theorem formal_sofaConstant_eq_volume_gerversSofa : MovingSofa.sofaConstant = volume MovingSofa.gerversSofa := by
  obtain ⟨P, hP, hPb⟩ := gerver_params_exists
  rw [sofaConstant_eq_volume_baek P hP hPb, volume_gerversSofa_eq_baek P hP hPb]

/-- Exactly the existing formal-conjectures uniqueness statement, through the new route. -/
theorem formal_volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, MovingSofa.IsMovingSofa s m) :
    volume s = MovingSofa.sofaConstant ↔
      ∃ g : ℝ² ≃ᵃⁱ[ℝ] ℝ², s = g '' MovingSofa.gerversSofa := by
  obtain ⟨P, hP, hPb⟩ := gerver_params_exists
  rw [sofaConstant_eq_volume_baek P hP hPb]
  constructor
  · intro hvol
    obtain ⟨θ, v, hθv⟩ := gerver_sofa_unique P hP hPb _ ((bridge_isMovingSofa_iff s).1 hs).2
      ((MovingSofaBridge.volume_coordinates_image s).trans hvol)
    rw [← bridge_gerversSofa_eq P hP hPb] at hθv
    refine ⟨(MovingSofaBridge.realization (θ, v)).symm, ?_⟩
    rw [← MovingSofaBridge.realization_image_eq θ v hθv]
    simp [Set.image_image]
  · rintro ⟨g, rfl⟩
    rw [MovingSofaBridge.volume_image_affineIsometry, volume_gerversSofa_eq_baek P hP hPb]

end CoerciveSolution
