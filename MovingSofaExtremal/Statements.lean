module

public import MovingSofaBridge.Defs
public import MovingSofaExtremal.Unified
public import MovingSofaStability.Sharpness
public import MovingSofaBridge.GerverSofa

/-!
# Version 5: fifteen of its theorems

This module proves fifteen of the seventeen theorems of `Challenge.lean`, the Challenge at the root
(version 5 of the Palomar entry): the twelve that `baek/Challenge.lean` (the Challenge of versions 1
to 4) states too, and the three stability theorems. It uses the definitions of
`MovingSofaBridge.Defs` and the bridge `MovingSofaBridge`, with optimality, uniqueness and stability
taken from the coercive route `MovingSofaExtremal` (`gerver_sofa_optimal_unique_stable`). It imports
neither `baek.Solution` nor `MovingSofaUniqueness.Main`. `Solution`, the solution at the root,
states these theorems under the Challenge's names, with the two theorems about the certificate of
`MovingSofaExtremal.Certificate`.

The theorems are in the namespace `CoerciveSolution`, so that the audits can load them together with
`baek/Solution.lean`; `scripts/AuditCoerciveRoute.lean` checks that the twelve that
`baek/Solution.lean` also states have exactly the types of the matching theorems of
`baek/Solution.lean` (it lists the pairs; for the bridge and formal-conjectures' theorems the names
differ, as in `bridge_isMovingSofa_iff` for `Bridge.isMovingSofa_iff`), and that none of the fifteen
uses Baek's Theorem 1.1.1, his results on balanced caps, or the first proof of uniqueness.
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

/-- The statement of `Baek.gerver_params_exists`. -/
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

/-- The statement of `Baek.gerver_sofa_optimal`, through the coercive route. -/
theorem gerver_sofa_optimal (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    Baek.IsMovingSofa (Baek.gerverSofa P) ∧
      ∀ S, Baek.IsMovingSofa S → volume S ≤ volume (Baek.gerverSofa P) := by
  have he := MovingSofaExtremal.gerver_sofa_optimal ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb)
  rw [gerverSofa_eq_lib, movingSofa_iff_lib]
  exact ⟨he.1, fun S hS => he.2 S ((movingSofa_iff_lib S).1 hS)⟩

/-- The statement of `Baek.gerver_sofa_unique`, through the coercive route. -/
theorem gerver_sofa_unique (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (S : Set (ℝ × ℝ)) (hS : Baek.IsMovingSofa S)
    (harea : volume S = volume (Baek.gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => Baek.rot θ p + v) '' S = Baek.gerverSofa P := by
  obtain ⟨g, hg⟩ := MovingSofaExtremal.image_eq_gerver_of_volume_eq
    ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb) ((movingSofa_iff_lib S).1 hS)
    (by rw [← gerverSofa_eq_lib]; exact harea)
  exact ⟨g.angle, g.shift, by rw [gerverSofa_eq_lib]; exact hg⟩

/-- The statement of `Bridge.isMovingSofa_iff`, from the same bridge library. -/
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

/-- The statement of `FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`, which
`MovingSofaBridge.Defs` proves. -/
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

/-- The statement of
`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`, through the
coercive route. -/
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

/-! ### Stability -/

/-- Moving sofas with a rotation angle, in the Challenge's vocabulary, are those of the library. -/
theorem isMovingSofaWithAngle_iff_lib (S : Set (ℝ × ℝ)) (ω : ℝ) :
    Baek.IsMovingSofaWithAngle S ω ↔ MovingSofaOptimality.IsMovingSofaWithAngle S ω := by
  constructor
  · rintro ⟨hc, hconn, θ, c, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨hc, hconn, θ, c, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  · rintro ⟨hc, hconn, θ, c, hm⟩
    exact ⟨hc, hconn, θ, c, hm.continuousOn_angle, hm.continuousOn_shift, hm.angle_zero,
      hm.angle_one, hm.start, hm.inside, hm.finish⟩

/-- The deficit in the Challenge's vocabulary is the library's. -/
theorem sofaDeficit_eq_lib (P : Baek.GerverParams) (S : Set (ℝ × ℝ)) :
    Baek.sofaDeficit P S = MovingSofaStability.sofaDeficit (toLib P) S :=
  rfl

/-- The Euclidean distance in the Challenge's vocabulary is the library's. -/
theorem euclideanDist_eq_lib (p q : ℝ × ℝ) :
    Baek.euclideanDist p q = MovingSofaStability.euclideanDist p q := by
  simp only [Baek.euclideanDist, MovingSofaStability.euclideanDist, MovingSofaOptimality.norm2,
    MovingSofaOptimality.dot, Prod.fst_sub, Prod.snd_sub]
  congr 1
  ring

/-- Closeness in the Challenge's vocabulary is the library's. -/
theorem euclideanClose_iff_lib (r : ℝ) (S T : Set (ℝ × ℝ)) :
    Baek.EuclideanClose r S T ↔ MovingSofaStability.EuclideanClose r S T := by
  simp only [Baek.EuclideanClose, MovingSofaStability.EuclideanClose,
    MovingSofaStability.DirectedClose, euclideanDist_eq_lib]

/-- The support function in the direction `π` is minus the least abscissa. -/
theorem supp_pi_eq (X : Set (ℝ × ℝ)) : MovingSofaOptimality.supp X π = -sInf (Prod.fst '' X) := by
  rw [MovingSofaOptimality.supp, ← Real.sSup_neg]
  congr 1
  ext y
  simp only [mem_image, Set.mem_neg, MovingSofaOptimality.dot, MovingSofaOptimality.uvec, cos_pi,
    sin_pi, mul_neg, mul_one, mul_zero, add_zero]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by ring⟩
  · rintro ⟨p, hp, hpy⟩
    exact ⟨p, hp, by linarith⟩

/-- The support function in the direction `π/2` is the greatest height. -/
theorem supp_pi_div_two_eq (X : Set (ℝ × ℝ)) :
    MovingSofaOptimality.supp X (π / 2) = sSup (Prod.snd '' X) := by
  rw [MovingSofaOptimality.supp]
  congr 1
  ext y
  simp only [mem_image, MovingSofaOptimality.dot, MovingSofaOptimality.uvec, cos_pi_div_two,
    sin_pi_div_two, mul_zero, mul_one, zero_add]

/-- The normalization in the Challenge's vocabulary is the library's. -/
theorem normalizedSofa_eq_lib (P : Baek.GerverParams) (S : Set (ℝ × ℝ)) :
    Baek.normalizedSofa P S = MovingSofaStability.normalizedSofa (toLib P) S := by
  rw [MovingSofaStability.normalizedSofa, MovingSofaUniqueness.Rigid.coe_translate,
    MovingSofaStability.normalizingShift, supp_pi_eq, supp_pi_eq, supp_pi_div_two_eq,
    ← gerverSofa_eq_lib, Baek.normalizedSofa]
  congr 2
  ext p
  · simp only [Prod.fst_add]
    ring
  · rfl

open scoped symmDiff in
/-- The statement of `Baek.gerver_sofa_stable`, through the coercive route. -/
theorem gerver_sofa_stable (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C C' ε₀ : ℝ, 0 < C ∧ 0 < C' ∧ 0 < ε₀ ∧
      ∀ S, Baek.IsMovingSofa S → Baek.sofaDeficit P S < ε₀ →
        Baek.EuclideanClose (C * √(Baek.sofaDeficit P S)) (Baek.normalizedSofa P S)
          (Baek.gerverSofa P) ∧
        (volume (Baek.normalizedSofa P S ∆ Baek.gerverSofa P)).toReal ≤
          C' * √(Baek.sofaDeficit P S) := by
  obtain ⟨C, C', ε₀, hC, hC', hε₀, h⟩ := (MovingSofaExtremal.gerver_sofa_optimal_unique_stable
    ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb)).2.2.2.1
  refine ⟨C, C', ε₀, hC, hC', hε₀, fun S hS hε => ?_⟩
  obtain ⟨h1, h2⟩ := h S ((movingSofa_iff_lib S).1 hS) hε
  rw [euclideanClose_iff_lib, normalizedSofa_eq_lib, sofaDeficit_eq_lib, gerverSofa_eq_lib]
  exact ⟨h1, h2⟩

/-- The statement of `Baek.gerver_sofa_angle_stable`, through the coercive route. -/
theorem gerver_sofa_angle_stable (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ S ω, Baek.IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
        Baek.sofaDeficit P S < ε₀ → π / 2 - ω ≤ C * Baek.sofaDeficit P S := by
  obtain ⟨C, ε₀, hC, hε₀, h⟩ := (MovingSofaExtremal.gerver_sofa_optimal_unique_stable
    ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb)).2.2.2.2
  exact ⟨C, ε₀, hC, hε₀, fun S ω hS hω hε =>
    (h S ω ((isMovingSofaWithAngle_iff_lib S ω).1 hS) hω hε).2⟩

/-- The statement of `Baek.gerver_sofa_stability_exponent`, from the punctured sofas of
`MovingSofaStability`, which use neither optimality nor uniqueness. -/
theorem gerver_sofa_stability_exponent (P : Baek.GerverParams) (hP : P.IsSolution)
    (hPb : P.InBox) (a C ε₀ : ℝ) (ha : 1 / 2 < a) (hε₀ : 0 < ε₀) :
    ∃ S, Baek.IsMovingSofa S ∧ 0 < Baek.sofaDeficit P S ∧ Baek.sofaDeficit P S < ε₀ ∧
      ∀ (θ : ℝ) (v : ℝ × ℝ),
        ¬ Baek.EuclideanClose (C * Baek.sofaDeficit P S ^ a) S
          ((fun p => Baek.rot θ p + v) '' Baek.gerverSofa P) := by
  obtain ⟨S, hS, hpos, hlt, hfar⟩ := MovingSofaStability.no_hausdorff_exponent_gt_half
    ((toLib_isSolution P).2 hP) ((toLib_inBox P).2 hPb) ha C hε₀
  refine ⟨S, (movingSofa_iff_lib S).2 hS, hpos, hlt, fun θ v hclose => hfar ⟨θ, v⟩ ?_⟩
  rw [euclideanClose_iff_lib, sofaDeficit_eq_lib, gerverSofa_eq_lib] at hclose
  exact hclose

end CoerciveSolution
