module

public import MovingSofaExtremal.Statements
public import MovingSofaExtremal.Certificate

/-!
# The solution of version 5: the seventeen theorems of `Challenge.lean`

This module is the solution that Comparator checks against `Challenge.lean` (`comparator.json`).
`MovingSofaExtremal.Statements` proves fifteen of its theorems, with optimality, uniqueness and
stability through the coercive certificate, in the namespace `CoerciveSolution`, so that the audits
can load it together with `baek/Solution.lean`; this module states fourteen of them under the
Challenge's names, each proved by the theorem of `MovingSofaExtremal.Statements`. The fifteenth,
`FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`, is proved in
`MovingSofaBridge.Defs`, for both Challenges, and the last two, `Certificate.coercive_certificate` and
`Certificate.gerver_triple`, in `MovingSofaExtremal.Certificate`. The module declares the names that
`baek/Solution.lean` declares, so no module imports it.
-/

@[expose] public section

open Real Set MeasureTheory
open scoped EuclideanGeometry

namespace Baek

/-- Romik's system has a solution in the stated range. -/
theorem gerver_params_exists : ∃ P : GerverParams, P.IsSolution ∧ P.InBox :=
  CoerciveSolution.gerver_params_exists

/-- Romik's system has at most one solution in the stated range. -/
theorem gerver_params_unique (P Q : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (hQ : Q.IsSolution) (hQb : Q.InBox) : P = Q :=
  CoerciveSolution.gerver_params_unique P Q hP hPb hQ hQb

/-- Gerver's sofa has area `2.219…`: between `2.2192` and `2.2199`. (Gerver's and Romik's value is
`2.21953…`.) -/
theorem gerver_sofa_area (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ENNReal.ofReal 2.2192 ≤ volume (gerverSofa P) ∧ volume (gerverSofa P) ≤ ENNReal.ofReal 2.2199 :=
  CoerciveSolution.gerver_sofa_area P hP hPb

/-- **Theorem 1.1.1.** Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
of Gerver's sofa. -/
theorem gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  CoerciveSolution.gerver_sofa_optimal P hP hPb

/-- **Uniqueness** (not in Baek's paper). Every moving sofa with the area of Gerver's sofa is
congruent to Gerver's sofa: a rotation about the origin followed by a translation maps it onto
Gerver's sofa. -/
theorem gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) (S : Set (ℝ × ℝ))
    (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P :=
  CoerciveSolution.gerver_sofa_unique P hP hPb S hS harea

open scoped symmDiff in
/-- **Stability** (not in Baek's paper). There are constants `C`, `C'` and `ε₀ > 0` such that every
moving sofa `S` whose area is less than the area of Gerver's sofa by `ε < ε₀`, once normalized, lies
within Euclidean Hausdorff distance `C √ε` of Gerver's sofa, and the symmetric difference of the two
has area at most `C' √ε`. -/
theorem gerver_sofa_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C C' ε₀ : ℝ, 0 < C ∧ 0 < C' ∧ 0 < ε₀ ∧
      ∀ S, IsMovingSofa S → sofaDeficit P S < ε₀ →
        EuclideanClose (C * √(sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        (volume (normalizedSofa P S ∆ gerverSofa P)).toReal ≤ C' * √(sofaDeficit P S) :=
  CoerciveSolution.gerver_sofa_stable P hP hPb

/-- **Stability of the rotation angle** (not in Baek's paper). There are constants `C` and `ε₀ > 0`
such that a moving sofa whose area is less than the area of Gerver's sofa by `ε < ε₀`, and whose
motion turns it clockwise by an angle `ω ∈ [arccos (5/11), π/2]`, has `π/2 - ω ≤ C ε`. -/
theorem gerver_sofa_angle_stable (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ S ω, IsMovingSofaWithAngle S ω → ω ∈ Icc (arccos (5 / 11)) (π / 2) →
        sofaDeficit P S < ε₀ → π / 2 - ω ≤ C * sofaDeficit P S :=
  CoerciveSolution.gerver_sofa_angle_stable P hP hPb

/-- **The exponent `1/2` is optimal** (not in Baek's paper). For every exponent `a > 1/2`, every
constant `C` and every `ε₀ > 0`, there is a moving sofa `S` whose deficit `ε` satisfies `0 < ε < ε₀`
and which lies within Euclidean Hausdorff distance `C εᵃ` of no image of Gerver's sofa by a rotation
about the origin followed by a translation. -/
theorem gerver_sofa_stability_exponent (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (a C ε₀ : ℝ) (ha : 1 / 2 < a) (hε₀ : 0 < ε₀) :
    ∃ S, IsMovingSofa S ∧ 0 < sofaDeficit P S ∧ sofaDeficit P S < ε₀ ∧
      ∀ (θ : ℝ) (v : ℝ × ℝ),
        ¬ EuclideanClose (C * sofaDeficit P S ^ a) S ((fun p => rot θ p + v) '' gerverSofa P) :=
  CoerciveSolution.gerver_sofa_stability_exponent P hP hPb a C ε₀ ha hε₀

end Baek

namespace Bridge

/-- **The two notions of moving sofa agree.** A set `s ⊆ ℝ²` is a moving sofa of formal-conjectures
if and only if it lies in the horizontal side of the hallway and its coordinates form a moving sofa
of Baek's paper. -/
theorem isMovingSofa_iff (s : Set ℝ²) :
    (∃ m, FormalConjectures.MovingSofa.IsMovingSofa s m) ↔
      s ⊆ FormalConjectures.MovingSofa.horizontalHallway ∧
        Baek.IsMovingSofa ((fun p : ℝ² => (p 0, p 1)) '' s) :=
  CoerciveSolution.bridge_isMovingSofa_iff s

/-- **The two optimal areas agree.** The sofa constant of formal-conjectures is the supremum of the
areas of the moving sofas of Baek's paper. -/
theorem sofaConstant_eq :
    FormalConjectures.MovingSofa.sofaConstant =
      ⨆ (S : Set (ℝ × ℝ)) (_ : Baek.IsMovingSofa S), volume S :=
  CoerciveSolution.bridge_sofaConstant_eq

/-- **The two Gerver's sofas agree.** In coordinates, the Gerver's sofa of formal-conjectures,
defined from Gerver's four constants, is the Gerver's sofa of Baek's paper, defined from Romik's
parameters. -/
theorem gerversSofa_eq (P : Baek.GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    (fun p : ℝ² => (p 0, p 1)) '' FormalConjectures.MovingSofa.gerversSofa = Baek.gerverSofa P :=
  CoerciveSolution.bridge_gerversSofa_eq P hP hPb

end Bridge

namespace FormalConjectures.MovingSofa

/-- Gerver's concrete sofa admits a valid hallway motion. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m :=
  CoerciveSolution.formal_isMovingSofa_gerversSofa

/-- Gerver's sofa attains the sofa constant. -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa :=
  CoerciveSolution.formal_sofaConstant_eq_volume_gerversSofa

/-- Gerver's sofa is the unique sofa that attains the sofa constant, up to a rigid motion. -/
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa :=
  CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa s hs

end FormalConjectures.MovingSofa
