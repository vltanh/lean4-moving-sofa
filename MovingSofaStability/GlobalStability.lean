module

public import MovingSofaStability.QualitativeEntry

/-!
# Unrestricted stability of Gerver's sofa

Uncompiled proof source. The conclusions concern the actual nonconvex sets in
the repository's original moving-sofa definition. All analytic and geometric
prerequisites are supplied by the preceding modules; neither an injective
envelope nor a stability estimate is assumed of the input sofa.

This file completes the written source assembly, not Lean kernel verification.
No claim is made that the global constants are sharp or effectively computed.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness
open GerverParams

namespace MovingSofaStability

/-- An exact maximizer equals Gerver after the prescribed translation. -/
theorem normalizedSofa_eq_gerver_of_zero_deficit {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Point}
    (hS : IsMovingSofa S) (hzero : sofaDeficit P S = 0) :
    normalizedSofa P S = gerverSofa P := by
  have hc := isCompact_of_isMovingSofa hS
  have hn := hS.choose_spec.2.1.nonempty
  apply pinned_maximizer_eq_gerver hP hbox (normalizedSofa_moving P hS)
    (normalizedSofa_top P hc hn) (normalizedSofa_left P hc hn)
  rw [area_normalizedSofa]
  unfold sofaDeficit at hzero
  linarith

/-- In a reduced angle range Gerver itself must complete the right-angle turn. -/
theorem gerver_reduced_angle_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {ω : ℝ} (hω : ω ∈ Icc (arccos (5 / 11)) (π / 2))
    (hmove : IsMovingSofaWithAngle (gerverSofa P) ω) : ω = π / 2 := by
  by_contra hne
  obtain ⟨p, hp, q, hq, hgt⟩ := gerver_width_gt_one hP hbox
    ⟨(arccos_nonneg _).trans hω.1, by linarith [hω.2, pi_pos]⟩ hne
  have hle := moving_terminal_projection hmove hq hp
  linarith

/-- A single neighborhood and one choice of constants work for every reduced
motion of every sufficiently near-optimal original sofa. -/
theorem reduced_sofa_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    ∃ C Carea Cangle ε₀ : ℝ,
      0 < C ∧ 0 < Carea ∧ 0 < Cangle ∧ 0 < ε₀ ∧
      ∀ S : Set Point, ∀ ω : ℝ, IsMovingSofaWithAngle S ω →
      ω ∈ Icc (arccos (5 / 11)) (π / 2) → sofaDeficit P S < ε₀ →
        EuclideanClose (C * sqrt (sofaDeficit P S)) (normalizedSofa P S) (gerverSofa P) ∧
        symmetricDifferenceArea (normalizedSofa P S) (gerverSofa P) ≤ Carea * sqrt (sofaDeficit P S) ∧
        0 ≤ π / 2 - ω ∧ π / 2 - ω ≤ Cangle * sofaDeficit P S := by
  sorry

/-- The unrestricted actual-set stability theorem, in the precise target
proposition. No geometric certificate is an assumption of this theorem. -/
theorem unrestricted_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P := by
  sorry

/-- The missing terminal angle is controlled linearly in the original area deficit. -/
theorem terminal_angle_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P := by
  obtain ⟨C, Carea, Cangle, ε₀, hC, hCarea, hCangle, hε₀, hresult⟩ := reduced_sofa_stability hP hbox
  exact ⟨Cangle, ε₀, hCangle, hε₀, fun S ω hS hω hε => (hresult S ω hS hω hε).2.2⟩

end MovingSofaStability
