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
  obtain ⟨C, c, δ, α₀, εL, hC, hc, hδ, hδ1, hα₀, hεL, hεL1, hlocal⟩ :=
    local_positive_sofa_hausdorff hP hbox
  obtain ⟨Carea, εA, hCarea, hεA, hεA1, harea⟩ :=
    gerver_symmetricDifference_from_distance hP hbox hC
  obtain ⟨εQ, hεQ, hentry⟩ := near_maximizers_enter_neighborhood hP hbox hδ hα₀
  let ε₀ := min εL (min εA εQ)
  have hε₀ : 0 < ε₀ := lt_min hεL (lt_min hεA hεQ)
  have eL : ε₀ ≤ εL := min_le_left _ _
  have eA : ε₀ ≤ εA := (min_le_right _ _).trans (min_le_left _ _)
  have eQ : ε₀ ≤ εQ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, Carea, 1 / c, ε₀, hC, hCarea, one_div_pos.mpr hc, hε₀, ?_⟩
  intro S ω hS hω hε
  have hSmove : IsMovingSofa S := ⟨ω, hS⟩
  have hdef := sofaDeficit_nonneg hP hbox hSmove
  have hα : 0 ≤ π / 2 - ω := sub_nonneg.mpr hω.2
  rcases eq_or_lt_of_le hdef with hzero | hpositive
  · have hz : sofaDeficit P S = 0 := hzero.symm
    have hset := normalizedSofa_eq_gerver_of_zero_deficit hP hbox hSmove hz
    have hGmove := normalizedSofa_movingWithAngle P hS
    rw [hset] at hGmove
    have hωeq := gerver_reduced_angle_eq hP hbox hω hGmove
    rw [hz, sqrt_zero, mul_zero, mul_zero, mul_zero, hset, hωeq, sub_self]
    refine ⟨EuclideanClose.refl _ le_rfl, ?_, le_rfl, le_rfl⟩
    simp [symmetricDifferenceArea, area]
  · have hcompact := ms_isCompact_of_isMovingSofaWithAngle hS
    have hne := hS.2.1.nonempty
    let N := normalizedSofa P S
    have hNmove : IsMovingSofaWithAngle N ω := normalizedSofa_movingWithAngle P hS
    have hNc := ms_isCompact_of_isMovingSofaWithAngle hNmove
    have hNne := hNmove.2.1.nonempty
    have htop : supp N (π / 2) = 1 := normalizedSofa_top P hcompact hne
    have hleft : supp N π = supp (gerverSofa P) π := normalizedSofa_left P hcompact hne
    have hstrip := normalizedSofa_strip P hSmove
    obtain ⟨hclose, hangle⟩ := hentry S ω hS hω (hε.trans_le eQ)
    let K := sofaCap N
    have hK : IsCap K (π / 2) := sofaCap_isCap hNc hNne hstrip htop
    have hKleft : supp K π = supp P.cap π := by
      rw [sofaCap_upper_support hNc hNne hstrip htop ⟨pi_pos.le, le_rfl⟩,
        hleft, gerver_upper_support hP hbox ⟨pi_pos.le, le_rfl⟩]
    have hKclose : UpperSupportClose δ K P.cap :=
      sofaCap_close_to_gerver hP hbox hNc hNne hstrip htop hclose
    have hω' : ω ∈ Icc (0 : ℝ) (π / 2) := ⟨(arccos_nonneg _).trans hω.1, hω.2⟩
    have hconstraints : PartialSofaConstraints K N ω := sofaCap_partial_constraints hNmove hω' htop
    have heq : sofaDeficit P S = area (gerverSofa P) - area N := by
      rw [area_normalizedSofa]
      rfl
    obtain ⟨hd, ha⟩ := hlocal K hK hKleft hKclose N hNc.measurableSet ω hω' hangle.le hconstraints
      (sofaDeficit P S) heq hpositive (hε.trans_le eL)
    have had := harea N hNc (sofaDeficit P S) ⟨hpositive, (hε.trans_le eA).le⟩ heq hd
    refine ⟨hd, had, hα, ?_⟩
    rwa [one_div_mul_eq_div]

/-- The unrestricted actual-set stability theorem, in the precise target
proposition. No geometric certificate is an assumption of this theorem. -/
theorem unrestricted_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P := by
  obtain ⟨C, Carea, Cangle, εR, hC, hCarea, hCangle, hεR, hresult⟩ := reduced_sofa_stability hP hbox
  let gap := area (gerverSofa P) - (2.2 : ℝ)
  have hgap : 0 < gap := by
    have harea := (gerverSofa_area_mem hP hbox).1
    dsimp [gap]
    linarith
  let ε₀ := min εR gap
  refine ⟨C, Carea, ε₀, hC, hCarea, lt_min hεR hgap, ?_⟩
  intro S hS hε
  have h22 : (2.2 : ℝ) ≤ area S := by
    have he := hε.trans_le (min_le_right εR gap)
    dsimp [sofaDeficit, gap] at he
    linarith
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hω' : ω ∈ Icc (arccos (5 / 11 : ℝ)) (π / 2) := by
    have h : (1 / 2.2 : ℝ) = 5 / 11 := by norm_num
    simpa only [arcsec22, h] using hω
  have he := hresult S ω hSω hω' (hε.trans_le (min_le_left _ _))
  exact ⟨he.1, he.2.1⟩

/-- The missing terminal angle is controlled linearly in the original area deficit. -/
theorem terminal_angle_stability {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P := by
  obtain ⟨C, Carea, Cangle, ε₀, hC, hCarea, hCangle, hε₀, hresult⟩ := reduced_sofa_stability hP hbox
  exact ⟨Cangle, ε₀, hCangle, hε₀, fun S ω hS hω hε => (hresult S ω hS hω hε).2.2⟩

end MovingSofaStability
