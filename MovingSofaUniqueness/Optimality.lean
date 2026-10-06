module

public import MovingSofaUniqueness.Maximizers

/-!
# A second proof of Baek's optimality theorem

`thm:unified-optimality` of the manuscript `docs/paper`, in the form of its `rem:second`, from the
maximizing caps of `MovingSofaUniqueness.Maximizers`, without Baek's Theorem 1.1.1. A maximizing
right-angle cap exists and has sofa area `|G|`, so every right-angle cap has sofa area at most
`|G|`, and the maximizing caps are the horizontal translates of Gerver's cap
(`right_angle_optimality_and_rigidity`). Every moving sofa with rotation angle `π/2` has area at
most that of the monotone sofa of a maximizing cap, which is `|G|` (`right_angle_area_le_gerver`). A
moving sofa `S` of area at least `11/5` has a rotation angle `ω ∈ [arcsec(11/5), π/2]`; its area is
at most that of the monotone sofa `S_ω` of a maximizing cap with angle `ω`, and a rotated copy of
`S_ω` moves with the rotation angle `π/2`, so `|S| ≤ |S_ω| ≤ |G|` (`area_le_gerver_of_large`).
Smaller sofas have area less than `|G| ≥ 2.2192`. The bound for caps of every rotation angle comes
last (`cap_area_le_gerver`).

The module does not import `MovingSofaUniqueness.Main`; `scripts/AuditMaximizerRoute.lean` checks
that its proofs use neither Baek's Theorem 1.1.1 nor the results by which Baek derives the
right-angle motion and the injectivity condition of Baek's cap from its balance.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper` (`rem:second`), the bound: every
right-angle cap has sofa area at most `|G|`, the sofa area of a maximizing right-angle cap
(`fact:exists`, `rem:second`). -/
theorem right_angle_cap_area_le_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : Set Plane} (hC : IsCap C (π / 2)) :
    sofaArea (π / 2) C ≤ area (gerverSofa P) := by
  obtain ⟨K, hK, _, _, hmax, _⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
  exact (hmax C hC).trans_eq (right_angle_maximizer_value hP hbox hK hmax)

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper` (`rem:second`): the maximizing
right-angle caps are the horizontal translates of Gerver's cap. -/
theorem right_angle_maximizes_iff_translate_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    (∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) ↔
      ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap := by
  constructor
  · intro hmax
    obtain ⟨a, hcap, -⟩ := right_angle_maximizer_eq_gerver hP hbox hK hmax
    exact ⟨a, hcap⟩
  · rintro ⟨a, rfl⟩ C hC
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox),
      GerverParams.gm_sofaArea_cap hP hbox]
    exact right_angle_cap_area_le_gerver hP hbox hC

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper` (`rem:second`): a right-angle cap
has sofa area `|G|` if and only if it is a horizontal translate of Gerver's cap. -/
theorem right_angle_sofaArea_eq_gerver_iff {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    sofaArea (π / 2) K = area (gerverSofa P) ↔
      ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap := by
  constructor
  · intro heq
    apply (right_angle_maximizes_iff_translate_gerver hP hbox hK).1
    intro C hC
    exact (right_angle_cap_area_le_gerver hP hbox hC).trans_eq heq.symm
  · rintro ⟨a, rfl⟩
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox)]
    exact GerverParams.gm_sofaArea_cap hP hbox

/-- `thm:unified-optimality` (a) of the manuscript `docs/paper` (`rem:second`), in one statement:
the bound for right-angle caps and its equality case. -/
theorem right_angle_optimality_and_rigidity {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ K, IsCap K (π / 2) → sofaArea (π / 2) K ≤ area (gerverSofa P)) ∧
      (∀ K, IsCap K (π / 2) →
        (sofaArea (π / 2) K = area (gerverSofa P) ↔
          ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap)) :=
  ⟨fun _ hK => right_angle_cap_area_le_gerver hP hbox hK,
    fun _ hK => right_angle_sofaArea_eq_gerver_iff hP hbox hK⟩

/-- `thm:unified-optimality` (b) of the manuscript `docs/paper` (`rem:second`), the rotation angle
`π/2`: a moving sofa with rotation angle `π/2` has area at most that of the monotone sofa of a
maximizing cap, which is `|G|`. -/
theorem right_angle_area_le_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : IsMovingSofaWithAngle S (π / 2)) : area S ≤ area (gerverSofa P) := by
  obtain ⟨K, hK, hmono, hcap, hmax, hle⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
  have hA : sofaArea (π / 2) K = area (K \ niche K (π / 2)) := by
    have h := theorem2_5_10 hmono
    rwa [hcap] at h
  calc
    area S ≤ area (K \ niche K (π / 2)) := hle S hS
    _ = sofaArea (π / 2) K := hA.symm
    _ = area (gerverSofa P) := right_angle_maximizer_value hP hbox hK hmax

/-- `thm:unified-optimality` (b) of the manuscript `docs/paper` (`rem:second`), a sofa of area at
least `11/5`: with its rotation angle `ω`, `|S| ≤ |S_ω| = |R_{π/2-ω} S_ω| ≤ |G|`, where `S_ω` is the
monotone sofa of a maximizing cap (`fact:exists`) and its rotated copy moves with the rotation angle
`π/2` (`lem:right-motion`). -/
theorem area_le_gerver_of_large {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (h22 : (2.2 : ℝ) ≤ area S) : area S ≤ area (gerverSofa P) := by
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨K, _, hmono, hcap, hmax, hle⟩ := exists_maximizing_cap hωpos
  have hT22 : (2.2 : ℝ) ≤ area (K \ niche K ω) := h22.trans (hle S hSω)
  have hown : ∀ C, IsCap C ω →
      sofaArea ω C ≤ sofaArea ω (capOf (K \ niche K ω) ω) := by
    rw [hcap]
    exact hmax
  have hrot := maximizing_monotone_has_right_angle hmono hω hT22 hown
  calc
    area S ≤ area (K \ niche K ω) := hle S hSω
    _ = area (rot (π / 2 - ω) '' (K \ niche K ω)) :=
      (area_image_rot (π / 2 - ω) (K \ niche K ω)).symm
    _ ≤ area (gerverSofa P) := right_angle_area_le_gerver hP hbox hrot

/-- `thm:unified-optimality` (b) of the manuscript `docs/paper` (`rem:second`): every moving sofa
has area at most `|G|`. -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  by_cases h22 : (2.2 : ℝ) ≤ area S
  · exact area_le_gerver_of_large hP hbox hS h22
  · have hG := gerverSofa_area hP hbox
    have hsmall := lt_of_not_ge h22
    linarith

/-- `area_le_gerver`, for the measures: both are finite. -/
theorem volume_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ volume (gerverSofa P) := by
  have hSfin : volume S ≠ ⊤ := (isBounded_of_isMovingSofa hS).measure_lt_top.ne
  have hGfin : volume (gerverSofa P) ≠ ⊤ := gerverSofa_volume_ne_top hP hbox
  rw [← ENNReal.toReal_le_toReal hSfin hGfin]
  exact area_le_gerver hP hbox hS

/-- `thm:unified-optimality` (b) of the manuscript `docs/paper` (`rem:second`): Gerver's sofa is a
moving sofa, and every moving sofa has area at most that of Gerver's sofa. This is the statement of
Baek's Theorem 1.1.1, proved without it. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  ⟨⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩,
    fun _ hS => volume_le_gerver hP hbox hS⟩

/-- `thm:unified-optimality` (c) of the manuscript `docs/paper` (`rem:second`): every cap of every
rotation angle `ω` has sofa area at most `|G|`, as `𝒜_ω(C) ≤ 𝒜_ω(K) = |K \ 𝒩(K)| ≤ |G|` for the
maximizing cap `K` of `fact:exists`. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {C : Set Plane} {ω : ℝ} (hC : IsCap C ω) :
    sofaArea ω C ≤ area (gerverSofa P) := by
  obtain ⟨K, _, hmono, hcap, hmax, _⟩ := exists_maximizing_cap hC.1
  have hA : sofaArea ω K = area (K \ niche K ω) := by
    have h := theorem2_5_10 hmono
    rwa [hcap] at h
  calc
    sofaArea ω C ≤ sofaArea ω K := hmax C hC
    _ = area (K \ niche K ω) := hA
    _ ≤ area (gerverSofa P) := area_le_gerver hP hbox ⟨ω, hmono.isMovingSofaWithAngle⟩

end MovingSofaUniqueness.MaximizerRoute
