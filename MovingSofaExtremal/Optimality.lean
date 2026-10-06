module

public import MovingSofaExtremal.CoerciveRigidity

/-!
# Optimality through the coercive certificate

Every right-angle cap has sofa area at most `|G|` (`right_angle_cap_area_le_gerver`), because a
maximizing right-angle cap has sofa area `|G|` (`right_angle_maximizer_value`). A right-angle moving
sofa lies in the sofa of a maximizing cap (`right_angle_area_le_gerver`). A moving sofa of area at
least 2.2 moves with an angle `ω ≥ arcsec 2.2` (Baek's Theorem 1.5.1); it lies in the sofa of a
maximizing cap of angle `ω`, a rotated copy of which moves with the right angle
(`maximizing_monotone_has_right_angle`), so its area is at most `|G|` (`area_le_gerver`).

Baek's Theorem 1.1.1 is not used, nor are his results on balanced caps.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

theorem right_angle_cap_area_le_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : Set Plane} (hC : IsCap C (π / 2)) :
    sofaArea (π / 2) C ≤ area (gerverSofa P) :=
  (right_angle_extremal hP hbox).1 C hC

theorem right_angle_maximizes_iff_translate_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    MaximizesCap (π / 2) K ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap := by
  constructor
  · intro hmax
    obtain ⟨a, hcap, _⟩ := right_angle_maximizer_eq_gerver hP hbox hK hmax
    exact ⟨a, hcap⟩
  · rintro ⟨a, rfl⟩ C hC
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox),
      GerverParams.gm_sofaArea_cap hP hbox]
    exact right_angle_cap_area_le_gerver hP hbox hC

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

theorem area_le_gerver_of_large {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (h22 : (2.2 : ℝ) ≤ area S) : area S ≤ area (gerverSofa P) := by
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨K, _, hmono, hcap, hmax, hle⟩ := exists_maximizing_cap hωpos
  have hT22 : (2.2 : ℝ) ≤ area (K \ niche K ω) := h22.trans (hle S hSω)
  have hown : MaximizesCap ω (capOf (K \ niche K ω) ω) := by
    rw [hcap]
    exact hmax
  have hrot := maximizing_monotone_has_right_angle hmono hω hT22 hown
  calc
    area S ≤ area (K \ niche K ω) := hle S hSω
    _ = area (rot (π / 2 - ω) '' (K \ niche K ω)) :=
      (area_image_rot (π / 2 - ω) (K \ niche K ω)).symm
    _ ≤ area (gerverSofa P) := right_angle_area_le_gerver hP hbox hrot

theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  by_cases h22 : (2.2 : ℝ) ≤ area S
  · exact area_le_gerver_of_large hP hbox hS h22
  · have hG := gerverSofa_area hP hbox
    have hsmall := lt_of_not_ge h22
    linarith

theorem volume_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ volume (gerverSofa P) := by
  have hSfin : volume S ≠ ⊤ := (isBounded_of_isMovingSofa hS).measure_lt_top.ne
  have hGfin : volume (gerverSofa P) ≠ ⊤ := gerverSofa_volume_ne_top hP hbox
  rw [← ENNReal.toReal_le_toReal hSfin hGfin]
  exact area_le_gerver hP hbox hS

/-- The same optimality statement as Baek's final theorem, through the new certificate. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  ⟨⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩, fun _ hS => volume_le_gerver hP hbox hS⟩

theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {C : Set Plane} {ω : ℝ} (hC : IsCap C ω) : sofaArea ω C ≤ area (gerverSofa P) := by
  obtain ⟨K, _, hmono, hcap, hmax, _⟩ := exists_maximizing_cap hC.1
  have hA : sofaArea ω K = area (K \ niche K ω) := by
    have h := theorem2_5_10 hmono
    rwa [hcap] at h
  calc
    sofaArea ω C ≤ sofaArea ω K := hmax C hC
    _ = area (K \ niche K ω) := hA
    _ ≤ area (gerverSofa P) := area_le_gerver hP hbox ⟨ω, hmono.isMovingSofaWithAngle⟩

end MovingSofaExtremal
