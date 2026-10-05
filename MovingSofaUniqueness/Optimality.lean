module

public import MovingSofaUniqueness.Maximizers

/-!
# Optimality from the maximizer principles

The global bound is derived here, before equality with Gerver's area is used to infer
maximality. This is an alternative assembly from Baek's intermediate machinery and the
uniqueness development's maximizer principles, not a replacement for the formalization of
Baek's proof. In particular, `MovingSofaOptimality/` is left unchanged.

The first bound is for right-angle caps. Existence of a maximizing cap and the maximizer-value
theorem suffice. For a large arbitrary sofa, choose a fixed-angle maximizer, use the pinned
bounds to give that sofa a right-angle motion, and apply the right-angle bound. Small sofas
are below Gerver by the explicit lower bound for its area. The bound for all caps is deduced
last, using fixed-angle existence and maximality.

No theorem of `MovingSofaUniqueness.Main` is imported. No use is made of Baek's final
`theorem1_1_1` or `gm_area_le`. See `docs/maximizer-first/README.md` for the distinction between
source-level inspection and a future transitive proof-dependency audit.

Status: this new assembly has not been compiled or kernel-audited in this refactor.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- The right-angle cap bound, derived from existence and the value of any maximizer. -/
theorem right_angle_cap_area_le_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {C : Set Plane} (hC : IsCap C (π / 2)) :
    sofaArea (π / 2) C ≤ area (gerverSofa P) := by
  obtain ⟨K, hK, _, _, hmax, _⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
  exact (hmax C hC).trans_eq (right_angle_maximizer_value hP hbox hK hmax)

/-- All moving sofas with a right-angle motion satisfy the bound. The selected maximizing
sofa is only a numerical comparator; no containment of the original sofa in it is asserted. -/
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

/-- The large-sofa case. The fixed-angle maximizer has area at least that of `S`, so its
pinned bounds give a right-angle motion without assuming the value of the global maximum. -/
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

/-- The global real-valued area bound, proved without Baek's final optimality theorem. -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  by_cases h22 : (2.2 : ℝ) ≤ area S
  · exact area_le_gerver_of_large hP hbox hS h22
  · have hG := gerverSofa_area hP hbox
    have hsmall := lt_of_not_ge h22
    linarith

/-- The measure-valued bound. Both measures are finite before passing between volume and
its real value; no inequality is inferred from `toReal` for an infinite measure. -/
theorem volume_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ volume (gerverSofa P) := by
  have hSfin : volume S ≠ ⊤ := (isBounded_of_isMovingSofa hS).measure_lt_top.ne
  have hGfin : volume (gerverSofa P) ≠ ⊤ := gerverSofa_volume_ne_top hP hbox
  rw [← ENNReal.toReal_le_toReal hSfin hGfin]
  exact area_le_gerver hP hbox hS

/-- Gerver is feasible and optimal, by the maximizer-first route. Its feasibility comes
from the explicit Gerver motion, not from a conjunction containing the old optimality proof. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  ⟨⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩,
    fun _ hS => volume_le_gerver hP hbox hS⟩

/-- Only after global optimality has been proved do we bound the cap functional at every
angle, including caps whose niche need not be contained in the cap. -/
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
