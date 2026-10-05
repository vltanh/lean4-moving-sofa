module

public import MovingSofaUniqueness.Maximizers

/-!
# Optimality from the maximizer principles

This is a parallel proof, not a replacement for either original formalization.
`MovingSofaOptimality/`, `MovingSofaUniqueness.Main`, and `Solution` remain unchanged.
The global bound is derived here before equality with Gerver's area is used to infer maximality.

First, fixed-angle existence and the value of every right-angle maximizer give the bound for
all right-angle caps. Mamikon rigidity classifies the maximizing caps and the equality cases.
For a large arbitrary sofa, choose a fixed-angle maximizer, use the pinned bounds to give that
sofa a right-angle motion, and apply the right-angle bound. Small sofas are below Gerver by the
explicit lower bound for its area. The all-angle cap bound is deduced last.

This module does not import `MovingSofaUniqueness.Main`; its statements use the primitive
maximality predicate rather than the `IsMaxCap` definition owned by that original entry point.
No use is made of Baek's final `theorem1_1_1` or `gm_area_le`. Baek's intermediate machinery,
including the maximum of the quadratic functional, is retained. The separate audit script
`scripts/AuditMaximizerRoute.lean` is intended to check transitive proof dependencies later.

Status: this new assembly has not been compiled or kernel-audited in this work.
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

/-- The complete maximizer classification, using only the right-angle bound just proved.
The predicate is written out to avoid importing the original uniqueness entry point. -/
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

/-- The equality cases of the universal right-angle bound are the same translates. This
corollary does not assume the optimal value in order to prove the bound. -/
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

/-- A single statement of the right-angle inequality and its cap-rigidity equality case. -/
theorem right_angle_optimality_and_rigidity {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ K, IsCap K (π / 2) → sofaArea (π / 2) K ≤ area (gerverSofa P)) ∧
      (∀ K, IsCap K (π / 2) →
        (sofaArea (π / 2) K = area (gerverSofa P) ↔
          ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap)) :=
  ⟨fun _ hK => right_angle_cap_area_le_gerver hP hbox hK,
    fun _ hK => right_angle_sofaArea_eq_gerver_iff hP hbox hK⟩

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

/-- Both measures are finite before passing between volume and its real value. -/
theorem volume_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ volume (gerverSofa P) := by
  have hSfin : volume S ≠ ⊤ := (isBounded_of_isMovingSofa hS).measure_lt_top.ne
  have hGfin : volume (gerverSofa P) ≠ ⊤ := gerverSofa_volume_ne_top hP hbox
  rw [← ENNReal.toReal_le_toReal hSfin hGfin]
  exact area_le_gerver hP hbox hS

/-- Gerver is feasible and optimal by the parallel route. Feasibility comes directly from
the explicit motion, not from a conjunction containing Baek's final optimality proof. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  ⟨⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩,
    fun _ hS => volume_le_gerver hP hbox hS⟩

/-- Only after global optimality do we bound the cap functional at every angle, including
caps whose niche need not be contained in the cap. -/
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
