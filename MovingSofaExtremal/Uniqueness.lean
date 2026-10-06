module

public import MovingSofaExtremal.Optimality
public import MovingSofaUniqueness.RegularClosed

/-!
# Global uniqueness through zero-deficit cap coercivity

Uncompiled proof source. The global envelope/recovery steps are shared
mathematics, but the cap classification comes from the quantitative distance
estimate. The module imports neither the old uniqueness entry point nor the
old maximizer-route classification. It does not use global stability.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

theorem own_cap_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : MaximizesCap ω (capOf S ω) := by
  have hvalue : sofaArea ω (capOf S ω) = area (gerverSofa P) := (theorem2_5_10 hS).trans heq
  intro C hC
  exact (MovingSofaExtremal.cap_area_le_gerver hP hbox hC).trans_eq hvalue.symm

theorem equal_area_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (heq : area S = area (gerverSofa P)) :
    ∃ (v : Plane) (T : Set Plane), IsMonotoneSofa T ω ∧
      Rigid.translate v '' S ⊆ T ∧ area T = area (gerverSofa P) := by
  obtain ⟨v, hstd⟩ := proposition2_3_1_exists hω hS
  have hSm := mpc_isMovingSofaWithAngle_translate hS v
  rw [← Rigid.coe_translate v] at hstd hSm
  let T := monotonization (Rigid.translate v '' S) ω
  have hTm := theorem2_3_2 hω hSm hstd
  have hmono : IsMonotoneSofa T ω := ⟨hω, _, hSm, hstd, rfl⟩
  have hfinite : volume T ≠ ⊤ := (isBounded_of_isMovingSofa ⟨ω, hTm.1⟩).measure_lt_top.ne
  have hlower : area (Rigid.translate v '' S) ≤ area T :=
    ENNReal.toReal_mono hfinite (measure_mono hTm.2.2)
  have hupper := MovingSofaExtremal.area_le_gerver hP hbox ⟨ω, hTm.1⟩
  rw [Rigid.area_image, heq] at hlower
  exact ⟨v, T, hmono, hTm.2.2, le_antisymm hupper hlower⟩

theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  obtain ⟨a, _, ha⟩ := right_angle_maximizer_eq_gerver hP hbox hcap
    (own_cap_maximizes hP hbox hT heq)
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- The angle bound is retained for the optional translation-only refinement. -/
theorem maximizer_contained_in_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g.angle ∈ Icc 0 (π / 2 - arcsec22) ∧ g '' S ⊆ gerverSofa P := by
  have harea : area S = area (gerverSofa P) := congrArg ENNReal.toReal heq
  have h22 : (2.2 : ℝ) ≤ area S := harea ▸ gerverSofa_area hP hbox
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨v₀, T, hT, hST, hTarea⟩ := equal_area_envelope hP hbox hωpos hSω harea
  have hT22 : (2.2 : ℝ) ≤ area T := hTarea ▸ gerverSofa_area hP hbox
  have hrot := maximizing_monotone_has_right_angle hT hω hT22
    (own_cap_maximizes hP hbox hT hTarea)
  obtain ⟨v₁, U, hU, hTU, hUarea⟩ :=
    equal_area_envelope hP hbox pi_div_two_mem_Ioc hrot (by rw [area_image_rot, hTarea])
  obtain ⟨b, hUG⟩ := right_angle_monotone_eq_gerver hP hbox hU hUarea
  let g := ((Rigid.translate v₀).trans (Rigid.rotate (π / 2 - ω))).trans (Rigid.translate v₁)
  have hSU : g '' S ⊆ U := by
    simp only [g, Rigid.trans_image, Rigid.coe_rotate]
    exact (image_mono (image_mono hST)).trans hTU
  refine ⟨g.trans (Rigid.translate (-b, 0)), ?_, ?_⟩
  · change 0 ≤ (g.trans (Rigid.translate (-b, 0))).angle ∧
      (g.trans (Rigid.translate (-b, 0))).angle ≤ π / 2 - arcsec22
    simp only [g, Rigid.trans, Rigid.translate, Rigid.rotate, zero_add, add_zero]
    constructor <;> linarith [hω.1, hω.2]
  · rw [Rigid.trans_image]
    rintro _ ⟨q, hq, rfl⟩
    have hqU := hSU hq
    rw [hUG] at hqU
    obtain ⟨r, hr, rfl⟩ := hqU
    have hcancel : r + (b, 0) + (-b, 0) = r := by ext <;> simp
    simpa [hcancel] using hr

/-- Actual-set equality, not equality almost everywhere. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, _, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  constructor
  · exact image_eq_gerver_of_volume_eq hP hbox hS
  · rintro ⟨g, hg⟩
    calc
      volume S = volume (g '' S) := (g.volume_image S).symm
      _ = volume (gerverSofa P) := congrArg volume hg

/-- The common-framework extremal theorem, coexisting with both older routes. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) := by
  have hopt := MovingSofaExtremal.gerver_sofa_optimal hP hbox
  exact ⟨hopt.1, hopt.2, fun _ hS => volume_eq_gerver_iff hP hbox hS⟩

theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨hG, hle⟩ := MovingSofaExtremal.gerver_sofa_optimal hP hbox
  constructor
  · intro hmax
    exact image_eq_gerver_of_volume_eq hP hbox hS (le_antisymm (hle S hS) (hmax _ hG))
  · rintro ⟨g, hg⟩ S' hS'
    rw [← g.volume_image S, hg]
    exact hle S' hS'

end MovingSofaExtremal
