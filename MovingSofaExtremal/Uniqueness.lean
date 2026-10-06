module

public import MovingSofaExtremal.Optimality
public import MovingSofaUniqueness.RegularClosed

/-!
# Uniqueness through the coercive certificate

A moving sofa `S` with the area of Gerver's sofa `G` moves with an angle `ω ≥ arcsec 2.2`
(Baek's Theorem 1.5.1). Its monotonization `T` has area `|G|` by the optimality theorem of this
route, so the cap of `T` maximizes the sofa area at the angle `ω` (`own_cap_maximizes`). A rotated
copy of `T` moves with the right angle (`maximizing_monotone_has_right_angle`); its
monotonization `U` is a right-angle monotone sofa of area `|G|`, so its cap is a horizontal
translate of Gerver's cap (`right_angle_maximizer_eq_gerver`), and `U` is the same translate of
`G` (`right_angle_monotone_eq_gerver`). A rigid image of `S` thus lies in `G` and has the same
area; as `G` is regular closed, it is `G` (`image_eq_gerver_of_volume_eq`). The rigid map turns
by an angle in `[0, π/2 - arcsec 2.2]`, and `G` is wider than one in every such direction other
than the vertical, so the map is a translation (`translate_eq_gerver_of_volume_eq`).

These steps are those of `MovingSofaUniqueness.Main`; only the classification of the maximizing
right-angle caps differs. The module imports neither that module nor the stability theorem.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

/-- The cap of a monotone sofa of area `|G|` maximizes the sofa area at its angle. -/
theorem own_cap_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : MaximizesCap ω (capOf S ω) := by
  have hvalue : sofaArea ω (capOf S ω) = area (gerverSofa P) := (theorem2_5_10 hS).trans heq
  intro C hC
  exact (MovingSofaExtremal.cap_area_le_gerver hP hbox hC).trans_eq hvalue.symm

/-- A moving sofa of area `|G|` with angle `ω` has a translate inside a monotone sofa of angle `ω`
and area `|G|`, its monotonization. -/
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

/-- A right-angle monotone sofa of area `|G|` is a horizontal translate of `G`. -/
theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  obtain ⟨a, _, ha⟩ := right_angle_maximizer_eq_gerver hP hbox hcap
    (own_cap_maximizes hP hbox hT heq)
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- A rigid map that turns by an angle in `[0, π/2 - arcsec 2.2]` takes a moving sofa of area
`|G|` into `G`. -/
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

/-- **Uniqueness.** A rotation about the origin followed by a translation maps every moving sofa
with the area of Gerver's sofa onto Gerver's sofa. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, _, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-- **No rotation is needed.** Every moving sofa with the area of Gerver's sofa is a translate of
Gerver's sofa. The rigid map `g` of `maximizer_contained_in_gerver` maps `S` onto `G` and turns by
`ψ ∈ [0, π/2 - arcsec 2.2]`. As `S` lies in a horizontal strip of height one, `G = g(S)` has width
at most one in the direction `u_{π/2 + ψ}`, while the width of `G` exceeds one in every direction
`u_r`, `r ∈ (π/2, π]` (`gerver_width_gt_one`); so `ψ = 0`. -/
theorem translate_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ v : Plane, Rigid.translate v '' S = gerverSofa P := by
  obtain ⟨g, hψ, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  have hg : g '' S = gerverSofa P :=
    g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
      (gerverSofa_volume_ne_top hP hbox) heq
  have hwidth : ∀ x ∈ gerverSofa P, ∀ y ∈ gerverSofa P,
      dot (x - y) (uvec (g.angle + π / 2)) ≤ 1 := by
    intro x hx y hy
    rw [← hg] at hx hy
    rw [uvec_add_pi_div_two]
    exact dot_sub_vvec_le_one_of_mem_image hS g hx hy
  have hψ0 : g.angle = 0 := by
    by_contra hne
    have hpos : 0 < g.angle := lt_of_le_of_ne hψ.1 (Ne.symm hne)
    have hr : g.angle + π / 2 ∈ Icc 0 π :=
      ⟨by linarith [pi_pos], by linarith [hψ.2, ang_arcsec22_pos]⟩
    obtain ⟨p, hp, q, hq, hlt⟩ := gerver_width_gt_one hP hbox hr (by intro h; linarith)
    linarith [hwidth p hp q hq]
  refine ⟨g.shift, ?_⟩
  rw [← Rigid.eq_translate_of_angle_eq_zero hψ0]
  exact hg

/-- A moving sofa has the area of Gerver's sofa if and only if a rigid map takes it onto `G`. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  constructor
  · exact image_eq_gerver_of_volume_eq hP hbox hS
  · rintro ⟨g, hg⟩
    calc
      volume S = volume (g '' S) := (g.volume_image S).symm
      _ = volume (gerverSofa P) := congrArg volume hg

/-- **Optimality and uniqueness.** Gerver's sofa is a moving sofa, every moving sofa has at most
its area, and the moving sofas with its area are its rigid images. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) := by
  have hopt := MovingSofaExtremal.gerver_sofa_optimal hP hbox
  exact ⟨hopt.1, hopt.2, fun _ hS => volume_eq_gerver_iff hP hbox hS⟩

/-- A moving sofa has the maximal area if and only if a rigid map takes it onto `G`. -/
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
