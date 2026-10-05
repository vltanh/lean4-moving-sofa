module

public import MovingSofaUniqueness.Optimality
public import MovingSofaUniqueness.RegularClosed

/-!
# The parallel maximizer-first route: optimality and exact-set uniqueness

This is the entry point for the alternative route. It neither imports nor changes the
original `MovingSofaUniqueness.Main`; the original Challenge/Solution path is left intact.

`Maximizers` derives geometry, value, and cap rigidity from actual maximality. `Optimality`
then proves the global bound. This module uses that new bound to follow a given equality-case
sofa through its own monotone envelopes, and recovers the set by regular closedness.
The local assembly repeats these short containment steps intentionally: calling the original
uniqueness theorem would reintroduce its dependence on Baek's final optimality theorem.
The substantial selection, variation, curvature, Mamikon, and regular-closedness proofs are shared.

All declarations are in `MovingSofaUniqueness.MaximizerRoute`. In particular the final
`gerver_sofa_optimal_and_unique` and `volume_eq_gerver_iff` refer to the parallel proofs, not
aliases of the original final theorems. The original entry point may coexist in a client's
import environment; that is distinct from a proof dependency.

Status: uncompiled source. No compilation, CI, or proof-dependency audit was run in this work.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- The own cap of an equality-case monotone sofa is maximizing, by the new all-angle cap
bound. This is downstream of the alternative proof of optimality. -/
theorem own_cap_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) :
    ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω (capOf S ω) := by
  have hvalue : sofaArea ω (capOf S ω) = area (gerverSofa P) :=
    (theorem2_5_10 hS).trans heq
  intro C hC
  exact (MaximizerRoute.cap_area_le_gerver hP hbox hC).trans_eq hvalue.symm

/-- Monotonizing the specified equality-case sofa preserves its area and contains a translate
of it. It is not replaced by the unrelated maximizer used as a numerical comparator. -/
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
  have hupper := MaximizerRoute.area_le_gerver hP hbox ⟨ω, hTm.1⟩
  rw [Rigid.area_image, heq] at hlower
  exact ⟨v, T, hmono, hTm.2.2, le_antisymm hupper hlower⟩

/-- The new maximizer rigidity identifies a right-angle monotone equality-case sofa. -/
theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  obtain ⟨a, -, ha⟩ := right_angle_maximizer_eq_gerver hP hbox hcap
    (own_cap_maximizes hP hbox hT heq)
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- A rigid image of the given equality-case sofa lies in Gerver's sofa. Both numerical
upper comparisons use the parallel optimality proof. -/
theorem maximizer_contained_in_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S ⊆ gerverSofa P := by
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
  refine ⟨g.trans (Rigid.translate (-b, 0)), ?_⟩
  rw [Rigid.trans_image]
  rintro _ ⟨q, hq, rfl⟩
  have hqU := hSU hq
  rw [hUG] at hqU
  obtain ⟨r, hr, rfl⟩ := hqU
  have hcancel : r + (b, 0) + (-b, 0) = r := by ext <;> simp
  simpa [hcancel] using hr

/-- Exact set uniqueness along the alternative route; the original final uniqueness theorem
is not used. Equal areas suffice here because containment and regular closedness are proved. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-- Among moving sofas, equality in the new bound is equivalent to rigid congruence with
Gerver's sofa, as an equality of sets. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  constructor
  · exact image_eq_gerver_of_volume_eq hP hbox hS
  · rintro ⟨g, hg⟩
    calc
      volume S = volume (g '' S) := (g.volume_image S).symm
      _ = volume (gerverSofa P) := congrArg volume hg

/-- The alternative proof's feasibility, global bound, and exact-set equality characterization. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) := by
  have hopt := MaximizerRoute.gerver_sofa_optimal hP hbox
  exact ⟨hopt.1, hopt.2, fun _ hS => volume_eq_gerver_iff hP hbox hS⟩

/-- Global maximizers are exactly the moving sofas rigidly congruent to Gerver's sofa. -/
theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨hG, hle⟩ := MaximizerRoute.gerver_sofa_optimal hP hbox
  constructor
  · intro hmax
    exact image_eq_gerver_of_volume_eq hP hbox hS (le_antisymm (hle S hS) (hmax _ hG))
  · rintro ⟨g, hg⟩ S' hS'
    rw [← g.volume_image S, hg]
    exact hle S' hS'

end MovingSofaUniqueness.MaximizerRoute
