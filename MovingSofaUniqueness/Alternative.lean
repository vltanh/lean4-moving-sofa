module

public import MovingSofaUniqueness.Optimality
public import MovingSofaUniqueness.RegularClosed

/-!
# The uniqueness theorem from the second proof of optimality

The proof of the uniqueness theorem (`thm:main` of the manuscript `docs/paper`) and of `cor:all`,
with the optimality of `MovingSofaUniqueness.Optimality` in place of Baek's Theorem 1.1.1, as
`rem:second` of the manuscript says. The steps are those of `MovingSofaUniqueness.Main`: a translate
of the sofa lies in its monotonization, of the same area, whose cap is maximizing
(`equal_area_envelope`, `own_cap_maximizes`; `prop:reduction`); a rotated copy of that sofa moves
with the rotation angle `π/2` (`lem:right-motion`), and its monotonization is a horizontal translate
of Gerver's sofa (`right_angle_monotone_eq_gerver`; `thm:caps`); and Gerver's sofa is the closure of
its interior (`gerver_regularClosed`). The short assembly is repeated here, so that this module does
not import `MovingSofaUniqueness.Main`, whose results use Baek's theorem.

The declarations are in the namespace `MovingSofaUniqueness.MaximizerRoute`;
`MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq` is the second proof of
`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`. `scripts/AuditMaximizerRoute.lean` checks that
no declaration of the three modules of the second proof uses Baek's Theorem 1.1.1.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- The cap of a monotone sofa of Gerver's area is maximizing, by `thm:unified-optimality` (c) of
the manuscript `docs/paper` (`rem:second`). -/
theorem own_cap_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) :
    ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω (capOf S ω) := by
  have hvalue : sofaArea ω (capOf S ω) = area (gerverSofa P) :=
    (theorem2_5_10 hS).trans heq
  intro C hC
  exact (MaximizerRoute.cap_area_le_gerver hP hbox hC).trans_eq hvalue.symm

/-- `prop:reduction` of the manuscript `docs/paper`, with `thm:unified-optimality` (b) as the bound
(`rem:second`): a translate of a moving sofa of Gerver's area lies in its monotonization, a monotone
sofa of the same area. -/
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

/-- The last statement of `thm:caps` of the manuscript `docs/paper`, from `rem:second`: a
right-angle monotone sofa of Gerver's area is a horizontal translate of Gerver's sofa. -/
theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  obtain ⟨a, -, ha⟩ := right_angle_maximizer_eq_gerver hP hbox hcap
    (own_cap_maximizes hP hbox hT heq)
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- A rigid image of a moving sofa of Gerver's area lies in Gerver's sofa (`eq:contained` and
`thm:caps` of the manuscript `docs/paper`), with the bound of `rem:second`. -/
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

/-- **The uniqueness of Gerver's sofa** (`thm:main` of the manuscript `docs/paper`), from the
second proof of optimality: a rotation about the origin followed by a translation maps every moving
sofa with the area of Gerver's sofa onto Gerver's sofa. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-- A moving sofa has the area of Gerver's sofa if and only if a rigid map takes it onto Gerver's
sofa. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  constructor
  · exact image_eq_gerver_of_volume_eq hP hbox hS
  · rintro ⟨g, hg⟩
    calc
      volume S = volume (g '' S) := (g.volume_image S).symm
      _ = volume (gerverSofa P) := congrArg volume hg

/-- Gerver's sofa is a moving sofa, every moving sofa has area at most that of Gerver's sofa, and
equality holds exactly for the rigid images of Gerver's sofa: `thm:unified-optimality` (b) and
`thm:main` of the manuscript `docs/paper`, from the second proof (`rem:second`). -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) := by
  have hopt := MaximizerRoute.gerver_sofa_optimal hP hbox
  exact ⟨hopt.1, hopt.2, fun _ hS => volume_eq_gerver_iff hP hbox hS⟩

/-- `cor:all` of the manuscript `docs/paper`, from the second proof: a moving sofa has maximal
area if and only if a rigid map takes it onto Gerver's sofa. -/
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
