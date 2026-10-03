module

public import MovingSofaUniqueness.Reductions

/-!
# Assemble shape uniqueness in the paper coordinates

Both monotonizations apply to the actual starting set. Balanced-maximizer
existence supplies only the global numerical bound in `cap_area_le_gerver`.
The positive-area premise needed for the pinned selection is proved from
Gerver's established lower bound, not added to the final theorem.

The historical `Draft` namespace is retained for compatibility with the
formal-conjectures adapter, which imports this module.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-- Global maximality in the paper presentation, in exact ENNReal volume. -/
def IsGlobalMax (S : Set Plane) : Prop :=
  MovingSofaOptimality.IsMovingSofa S ∧
    ∀ T, MovingSofaOptimality.IsMovingSofa T → volume T ≤ volume S

private theorem coe_translate (v : Plane) :
    (Rigid.translate v : Plane → Plane) = fun p => p + v := by
  funext p
  exact Rigid.translate_apply v p

private theorem coe_rotate (a : ℝ) :
    (Rigid.rotate a : Plane → Plane) = rot a := by
  funext p
  exact Rigid.rotate_apply a p

theorem standard_of_monotone {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsStandardPosition S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).2.1

/-- Translate the specified sofa, then take its own monotonization. -/
theorem maximal_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
    (hS : IsMovingSofaWithAngle S ω) (heq : area S = area (gerverSofa P)) :
    ∃ (v : Plane) (T : Set Plane), IsMonotoneSofa T ω ∧
      Rigid.translate v '' S ⊆ T ∧ area T = area (gerverSofa P) := by
  obtain ⟨v, hstd⟩ := proposition2_3_1_exists hω hS
  have hSm := mpc_isMovingSofaWithAngle_translate hS v
  rw [← coe_translate v] at hstd hSm
  let T := monotonization (Rigid.translate v '' S) ω
  have hTm := theorem2_3_2 hω hSm hstd
  have hmono : IsMonotoneSofa T ω := ⟨hω, _, hSm, hstd, rfl⟩
  have hfinite : volume T ≠ ⊤ := (isBounded_of_isMovingSofa ⟨ω, hTm.1⟩).measure_lt_top.ne
  have hlower : area (Rigid.translate v '' S) ≤ area T :=
    ENNReal.toReal_mono hfinite (measure_mono hTm.2.2)
  have hupper := area_le_gerver hP hbox ⟨ω, hTm.1⟩
  rw [Rigid.area_image, heq] at hlower
  exact ⟨v, T, hmono, hTm.2.2, le_antisymm hupper hlower⟩

/-- The own cap of a monotone sofa of Gerver's area maximizes cap area. -/
theorem own_cap_isMax {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : IsMaxCap ω (capOf S ω) := by
  apply isMaxCap_of_area_eq hP hbox
    (theorem2_4_1 hS.1 (moving_of_monotone hS) (standard_of_monotone hS))
  rw [theorem2_5_10 hS]
  exact heq

/-- The right-angle case needs no extension. In the smaller-angle case the
new pinned estimates apply to this same positive-area cap. -/
theorem maximal_monotone_has_right_angle {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (heq : area S = area (gerverSofa P)) :
    ∃ a : ℝ, IsMovingSofaWithAngle (rot a '' S) (π / 2) := by
  rcases eq_or_lt_of_le hω.2 with hright | hsmall
  · refine ⟨0, ?_⟩
    simpa [rot_zero, hright] using moving_of_monotone hS
  · have hmax := own_cap_isMax hP hbox hS heq
    have hpositive : 0 < sofaArea ω (capOf S ω) := by
      rw [theorem2_5_10 hS, heq]
      have hG := gerverSofa_area hP hbox
      linarith
    have hpin := pinnedBounds_of_isMaxCap ⟨hS.1.1, hsmall⟩ hmax hpositive
    apply right_angle_motion_of_pinned hS ⟨hω.1, hsmall⟩ _ hpin
    rw [heq]
    exact gerverSofa_area hP hbox

/-- A maximal right-angle monotone sofa is an actual translate of Gerver's sofa. -/
theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 (moving_of_monotone hT) (standard_of_monotone hT)
  have hvalue : sofaArea (π / 2) (capOf T (π / 2)) = area (gerverSofa P) := by
    rw [theorem2_5_10 hT]
    exact heq
  obtain ⟨a, ha⟩ := ki_sofa_eq_gerver_translate hP hbox
    (isKi_of_maximal_area hP hbox hcap hvalue) hvalue
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- Keep the full containment chain before applying regular-closedness. -/
theorem maximizer_contained_in_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S ⊆ gerverSofa P := by
  have harea : area S = area (gerverSofa P) := congrArg ENNReal.toReal heq
  have h22 : (2.2 : ℝ) ≤ area S := by rw [harea]; exact gerverSofa_area hP hbox
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨gm_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨v₀, T, hT, hST, hTarea⟩ := maximal_envelope hP hbox hωpos hSω harea
  obtain ⟨a, hrot⟩ := maximal_monotone_has_right_angle hP hbox hT hω hTarea
  have hrotArea : area (rot a '' T) = area (gerverSofa P) := by
    rw [gm_area_rot, hTarea]
  obtain ⟨v₁, U, hU, hTU, hUarea⟩ :=
    maximal_envelope hP hbox pi_div_two_mem_Ioc hrot hrotArea
  obtain ⟨b, hUG⟩ := right_angle_monotone_eq_gerver hP hbox hU hUarea
  let g₀ := (Rigid.translate v₀).trans (Rigid.rotate a)
  let g₁ := g₀.trans (Rigid.translate v₁)
  have hSU : g₁ '' S ⊆ U := by
    rw [show g₁ = ((Rigid.translate v₀).trans (Rigid.rotate a)).trans
      (Rigid.translate v₁) from rfl, Rigid.trans_image, Rigid.trans_image, coe_rotate]
    exact (Set.image_mono (Set.image_mono hST)).trans hTU
  let unshift := Rigid.translate (-b, 0)
  refine ⟨g₁.trans unshift, ?_⟩
  rw [Rigid.trans_image]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hqU := hSU hq
  rw [hUG] at hqU
  obtain ⟨r, hr, rfl⟩ := hqU
  have hcancel : r + (b, 0) + (-b, 0) = r := by
    ext <;> simp
  simp only [unshift, Rigid.translate_apply]
  rw [hcancel]
  exact hr

/-- Recover the original closed set, not only its area or its monotone envelope. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  have hclosed : IsClosed S := by
    obtain ⟨ω, hω⟩ := hS
    exact hω.1
  exact ⟨g, g.recover hclosed hsub (regularClosed_gerver hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-- A paper maximizer has the volume of the library's concrete Gerver witness. -/
theorem globalMax_volume_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane} (hS : IsGlobalMax S) :
    volume S = volume (gerverSofa P) := by
  have hG := theorem1_1_1 hP hbox
  exact le_antisymm (hG.2 S hS.1) (hS.2 _ hG.1)

/-- Any two global maximizers are congruent via the same internal Gerver witness. -/
theorem globalMax_congruent {S T : Set Plane}
    (hS : IsGlobalMax S) (hT : IsGlobalMax T) : ∃ g : Rigid, S = g '' T := by
  obtain ⟨P, hP, hbox⟩ := definition8_1_2_exists
  obtain ⟨gS, hgS⟩ := image_eq_gerver_of_volume_eq hP hbox hS.1
    (globalMax_volume_eq_gerver hP hbox hS)
  obtain ⟨gT, hgT⟩ := image_eq_gerver_of_volume_eq hP hbox hT.1
    (globalMax_volume_eq_gerver hP hbox hT)
  refine ⟨gT.trans gS.symm, ?_⟩
  rw [Rigid.trans_image, hgT, ← hgS, Rigid.symm_image_image]

/-- Gerver's sofa is a moving sofa of maximum area (Theorem 1.1.1 of Baek's paper). -/
theorem gerverSofa_isGlobalMax {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    IsGlobalMax (gerverSofa P) :=
  theorem1_1_1 hP hbox

/-- A moving sofa has the area of Gerver's sofa if and only if a rigid motion maps it onto
Gerver's sofa. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  refine ⟨image_eq_gerver_of_volume_eq hP hbox hS, ?_⟩
  rintro ⟨g, hg⟩
  rw [← hg, Rigid.volume_image]

/-- The moving sofas of maximum area are exactly the moving sofas that a rigid motion maps onto
Gerver's sofa. (Not every rigid image of Gerver's sofa is a moving sofa: the definition fixes the
starting position in the horizontal side of the hallway.) -/
theorem isGlobalMax_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} :
    IsGlobalMax S ↔ MovingSofaOptimality.IsMovingSofa S ∧ ∃ g : Rigid, g '' S = gerverSofa P := by
  constructor
  · intro h
    exact ⟨h.1, image_eq_gerver_of_volume_eq hP hbox h.1 (globalMax_volume_eq_gerver hP hbox h)⟩
  · rintro ⟨hS, g, hg⟩
    refine ⟨hS, fun T hT => ?_⟩
    have h := (theorem1_1_1 hP hbox).2 T hT
    rwa [← hg, Rigid.volume_image] at h

/-- There is a moving sofa of maximum area, and it is unique up to rigid motions. -/
theorem exists_globalMax_unique_up_to_rigid :
    (∃ S, IsGlobalMax S) ∧ ∀ S T, IsGlobalMax S → IsGlobalMax T → ∃ g : Rigid, S = g '' T := by
  obtain ⟨P, hP, hbox⟩ := definition8_1_2_exists
  exact ⟨⟨gerverSofa P, gerverSofa_isGlobalMax hP hbox⟩, fun _ _ => globalMax_congruent⟩

end MovingSofaUniqueness
