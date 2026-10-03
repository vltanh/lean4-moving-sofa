module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.RegularClosed

/-!
# The uniqueness of Gerver's sofa

Every moving sofa `S` with the area of Gerver's sofa `G` is mapped onto `G` by a rotation about the
origin followed by a translation (`image_eq_gerver_of_volume_eq`). The proof assembles the
propositions of `docs/uniqueness/20-complete-paper-proof.md`:

1. By Baek's Theorem 1.5.1, `S` moves with a rotation angle `ω ∈ [arcsec(11/5), π/2]`. A translate
   of `S` lies in its monotonization, a monotone sofa `T` of the same area (`maximal_envelope`),
   whose cap maximizes the cap area `A_ω` (`own_cap_isMax`).
2. If `ω < π/2`, the pinned bounds of that cap (Propositions 1 and 2) give a right-angle motion of a
   rotated copy of `T` (Proposition 4, `maximal_monotone_has_right_angle`). Monotonizing again gives
   a right-angle monotone sofa `U` of area `|G|` that contains a rigid image of `S`.
3. The cap of `U` satisfies the injectivity condition (Proposition 3, `isKi_of_maximal_area`), so
   `U` is a horizontal translate of `G` (Proposition 5, `ki_sofa_eq_gerver_translate`).
4. `G` is the closure of its interior (Proposition 6, `gerver_regularClosed`), so the rigid image of
   the closed set `S`, which has the same area, is all of `G`.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-! ## Maximizing caps -/

/-- `K` maximizes the sofa area `A_ω` among the caps of angle `ω`. -/
def IsMaxCap (ω : ℝ) (K : Set Plane) : Prop :=
  IsCap K ω ∧ ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

theorem moving_of_monotone {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsMovingSofaWithAngle S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).1

theorem standard_of_monotone {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) : IsStandardPosition S ω := by
  obtain ⟨hω, T, hT, hstd, rfl⟩ := hS
  exact (theorem2_3_2 hω hT hstd).2.1

theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  exact ENNReal.toReal_mono (gerverSofa_volume_ne_top hP hbox)
    ((theorem1_1_1 hP hbox).2 S hS)

/-- Every cap has sofa area at most the area of Gerver's sofa (Baek's Theorems 3.5.5, 3.5.6 and
1.1.1). -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω) :
    sofaArea ω K ≤ area (gerverSofa P) := by
  obtain ⟨B, hB, hS, hcap, _⟩ := theorem3_5_6 hK.1
  have hle := theorem3_5_5 hB K hK
  have hval := theorem2_5_10 hS.1
  rw [hcap] at hval
  have harea := area_le_gerver hP hbox ⟨ω, moving_of_monotone hS.1⟩
  linarith

theorem isMaxCap_of_area_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω)
    (heq : sofaArea ω K = area (gerverSofa P)) : IsMaxCap ω K := by
  refine ⟨hK, fun C hC => ?_⟩
  rw [heq]
  exact cap_area_le_gerver hP hbox hC

/-! ## Proposition 3: maximizing right-angle caps satisfy the injectivity condition -/

/-- A maximizing right-angle cap has positive sofa area: Gerver's cap is a competitor. -/
theorem sofaArea_pos_of_isMaxCap {K : Set Plane}
    (hK : IsMaxCap (π / 2) K) : 0 < sofaArea (π / 2) K := by
  obtain ⟨P, hP, hbox⟩ := definition8_1_2_exists
  have hcompare := hK.2 P.cap (GerverParams.gm_isCap hP hbox)
  rw [GerverParams.gm_sofaArea_cap hP hbox] at hcompare
  have hG := gerverSofa_area hP hbox
  linarith

/-- **Proposition 3.** A right-angle cap with the sofa area of Gerver's sofa is in `𝒦^i`: its
curvature bounds (16) give the injectivity condition. -/
theorem isKi_of_maximal_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) : IsKi K := by
  have hmax := isMaxCap_of_area_eq hP hbox hK heq
  have hcurv := curvature_of_maximal_positive hK (sofaArea_pos_of_isMaxCap hmax) hmax.2
  refine ⟨hK, injectivity_of_curvature hK hcurv.1 hcurv.2, ?_⟩
  have hG := gerverSofa_area hP hbox
  have hn : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at heq
  linarith

/-! ## Proposition 5: such a cap is Gerver's cap -/

/-- **Proposition 5.** A cap in `𝒦^i` with the sofa area of Gerver's sofa is, minus its niche, a
horizontal translate of Gerver's sofa. -/
theorem ki_sofa_eq_gerver_translate {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsKi K)
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ a : ℝ, K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  have hmid := (ki_maximizer_equality_conditions hP hbox hK heq).2
    (1 / 2) (by constructor <;> norm_num)
  have hker := capKernel_of_triple_midpoint (GerverParams.gm_φ_mem_Ioo hP hbox)
    (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) hmid
  change CapKernel P.φ (fun t => supp K t - supp P.cap t) at hker
  let a := -(supp K π - supp P.cap π)
  have hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t :=
    hker.eq_horizontal_translation (GerverParams.gm_φ_mem_Ioo hP hbox)
  refine ⟨a, ?_⟩
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support hK.1 (GerverParams.gm_isCap hP hbox) a hsupp

/-! ## The theorem -/

private theorem coe_translate (v : Plane) :
    (Rigid.translate v : Plane → Plane) = fun p => p + v := by
  funext p
  exact Rigid.translate_apply v p

private theorem coe_rotate (a : ℝ) :
    (Rigid.rotate a : Plane → Plane) = rot a := by
  funext p
  exact Rigid.rotate_apply a p

/-- A translate of a moving sofa of Gerver's area lies in its monotonization, a monotone sofa of
the same area. -/
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

/-- The cap of a monotone sofa of Gerver's area maximizes the cap area. -/
theorem own_cap_isMax {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : IsMaxCap ω (capOf S ω) := by
  apply isMaxCap_of_area_eq hP hbox
    (theorem2_4_1 hS.1 (moving_of_monotone hS) (standard_of_monotone hS))
  rw [theorem2_5_10 hS]
  exact heq

/-- **Proposition 4.** A rotated copy of a monotone sofa of Gerver's area moves with a right angle:
for `ω < π/2`, by the pinned bounds (19) of its maximizing cap. -/
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
    have hpin := pinned_bounds_of_maximal_positive ⟨hS.1.1, hsmall⟩ hmax.1 hpositive hmax.2
    apply right_angle_motion_of_pinned_bounds hS ⟨hω.1, hsmall⟩ _ hpin.1 hpin.2
    rw [heq]
    exact gerverSofa_area hP hbox

/-- A right-angle monotone sofa of Gerver's area is a horizontal translate of Gerver's sofa. -/
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

/-- A rigid image of a moving sofa of Gerver's area lies in Gerver's sofa. -/
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

/-- **The uniqueness of Gerver's sofa.** A rotation about the origin followed by a translation maps
every moving sofa with the area of Gerver's sofa onto Gerver's sofa. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  have hclosed : IsClosed S := by
    obtain ⟨ω, hω⟩ := hS
    exact hω.1
  exact ⟨g, g.recover hclosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

end MovingSofaUniqueness
