module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.RegularClosed

/-!
# The uniqueness of Gerver's sofa

Every moving sofa `S` with the area of Gerver's sofa `G` is mapped onto `G` by a rotation about the
origin followed by a translation (`image_eq_gerver_of_volume_eq`). The proof assembles the
propositions of `docs/archive/uniqueness/20-complete-paper-proof.md`:

1. By Baek's Theorem 1.5.1, `S` moves with a rotation angle `ω ∈ [arcsec(11/5), π/2]`. A translate
   of `S` lies in its monotonization, a monotone sofa `T` of the same area (`maximal_envelope`),
   whose cap maximizes the cap area `A_ω` (`own_cap_isMax`).
2. If `ω < π/2`, the pinned bounds of that cap (Propositions 1 and 2) give a right-angle motion of
   the copy of `T` rotated by `π/2 - ω` (Proposition 4, `maximal_monotone_has_right_angle`).
   Monotonizing again gives a right-angle monotone sofa `U` of area `|G|` that contains a rigid
   image of `S`.
3. The cap of `U` satisfies the injectivity condition (Proposition 3, `isKi_of_maximal_area`), so
   `U` is a horizontal translate of `G` (Proposition 5, `ki_sofa_eq_gerver_translate`).
4. `G` is the closure of its interior (Proposition 6, `gerver_regularClosed`), so the rigid image of
   the closed set `S`, which has the same area, is all of `G`.

Three results of the manuscript `docs/paper` sharpen the theorem. A right-angle cap has the sofa
area of `G` if and only if it is a horizontal translate of Gerver's cap, and then its sofa is the
same translate of `G` (`thm:caps`: `sofaArea_eq_gerver_iff`, `cap_eq_gerver_translate`,
`translate_gerver_cap_sdiff_niche`, `isMaxCap_iff_translate_gerver_cap`). A moving sofa has maximal
area if and only if a rigid map takes it onto `G` (`cor:all`: `isMaximal_iff_image_eq_gerver`).
And no rotation is needed (`cor:translate`: `translate_eq_gerver_of_volume_eq`): the rigid map of the
proof turns by `π/2 - ω ∈ [0, π/2 - arcsec(11/5)]` (`maximizer_contained_in_gerver`), a moving sofa
lies in a horizontal strip of height one, and the width of `G` exceeds one in every direction other
than the vertical (`gerver_width_gt_one`), so the angle is zero. For the same reason a rotated copy
`R_θ G` fits into the horizontal side of the hallway only if `θ` is a multiple of `π`, as the
manuscript says (`cor:translate`, `sin_eq_zero_of_rot_gerver_mem_horizSide`,
`sin_eq_zero_of_isMovingSofa_rot_gerver`).
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-! ## Maximizing caps -/

/-- `K` maximizes the sofa area `A_ω` among the caps of angle `ω`. -/
def IsMaxCap (ω : ℝ) (K : Set Plane) : Prop :=
  IsCap K ω ∧ ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

/-- Every moving sofa has area at most that of Gerver's sofa (Baek's Theorem 1.1.1). -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) :=
  ENNReal.toReal_mono (gerverSofa_volume_ne_top hP hbox) ((theorem1_1_1 hP hbox).2 S hS)

/-- Every cap has sofa area at most the area of Gerver's sofa (Baek's Theorems 3.5.5, 3.5.6 and
1.1.1). -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω) :
    sofaArea ω K ≤ area (gerverSofa P) := by
  obtain ⟨B, hB, hS, hcap, _⟩ := theorem3_5_6 hK.1
  have hle := theorem3_5_5 hB K hK
  have hval := theorem2_5_10 hS.1
  rw [hcap] at hval
  have harea := area_le_gerver hP hbox ⟨ω, hS.1.isMovingSofaWithAngle⟩
  linarith

/-- A cap with the area of Gerver's sofa maximizes `A_ω`. -/
theorem isMaxCap_of_area_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω)
    (heq : sofaArea ω K = area (gerverSofa P)) : IsMaxCap ω K :=
  ⟨hK, fun _ hC => (cap_area_le_gerver hP hbox hC).trans_eq heq.symm⟩

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

/-- A cap `K` in `𝒦^i` with the sofa area of Gerver's sofa has the supports of a horizontal
translate of Gerver's cap: `h_K(t) - h_{K_G}(t) = a cos t` on `[0, π]` for some `a`. Equality in
Baek's bound makes the difference of the supports a `CapKernel`, whose solutions are `a cos t`
(`prop:kernel` of the manuscript `docs/paper`). -/
theorem ki_supp_sub_gerver_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsKi K) (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ a : ℝ, ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t := by
  have hmid := ki_maximizer_equality_conditions hP hbox hK heq (1 / 2) (by constructor <;> norm_num)
  have hker := capKernel_of_triple_midpoint (GerverParams.gm_φ_mem_Ioo hP hbox)
    (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hK) hmid
  change CapKernel P.φ (fun t => supp K t - supp P.cap t) at hker
  let a := -(supp K π - supp P.cap π)
  have hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t :=
    hker.eq_horizontal_translation (GerverParams.gm_φ_mem_Ioo hP hbox)
  exact ⟨a, hsupp⟩

/-- **Proposition 5.** A cap in `𝒦^i` with the sofa area of Gerver's sofa is, minus its niche, a
horizontal translate of Gerver's sofa. -/
theorem ki_sofa_eq_gerver_translate {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsKi K)
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ a : ℝ, K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  obtain ⟨a, hsupp⟩ := ki_supp_sub_gerver_eq hP hbox hK heq
  refine ⟨a, ?_⟩
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support hK.1 (GerverParams.gm_isCap hP hbox) a hsupp

/-! ## The maximizing right-angle caps (`thm:caps` of the manuscript) -/

/-- The sofa of a horizontal translate of Gerver's cap is the same translate of Gerver's sofa:
`(K_G + (s, 0)) \ 𝒩(K_G + (s, 0)) = G + (s, 0)`, by `lem:translate` of the manuscript `docs/paper`
(`sofa_eq_translate_of_upper_support`) and `G = K_G \ 𝒩(K_G)`. -/
theorem translate_gerver_cap_sdiff_niche {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (s : ℝ) :
    Rigid.translate (s, 0) '' P.cap \ niche (Rigid.translate (s, 0) '' P.cap) (π / 2) =
      Rigid.translate (s, 0) '' gerverSofa P := by
  have hcap := GerverParams.gm_isCap hP hbox
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support (isCap_translate_horizontal hcap s) hcap s
    fun t _ => supp_translate_horizontal hcap.2.1 s t

/-- `thm:caps` of the manuscript `docs/paper`, for one cap: a right-angle cap `K`
with the sofa area of Gerver's sofa is a horizontal translate `K_G + (s, 0)` of Gerver's cap, and
then `K \ 𝒩(K) = G + (s, 0)`. By `isKi_of_maximal_area` (`cor:Ki`), `K` is in `𝒦^i`, so it has the supports of
`K_G + (s, 0)` on `[0, π]` (`ki_supp_sub_gerver_eq`), and `lem:translate` of the manuscript applies. -/
theorem cap_eq_gerver_translate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2)) (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ s : ℝ, K = Rigid.translate (s, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (s, 0) '' gerverSofa P := by
  obtain ⟨s, hsupp⟩ := ki_supp_sub_gerver_eq hP hbox (isKi_of_maximal_area hP hbox hK heq) heq
  have hKs := cap_eq_translate_of_upper_support hK (GerverParams.gm_isCap hP hbox) s hsupp
  refine ⟨s, hKs, ?_⟩
  rw [hKs]
  exact translate_gerver_cap_sdiff_niche hP hbox s

/-- **`thm:caps` of the manuscript** `docs/paper`: a right-angle cap `K` has the sofa
area of Gerver's sofa, `𝒜_{π/2}(K) = |G|`, if and only if `K = K_G + (s, 0)` for some `s`. A
horizontal translation preserves the sofa area (`sofaArea_translate_horizontal`), and
`𝒜_{π/2}(K_G) = |G|`. -/
theorem sofaArea_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2)) :
    sofaArea (π / 2) K = area (gerverSofa P) ↔ ∃ s : ℝ, K = Rigid.translate (s, 0) '' P.cap := by
  constructor
  · intro heq
    obtain ⟨s, hs, -⟩ := cap_eq_gerver_translate hP hbox hK heq
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox)]
    exact GerverParams.gm_sofaArea_cap hP hbox

/-- `thm:caps` of the manuscript `docs/paper`, the maximizers: the maximizers of the sofa area
`𝒜_{π/2}` on the right-angle caps are the horizontal translates of Gerver's cap. The maximum is
`|G|` (`cap_area_le_gerver`), attained by Gerver's cap. -/
theorem isMaxCap_iff_translate_gerver_cap {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} :
    IsMaxCap (π / 2) K ↔ ∃ s : ℝ, K = Rigid.translate (s, 0) '' P.cap := by
  have hcap := GerverParams.gm_isCap hP hbox
  constructor
  · intro hK
    have hge := hK.2 P.cap hcap
    rw [GerverParams.gm_sofaArea_cap hP hbox] at hge
    exact (sofaArea_eq_gerver_iff hP hbox hK.1).1
      (le_antisymm (cap_area_le_gerver hP hbox hK.1) hge)
  · rintro ⟨s, rfl⟩
    have hK := isCap_translate_horizontal hcap s
    exact isMaxCap_of_area_eq hP hbox hK ((sofaArea_eq_gerver_iff hP hbox hK).2 ⟨s, rfl⟩)

/-! ## The theorem -/

/-- A translate of a moving sofa of Gerver's area lies in its monotonization, a monotone sofa of
the same area. -/
theorem maximal_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
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
  have hupper := area_le_gerver hP hbox ⟨ω, hTm.1⟩
  rw [Rigid.area_image, heq] at hlower
  exact ⟨v, T, hmono, hTm.2.2, le_antisymm hupper hlower⟩

/-- The cap of a monotone sofa of Gerver's area maximizes the cap area. -/
theorem own_cap_isMax {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : IsMaxCap ω (capOf S ω) :=
  isMaxCap_of_area_eq hP hbox
    (theorem2_4_1 hS.1 hS.isMovingSofaWithAngle hS.isStandardPosition)
    ((theorem2_5_10 hS).trans heq)

/-- **Proposition 4.** The copy of a monotone sofa of Gerver's area rotated by `π/2 - ω` moves with
a right angle: for `ω < π/2`, by the pinned bounds (19) of its maximizing cap; for `ω = π/2` the
rotation is the identity. -/
theorem maximal_monotone_has_right_angle {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (heq : area S = area (gerverSofa P)) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  rcases eq_or_lt_of_le hω.2 with hright | hsmall
  · simpa [rot_zero, hright] using hS.isMovingSofaWithAngle
  · have hmax := own_cap_isMax hP hbox hS heq
    have hpositive : 0 < sofaArea ω (capOf S ω) := by
      rw [theorem2_5_10 hS, heq]
      have hG := gerverSofa_area hP hbox
      linarith
    have hpin := pinned_bounds_of_maximal_positive ⟨hS.1.1, hsmall⟩ hmax.1 hpositive hmax.2
    apply right_angle_motion_of_pinned_bounds hS ⟨hω.1, hsmall⟩ _ hpin.1 hpin.2
    rw [heq]
    exact gerverSofa_area hP hbox

/-- A right-angle monotone sofa of Gerver's area is a horizontal translate of Gerver's sofa: the
last statement of `thm:caps` of the manuscript `docs/paper`. Its cap is in `𝒦^i`
(`cor:Ki`), and the sofa is its cap minus its niche (Baek's Theorem 2.4.3). -/
theorem right_angle_monotone_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  have hvalue : sofaArea (π / 2) (capOf T (π / 2)) = area (gerverSofa P) :=
    (theorem2_5_10 hT).trans heq
  obtain ⟨a, ha⟩ := ki_sofa_eq_gerver_translate hP hbox
    (isKi_of_maximal_area hP hbox hcap hvalue) hvalue
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- A rigid image of a moving sofa of Gerver's area lies in Gerver's sofa. The rigid map turns by
`π/2 - ω ∈ [0, π/2 - arcsec(11/5)]`, where `ω ∈ [arcsec(11/5), π/2]` is a rotation angle of the
sofa (Baek's Theorem 1.5.1). -/
theorem maximizer_contained_in_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g.angle ∈ Icc 0 (π / 2 - arcsec22) ∧ g '' S ⊆ gerverSofa P := by
  have harea : area S = area (gerverSofa P) := congrArg ENNReal.toReal heq
  have h22 : (2.2 : ℝ) ≤ area S := harea ▸ gerverSofa_area hP hbox
  -- Step 1: `S` moves with an angle `ω ∈ [arcsec(11/5), π/2]`, and a translate of `S` lies in a
  -- monotone sofa `T` of Gerver's area.
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨v₀, T, hT, hST, hTarea⟩ := maximal_envelope hP hbox hωpos hSω harea
  -- Step 2: the copy of `T` rotated by `π/2 - ω` moves with a right angle, and a translate of it
  -- lies in a right-angle monotone sofa `U` of Gerver's area.
  have hrot := maximal_monotone_has_right_angle hP hbox hT hω hTarea
  obtain ⟨v₁, U, hU, hTU, hUarea⟩ :=
    maximal_envelope hP hbox pi_div_two_mem_Ioc hrot (by rw [area_image_rot, hTarea])
  -- Step 3: `U` is a horizontal translate of Gerver's sofa.
  obtain ⟨b, hUG⟩ := right_angle_monotone_eq_gerver hP hbox hU hUarea
  let g := ((Rigid.translate v₀).trans (Rigid.rotate (π / 2 - ω))).trans (Rigid.translate v₁)
  have hSU : g '' S ⊆ U := by
    simp only [g, Rigid.trans_image, Rigid.coe_rotate]
    exact (image_mono (image_mono hST)).trans hTU
  refine ⟨g.trans (Rigid.translate (-b, 0)), ?_, ?_⟩
  · -- The map turns by `π/2 - ω`.
    have hangle : (g.trans (Rigid.translate (-b, 0))).angle = π / 2 - ω := by
      simp only [g, Rigid.trans, Rigid.translate, Rigid.rotate]
      ring
    rw [hangle]
    exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
  · rw [Rigid.trans_image]
    rintro _ ⟨q, hq, rfl⟩
    have hqU := hSU hq
    rw [hUG] at hqU
    obtain ⟨r, hr, rfl⟩ := hqU
    have hcancel : r + (b, 0) + (-b, 0) = r := by ext <;> simp
    simpa [hcancel] using hr

/-- **The uniqueness of Gerver's sofa.** A rotation about the origin followed by a translation maps
every moving sofa with the area of Gerver's sofa onto Gerver's sofa. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, -, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-! ## The maximal sofas (`cor:all` of the manuscript) -/

/-- **The maximal sofas** (`cor:all` of the manuscript `docs/paper`): a moving sofa
has the maximal area among moving sofas if and only if a rotation about the origin followed by a
translation maps it onto Gerver's sofa. One direction is the uniqueness theorem, as the maximum is
the area of Gerver's sofa (Baek's Theorem 1.1.1); conversely, a rigid image of Gerver's sofa has the
area of Gerver's sofa. -/
theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨hG, hle⟩ := theorem1_1_1 hP hbox
  constructor
  · intro hmax
    exact image_eq_gerver_of_volume_eq hP hbox hS (le_antisymm (hle S hS) (hmax _ hG))
  · rintro ⟨g, hg⟩ S' hS'
    rw [← g.volume_image S, hg]
    exact hle S' hS'

/-! ## No rotation is needed (`cor:translate` of the manuscript) -/

/-- A moving sofa lies in a horizontal strip of height one: its translate at the start of its
movement lies in the horizontal side `H_L = (-∞, 1] × [0, 1]` of the hallway. -/
theorem snd_sub_le_one_of_isMovingSofa {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) {p q : Plane} (hp : p ∈ S) (hq : q ∈ S) :
    p.2 - q.2 ≤ 1 := by
  obtain ⟨ω, -, -, θ, c, hm⟩ := hS
  have hp' := hm.start p hp
  have hq' := hm.start q hq
  rw [hm.angle_zero, rot_zero] at hp' hq'
  obtain ⟨-, -, hp1⟩ := hp'
  obtain ⟨-, hq0, -⟩ := hq'
  simp only [Prod.snd_add] at hp1 hq0
  linarith

/-- If a rigid map `g` of angle `θ` takes a moving sofa `S` onto a set containing `x` and `y`, then
`(x - y) · v_θ ≤ 1`: the image of `S` has width at most one in the direction
`v_θ = u_{θ + π/2}`, the image of the vertical direction under `R_θ`. -/
theorem dot_sub_vvec_le_one_of_mem_image {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (g : Rigid) {x y : Plane} (hx : x ∈ g '' S)
    (hy : y ∈ g '' S) : dot (x - y) (vvec g.angle) ≤ 1 := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  have he : g p - g q = rot g.angle (p - q) := by
    change rot g.angle p + g.shift - (rot g.angle q + g.shift) = rot g.angle (p - q)
    ext <;> simp only [rot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [he, dot_rot_vvec_eq_snd, Prod.snd_sub]
  exact snd_sub_le_one_of_isMovingSofa hS hp hq

/-- **No rotation is needed** (`cor:translate` of the manuscript `docs/paper`): every
moving sofa with the area of Gerver's sofa is a translate of Gerver's sofa. The rigid map `g` of
the proof of the theorem maps `S` onto `G` and turns by `ψ ∈ [0, π/2 - arcsec(11/5)]`
(`maximizer_contained_in_gerver`). As `S` lies in a horizontal strip of height one, `G = g(S)` has
width at most one in the direction `u_{π/2 + ψ}`, while the width of `G` exceeds one in every
direction `u_r`, `r ∈ (π/2, π]` (`gerver_width_gt_one`); so `ψ = 0`. -/
theorem translate_eq_gerver_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ v : Plane, Rigid.translate v '' S = gerverSofa P := by
  -- Step 1: the rigid map of the proof of the theorem maps `S` onto `G` and turns by
  -- `ψ ∈ [0, π/2 - arcsec(11/5)]`.
  obtain ⟨g, hψ, hsub⟩ := maximizer_contained_in_gerver hP hbox hS heq
  have hg : g '' S = gerverSofa P :=
    g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
      (gerverSofa_volume_ne_top hP hbox) heq
  -- Step 2: `G = g(S)` has width at most one in the direction `u_{ψ + π/2} = v_ψ`.
  have hwidth : ∀ x ∈ gerverSofa P, ∀ y ∈ gerverSofa P,
      dot (x - y) (uvec (g.angle + π / 2)) ≤ 1 := by
    intro x hx y hy
    rw [← hg] at hx hy
    rw [uvec_add_pi_div_two]
    exact dot_sub_vvec_le_one_of_mem_image hS g hx hy
  -- Step 3: for `ψ > 0` the direction `u_{ψ + π/2}` has `ψ + π/2 ∈ (π/2, π)`, where the width of
  -- `G` exceeds one; so `ψ = 0`, and `g` is a translation.
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

/-- A moving sofa with the area of Gerver's sofa moves with the rotation angle `π/2` (`cor:translate` of
the manuscript `docs/paper`): it is a translate of Gerver's sofa, which does. -/
theorem isMovingSofaWithAngle_pi_div_two_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    IsMovingSofaWithAngle S (π / 2) := by
  obtain ⟨v, hv⟩ := translate_eq_gerver_of_volume_eq hP hbox hS heq
  have hG := mpc_isMovingSofaWithAngle_translate (GerverParams.gm_movingSofa_std hP hbox).1 (-v)
  rw [← hv, Rigid.coe_translate, image_image] at hG
  simpa using hG

/-- A rotated copy `R_θ G` of Gerver's sofa fits into the horizontal side `H_L` of the hallway,
after a translation, only if `θ` is a multiple of `π` (`cor:translate` of the manuscript
`docs/paper`): `R_θ G` then has height at most one, so `G` has width at most one in the direction
`R_{-θ} u_{π/2} = (sin θ, cos θ)`, which is therefore vertical
(`fst_eq_zero_of_gerver_width_le_one`). -/
theorem sin_eq_zero_of_rot_gerver_mem_horizSide {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {θ : ℝ} {v : Plane} (h : ∀ p ∈ gerverSofa P, rot θ p + v ∈ horizSide) :
    sin θ = 0 := by
  refine fst_eq_zero_of_gerver_width_le_one hP hbox (w := (sin θ, cos θ)) (sin_sq_add_cos_sq θ) ?_
  intro p hp q hq
  obtain ⟨-, -, hp1⟩ := h p hp
  obtain ⟨-, hq0, -⟩ := h q hq
  simp only [rot, Prod.snd_add] at hp1 hq0
  simp only [dot, Prod.fst_sub, Prod.snd_sub]
  linarith

/-- A rotated copy `R_θ G` of Gerver's sofa is a moving sofa only if `θ` is a multiple of `π`, since
a moving sofa starts in the horizontal side of the hallway. So not every rotated copy of `G` is a
moving sofa (`not_isMovingSofa_rot_pi_div_two_gerver`). -/
theorem sin_eq_zero_of_isMovingSofa_rot_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {θ : ℝ} (h : MovingSofaOptimality.IsMovingSofa (rot θ '' gerverSofa P)) :
    sin θ = 0 := by
  obtain ⟨ω, -, -, φ, c, hm⟩ := h
  refine sin_eq_zero_of_rot_gerver_mem_horizSide hP hbox (v := c 0) fun p hp => ?_
  have hstart := hm.start _ ⟨p, hp, rfl⟩
  rwa [hm.angle_zero, rot_zero] at hstart

/-- The copy `R_{π/2} G` of Gerver's sofa turned by a right angle is not a moving sofa. -/
theorem not_isMovingSofa_rot_pi_div_two_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) : ¬ MovingSofaOptimality.IsMovingSofa (rot (π / 2) '' gerverSofa P) := by
  intro h
  have hsin := sin_eq_zero_of_isMovingSofa_rot_gerver hP hbox h
  rw [sin_pi_div_two] at hsin
  exact one_ne_zero hsin

end MovingSofaUniqueness
