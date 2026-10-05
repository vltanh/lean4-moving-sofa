module

public import MovingSofaUniqueness.Optimality
public import MovingSofaUniqueness.RegularClosed

/-!
# Optimality and uniqueness through maximizer rigidity

`Maximizers` starts from maximality itself and identifies every right-angle maximizer.
`Optimality` then derives the global bound from Baek's intermediate machinery, without invoking
his final optimality theorem. Only after that bound is available does this module turn equality
with Gerver's area into maximality and follow the original sofa through its monotone envelopes.
The public uniqueness statements are preserved; Baek's formalization is unchanged.

The containment and recovery argument is the same as before:

1. A sofa of Gerver's area has an admissible angle `ω ∈ [arcsec(11/5), π/2]`. Its monotonization
   has the same area by the newly derived global bound, and its own cap is maximizing.
2. The maximizer-level pinned bounds give that same monotone sofa a right-angle motion after
   rotation by `π/2 - ω`. Monotonizing again preserves the area and the containment chain.
3. The resulting right-angle cap is a translate of Gerver's cap by maximizer rigidity.
4. Regular closedness of Gerver's sofa recovers the original closed set, not just its measure.

`gerver_sofa_optimal_and_unique` packages the new bound and its equality case. The existing
`IsMaxCap` and equality-case API remain available to the manuscript, bridge, and Solution.
The width argument still strengthens the final congruence to translation for the chosen
starting orientation. No proof of a numbered result in `MovingSofaOptimality` is changed.

Status: this refactored assembly has not been compiled or kernel-audited. Historical
verification of the base commit does not certify these changes. See
`docs/maximizer-first/README.md` and the paper-integration notes there.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-! ## Maximizing caps and the independently assembled upper bound -/

/-- `K` maximizes the sofa area `A_ω` among the caps of angle `ω`. -/
def IsMaxCap (ω : ℝ) (K : Set Plane) : Prop :=
  IsCap K ω ∧ ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

/-- Every moving sofa has area at most that of Gerver's sofa, now obtained from the
maximizer-first route rather than from Baek's final optimality theorem. -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) :=
  MaximizerRoute.area_le_gerver hP hbox hS

/-- The cap bound at every angle, deduced after the new global sofa bound. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω) :
    sofaArea ω K ≤ area (gerverSofa P) :=
  MaximizerRoute.cap_area_le_gerver hP hbox hK

/-- A cap with the area of Gerver's sofa maximizes `A_ω`. This implication is used only
 downstream of the maximizer-first proof of the upper bound. -/
theorem isMaxCap_of_area_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} {ω : ℝ} (hK : IsCap K ω)
    (heq : sofaArea ω K = area (gerverSofa P)) : IsMaxCap ω K :=
  ⟨hK, fun _ hC => (cap_area_le_gerver hP hbox hC).trans_eq heq.symm⟩

/-! ## Every maximizing right-angle cap satisfies injectivity -/

/-- A maximizing right-angle cap has positive sofa area: Gerver's cap is a competitor. -/
theorem sofaArea_pos_of_isMaxCap {K : Set Plane}
    (hK : IsMaxCap (π / 2) K) : 0 < sofaArea (π / 2) K := by
  obtain ⟨P, hP, hbox⟩ := definition8_1_2_exists
  have hcompare := MaximizerRoute.gerver_le_of_maximizes hP hbox hK.2
  have hG := gerverSofa_area hP hbox
  linarith

/-- The maximizer-level injectivity theorem in the public `IsMaxCap` vocabulary. -/
theorem isKi_of_isMaxCap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsMaxCap (π / 2) K) : IsKi K :=
  MaximizerRoute.isKi_of_maximizes hP hbox hK.1 hK.2

/-- The value of a maximizing right-angle cap, without an a priori optimal-value assumption. -/
theorem sofaArea_eq_gerver_of_isMaxCap {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane} (hK : IsMaxCap (π / 2) K) :
    sofaArea (π / 2) K = area (gerverSofa P) :=
  MaximizerRoute.right_angle_maximizer_value hP hbox hK.1 hK.2

/-- **Proposition 3.** A right-angle cap with the sofa area of Gerver's sofa is in `𝒦^i`.
The stronger maximizer-level theorem is proved before the global area bound. -/
theorem isKi_of_maximal_area {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (heq : sofaArea (π / 2) K = area (gerverSofa P)) : IsKi K :=
  isKi_of_isMaxCap hP hbox (isMaxCap_of_area_eq hP hbox hK heq)

/-! ## The equality case in the injectivity domain -/

/-- A cap in `𝒦^i` with Gerver's sofa area has the supports of a horizontal translate of
Gerver's cap. This is `prop:kernel` of the manuscript. -/
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

/-- The sofa of a horizontal translate of Gerver's cap is the same translate of Gerver's sofa. -/
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

/-- A right-angle cap with Gerver's sofa area is a horizontal translate of its cap and sofa. -/
theorem cap_eq_gerver_translate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2)) (heq : sofaArea (π / 2) K = area (gerverSofa P)) :
    ∃ s : ℝ, K = Rigid.translate (s, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (s, 0) '' gerverSofa P := by
  have hmax := isMaxCap_of_area_eq hP hbox hK heq
  exact MaximizerRoute.right_angle_maximizer_eq_gerver hP hbox hK hmax.2

/-- `thm:caps` of the manuscript: equality of the right-angle sofa area is equivalent to
horizontal translation of Gerver's cap. -/
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

/-- All right-angle maximizers are horizontal translates of Gerver's cap. The forward
implication uses maximizer rigidity directly, not a bound assumed in advance. -/
theorem isMaxCap_iff_translate_gerver_cap {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} :
    IsMaxCap (π / 2) K ↔ ∃ s : ℝ, K = Rigid.translate (s, 0) '' P.cap := by
  have hcap := GerverParams.gm_isCap hP hbox
  constructor
  · intro hK
    obtain ⟨s, hs, -⟩ := MaximizerRoute.right_angle_maximizer_eq_gerver hP hbox hK.1 hK.2
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    have hK := isCap_translate_horizontal hcap s
    exact isMaxCap_of_area_eq hP hbox hK ((sofaArea_eq_gerver_iff hP hbox hK).2 ⟨s, rfl⟩)

/-! ## Following a given equality-case sofa -/

/-- A translate of a moving sofa of Gerver's area lies in its monotonization, a monotone sofa of
the same area. The upper comparison is the new maximizer-first global bound. -/
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

/-- **Proposition 4.** The copy of a monotone sofa of Gerver's area rotated by `π/2 - ω`
moves with a right angle. The underlying result requires only maximality and area at least `11/5`. -/
theorem maximal_monotone_has_right_angle {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (heq : area S = area (gerverSofa P)) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  have hmax := own_cap_isMax hP hbox hS heq
  have h22 : (2.2 : ℝ) ≤ area S := heq ▸ gerverSofa_area hP hbox
  exact MaximizerRoute.maximizing_monotone_has_right_angle hS hω h22 hmax.2

/-- A right-angle monotone sofa of Gerver's area is a horizontal translate of Gerver's sofa. -/
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
`π/2 - ω ∈ [0, π/2 - arcsec(11/5)]`, where `ω ∈ [arcsec(11/5), π/2]` is a rotation angle of the sofa. -/
theorem maximizer_contained_in_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g.angle ∈ Icc 0 (π / 2 - arcsec22) ∧ g '' S ⊆ gerverSofa P := by
  have harea : area S = area (gerverSofa P) := congrArg ENNReal.toReal heq
  have h22 : (2.2 : ℝ) ≤ area S := harea ▸ gerverSofa_area hP hbox
  -- Step 1: preserve the specified sofa through its own monotonization.
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨v₀, T, hT, hST, hTarea⟩ := maximal_envelope hP hbox hωpos hSω harea
  -- Step 2: rotate that same monotone sofa and monotonize again.
  have hrot := maximal_monotone_has_right_angle hP hbox hT hω hTarea
  obtain ⟨v₁, U, hU, hTU, hUarea⟩ :=
    maximal_envelope hP hbox pi_div_two_mem_Ioc hrot (by rw [area_image_rot, hTarea])
  -- Step 3: identify the resulting monotone sofa by equality-case rigidity.
  obtain ⟨b, hUG⟩ := right_angle_monotone_eq_gerver hP hbox hU hUarea
  let g := ((Rigid.translate v₀).trans (Rigid.rotate (π / 2 - ω))).trans (Rigid.translate v₁)
  have hSU : g '' S ⊆ U := by
    simp only [g, Rigid.trans_image, Rigid.coe_rotate]
    exact (image_mono (image_mono hST)).trans hTU
  refine ⟨g.trans (Rigid.translate (-b, 0)), ?_, ?_⟩
  · have hangle : (g.trans (Rigid.translate (-b, 0))).angle = π / 2 - ω := by
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

/-- Optimality and its set-theoretic equality case from the same maximizer-first development. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S = volume (gerverSofa P) →
        ∃ g : Rigid, g '' S = gerverSofa P) := by
  have hopt := MaximizerRoute.gerver_sofa_optimal hP hbox
  exact ⟨hopt.1, hopt.2, fun _ hS heq => image_eq_gerver_of_volume_eq hP hbox hS heq⟩

/-! ## The maximal sofas (`cor:all` of the manuscript) -/

/-- A moving sofa has maximal area if and only if a rigid map takes it onto Gerver's sofa.
Both the upper bound and the equality case now follow from the maximizer-first route. -/
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
`(x - y) · v_θ ≤ 1`: the image has width at most one in the rotated vertical direction. -/
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

/-- **No rotation is needed** (`cor:translate`): the width argument forces the angle of the
recovered rigid map to be zero. -/
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

/-- A moving sofa with the area of Gerver's sofa moves with the rotation angle `π/2`. -/
theorem isMovingSofaWithAngle_pi_div_two_of_volume_eq {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    IsMovingSofaWithAngle S (π / 2) := by
  obtain ⟨v, hv⟩ := translate_eq_gerver_of_volume_eq hP hbox hS heq
  have hG := mpc_isMovingSofaWithAngle_translate (GerverParams.gm_movingSofa_std hP hbox).1 (-v)
  rw [← hv, Rigid.coe_translate, image_image] at hG
  simpa using hG

/-- A rotated Gerver sofa fits in the horizontal side only if its rotation is a multiple of `π`. -/
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

/-- A rotated copy of Gerver's sofa is a moving sofa only if its rotation is a multiple of `π`. -/
theorem sin_eq_zero_of_isMovingSofa_rot_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {θ : ℝ} (h : MovingSofaOptimality.IsMovingSofa (rot θ '' gerverSofa P)) :
    sin θ = 0 := by
  obtain ⟨ω, -, -, φ, c, hm⟩ := h
  refine sin_eq_zero_of_rot_gerver_mem_horizSide hP hbox (v := c 0) fun p hp => ?_
  have hstart := hm.start _ ⟨p, hp, rfl⟩
  rwa [hm.angle_zero, rot_zero] at hstart

/-- The copy of Gerver's sofa turned by a right angle is not a moving sofa. -/
theorem not_isMovingSofa_rot_pi_div_two_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) : ¬ MovingSofaOptimality.IsMovingSofa (rot (π / 2) '' gerverSofa P) := by
  intro h
  have hsin := sin_eq_zero_of_isMovingSofa_rot_gerver hP hbox h
  rw [sin_pi_div_two] at hsin
  exact one_ne_zero hsin

end MovingSofaUniqueness
