module

public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.RegularClosed
public import MovingSofaUniqueness.Rigid

/-!
# Maximizing caps, and optimality and uniqueness from them

A cap with the largest sofa area exists at every angle (`exists_maximizing_cap`, Baek's
Theorems 3.5.5 and 3.5.6). A maximizing right-angle cap satisfies the injectivity condition
(`isKi_of_maximizes`), and Gerver's cap competes with it (`gerver_le_of_maximizes`). If a maximizing
cap has an angle `ω < π/2`, a rotated copy of its sofa moves with the right angle
(`maximizing_monotone_has_right_angle`, `lem:right-motion` of the manuscript `docs/paper`). None of
these uses the value of the largest sofa area.

The second part derives optimality and uniqueness from two facts about the maximizing right-angle
caps: their sofa area is `|G|` (`MaximizingValue`), and they are the horizontal translates of
Gerver's cap (`MaximizingShape`). Optimality needs the first (`Maximizing.gerver_sofa_optimal`);
uniqueness needs both (`Maximizing.image_eq_gerver_of_volume_eq`,
`Maximizing.translate_eq_gerver_of_volume_eq`); the steps are those of `MovingSofaUniqueness.Main`.
Two proofs establish the two facts: `MovingSofaUniqueness.MaximizerRoute`, from Baek's bound for
`𝒬` and the equality analysis of `MovingSofaUniqueness.Rigidity` (`rem:second` of the manuscript),
and `MovingSofaExtremal`, from the coercive certificate (`sec:unified`).
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness

/-! ## Maximizing caps -/

/-- `K` maximizes the sofa area among the caps of angle `ω`. -/
def MaximizesCap (ω : ℝ) (K : Set Plane) : Prop :=
  ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K

/-- `fact:exists` of the manuscript `docs/paper` (Baek's Theorems 3.5.5 and 3.5.6): for every
`ω ∈ (0, π/2]` there is a maximizing cap `K` such that `K \ 𝒩(K)` is a monotone sofa with cap `K`,
and every moving sofa with rotation angle `ω` has area at most `|K \ 𝒩(K)|`. -/
theorem exists_maximizing_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    ∃ K : Set Plane, IsCap K ω ∧ IsMonotoneSofa (K \ niche K ω) ω ∧
      capOf (K \ niche K ω) ω = K ∧ MaximizesCap ω K ∧
      (∀ S, IsMovingSofaWithAngle S ω → area S ≤ area (K \ niche K ω)) := by
  obtain ⟨K, hK, hS, hcap, hmax⟩ := theorem3_5_6 hω
  exact ⟨K, hK.2.1, hS.1, hcap, theorem3_5_5 hK, hmax⟩

/-- A maximizing right-angle cap has sofa area at least `|G|`: Gerver's cap is a competitor. -/
theorem gerver_le_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hmax : MaximizesCap (π / 2) K) :
    area (gerverSofa P) ≤ sofaArea (π / 2) K := by
  have h := hmax P.cap (GerverParams.gm_isCap hP hbox)
  rwa [GerverParams.gm_sofaArea_cap hP hbox] at h

/-- A maximizing right-angle cap lies in `𝒦^i`. Its sofa area is at least `|G| > 0`, so it
satisfies the curvature bounds (`curvature_of_maximal_positive`) and the injectivity condition
(`injectivity_of_curvature`). -/
theorem isKi_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    IsKi K := by
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hG := gerverSofa_area hP hbox
  have hpositive : 0 < sofaArea (π / 2) K := by linarith
  have hcurv := curvature_of_maximal_positive hK hpositive hmax
  refine ⟨hK, injectivity_of_curvature hK hcurv.1 hcurv.2, ?_⟩
  have hn : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at hge
  linarith

/-- `lem:right-motion` of the manuscript `docs/paper`: a monotone sofa with rotation angle
`ω ∈ [arcsec 2.2, π/2]` and area at least `2.2` whose cap is maximizing has a rotated copy, by
`π/2 - ω`, that moves with the rotation angle `π/2`. For `ω < π/2` its cap satisfies the pinned
bounds (`pinned_bounds_of_maximal_positive`). -/
theorem maximizing_monotone_has_right_angle {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S) (hmax : MaximizesCap ω (capOf S ω)) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  rcases eq_or_lt_of_le hω.2 with hright | hsmall
  · simpa [rot_zero, hright] using hS.isMovingSofaWithAngle
  · have hcap := theorem2_4_1 hS.1 hS.isMovingSofaWithAngle hS.isStandardPosition
    have hpositive : 0 < sofaArea ω (capOf S ω) := by
      rw [theorem2_5_10 hS]
      linarith
    have hpin := pinned_bounds_of_maximal_positive ⟨hS.1.1, hsmall⟩ hcap hpositive hmax
    exact right_angle_motion_of_pinned_bounds hS ⟨hω.1, hsmall⟩ harea hpin.1 hpin.2

/-! ## The value and the shape of the maximizing right-angle caps -/

/-- Every maximizing right-angle cap has the sofa area of Gerver's sofa. -/
def MaximizingValue (P : GerverParams) : Prop :=
  ∀ K, IsCap K (π / 2) → MaximizesCap (π / 2) K → sofaArea (π / 2) K = area (gerverSofa P)

/-- Every maximizing right-angle cap is a horizontal translate of Gerver's cap, and its sofa is the
same translate of Gerver's sofa. -/
def MaximizingShape (P : GerverParams) : Prop :=
  ∀ K, IsCap K (π / 2) → MaximizesCap (π / 2) K → ∃ a : ℝ,
    K = Rigid.translate (a, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P

namespace Maximizing

/-! ## Optimality from the value -/

/-- Every right-angle cap has sofa area at most `|G|`, the value of a maximizing cap. -/
theorem right_angle_cap_area_le_gerver {P : GerverParams} (hval : MaximizingValue P)
    {C : Set Plane} (hC : IsCap C (π / 2)) : sofaArea (π / 2) C ≤ area (gerverSofa P) := by
  obtain ⟨K, hK, -, -, hmax, -⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
  exact (hmax C hC).trans_eq (hval K hK hmax)

/-- A moving sofa with rotation angle `π/2` has area at most that of the sofa of a maximizing
right-angle cap, which is `|G|`. -/
theorem right_angle_area_le_gerver {P : GerverParams} (hval : MaximizingValue P)
    {S : Set Plane} (hS : IsMovingSofaWithAngle S (π / 2)) : area S ≤ area (gerverSofa P) := by
  obtain ⟨K, hK, hmono, hcap, hmax, hle⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
  have hA : sofaArea (π / 2) K = area (K \ niche K (π / 2)) := by
    have h := theorem2_5_10 hmono
    rwa [hcap] at h
  calc
    area S ≤ area (K \ niche K (π / 2)) := hle S hS
    _ = sofaArea (π / 2) K := hA.symm
    _ = area (gerverSofa P) := hval K hK hmax

/-- A moving sofa of area at least `2.2` moves with an angle `ω ≥ arcsec 2.2` (Baek's
Theorem 1.5.1); its area is at most that of the sofa of a maximizing cap of angle `ω`, a rotated
copy of which moves with the right angle. -/
theorem area_le_gerver_of_large {P : GerverParams} (hval : MaximizingValue P)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (h22 : (2.2 : ℝ) ≤ area S) : area S ≤ area (gerverSofa P) := by
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨K, -, hmono, hcap, hmax, hle⟩ := exists_maximizing_cap hωpos
  have hT22 : (2.2 : ℝ) ≤ area (K \ niche K ω) := h22.trans (hle S hSω)
  have hown : MaximizesCap ω (capOf (K \ niche K ω) ω) := by
    rw [hcap]
    exact hmax
  have hrot := maximizing_monotone_has_right_angle hmono hω hT22 hown
  calc
    area S ≤ area (K \ niche K ω) := hle S hSω
    _ = area (rot (π / 2 - ω) '' (K \ niche K ω)) :=
      (area_image_rot (π / 2 - ω) (K \ niche K ω)).symm
    _ ≤ area (gerverSofa P) := right_angle_area_le_gerver hval hrot

/-- Every moving sofa has area at most `|G|`; a sofa of area less than `2.2` has, as
`|G| ≥ 2.2192`. -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    area S ≤ area (gerverSofa P) := by
  by_cases h22 : (2.2 : ℝ) ≤ area S
  · exact area_le_gerver_of_large hval hS h22
  · have hG := gerverSofa_area hP hbox
    linarith [lt_of_not_ge h22]

/-- `area_le_gerver`, for the measures: both are finite. -/
theorem volume_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S ≤ volume (gerverSofa P) := by
  rw [← ENNReal.toReal_le_toReal (isBounded_of_isMovingSofa hS).measure_lt_top.ne
    (gerverSofa_volume_ne_top hP hbox)]
  exact area_le_gerver hP hbox hval hS

/-- Gerver's sofa is a moving sofa, and every moving sofa has area at most `|G|`: the statement of
Baek's Theorem 1.1.1. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  ⟨⟨π / 2, (GerverParams.gm_movingSofa_std hP hbox).1⟩,
    fun _ hS => volume_le_gerver hP hbox hval hS⟩

/-- Every cap of every angle `ω` has sofa area at most `|G|`, as
`𝒜_ω(C) ≤ 𝒜_ω(K) = |K \ 𝒩(K)| ≤ |G|` for the maximizing cap `K` of `exists_maximizing_cap`. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) {C : Set Plane} {ω : ℝ} (hC : IsCap C ω) :
    sofaArea ω C ≤ area (gerverSofa P) := by
  obtain ⟨K, -, hmono, hcap, hmax, -⟩ := exists_maximizing_cap hC.1
  have hA : sofaArea ω K = area (K \ niche K ω) := by
    have h := theorem2_5_10 hmono
    rwa [hcap] at h
  calc
    sofaArea ω C ≤ sofaArea ω K := hmax C hC
    _ = area (K \ niche K ω) := hA
    _ ≤ area (gerverSofa P) := area_le_gerver hP hbox hval ⟨ω, hmono.isMovingSofaWithAngle⟩

/-- A right-angle cap is maximizing if and only if it is a horizontal translate of Gerver's cap. -/
theorem right_angle_maximizes_iff_translate_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (hval : MaximizingValue P) (hshape : MaximizingShape P) {K : Set Plane}
    (hK : IsCap K (π / 2)) :
    MaximizesCap (π / 2) K ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap := by
  constructor
  · intro hmax
    obtain ⟨a, hcap, -⟩ := hshape K hK hmax
    exact ⟨a, hcap⟩
  · rintro ⟨a, rfl⟩ C hC
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox),
      GerverParams.gm_sofaArea_cap hP hbox]
    exact right_angle_cap_area_le_gerver hval hC

/-- A right-angle cap has the sofa area of Gerver's sofa if and only if it is a horizontal
translate of Gerver's cap. -/
theorem right_angle_sofaArea_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (hval : MaximizingValue P) (hshape : MaximizingShape P) {K : Set Plane}
    (hK : IsCap K (π / 2)) :
    sofaArea (π / 2) K = area (gerverSofa P) ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap := by
  constructor
  · intro heq
    apply (right_angle_maximizes_iff_translate_gerver hP hbox hval hshape hK).1
    intro C hC
    exact (right_angle_cap_area_le_gerver hval hC).trans_eq heq.symm
  · rintro ⟨a, rfl⟩
    rw [sofaArea_translate_horizontal (GerverParams.gm_isConvexBody_cap hP hbox)]
    exact GerverParams.gm_sofaArea_cap hP hbox

/-! ## Uniqueness from the value and the shape -/

/-- The cap of a monotone sofa of area `|G|` maximizes the sofa area at its angle. -/
theorem own_cap_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) {S : Set Plane} {ω : ℝ} (hS : IsMonotoneSofa S ω)
    (heq : area S = area (gerverSofa P)) : MaximizesCap ω (capOf S ω) := by
  have hvalue : sofaArea ω (capOf S ω) = area (gerverSofa P) := (theorem2_5_10 hS).trans heq
  intro C hC
  exact (cap_area_le_gerver hP hbox hval hC).trans_eq hvalue.symm

/-- A moving sofa of area `|G|` with angle `ω` has a translate inside a monotone sofa of angle `ω`
and area `|G|`, its monotonization. -/
theorem equal_area_envelope {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) {S : Set Plane} {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2))
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
  have hupper := area_le_gerver hP hbox hval ⟨ω, hTm.1⟩
  rw [Rigid.area_image, heq] at hlower
  exact ⟨v, T, hmono, hTm.2.2, le_antisymm hupper hlower⟩

/-- A right-angle monotone sofa of area `|G|` is a horizontal translate of `G`. -/
theorem right_angle_monotone_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) (hshape : MaximizingShape P) {T : Set Plane}
    (hT : IsMonotoneSofa T (π / 2)) (heq : area T = area (gerverSofa P)) :
    ∃ a : ℝ, T = Rigid.translate (a, 0) '' gerverSofa P := by
  have hcap := theorem2_4_1 hT.1 hT.isMovingSofaWithAngle hT.isStandardPosition
  obtain ⟨a, -, ha⟩ := hshape _ hcap (own_cap_maximizes hP hbox hval hT heq)
  exact ⟨a, (theorem2_4_3 hT).trans ha⟩

/-- A rigid map that turns by an angle in `[0, π/2 - arcsec 2.2]` takes a moving sofa of area
`|G|` into `G`. -/
theorem maximizer_contained_in_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) (hshape : MaximizingShape P) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g.angle ∈ Icc 0 (π / 2 - arcsec22) ∧ g '' S ⊆ gerverSofa P := by
  have harea : area S = area (gerverSofa P) := congrArg ENNReal.toReal heq
  have h22 : (2.2 : ℝ) ≤ area S := harea ▸ gerverSofa_area hP hbox
  obtain ⟨ω, hω, hSω⟩ := theorem1_5_1 hS h22
  have hωpos : ω ∈ Ioc 0 (π / 2) := ⟨ang_arcsec22_pos.trans_le hω.1, hω.2⟩
  obtain ⟨v₀, T, hT, hST, hTarea⟩ := equal_area_envelope hP hbox hval hωpos hSω harea
  have hT22 : (2.2 : ℝ) ≤ area T := hTarea ▸ gerverSofa_area hP hbox
  have hrot := maximizing_monotone_has_right_angle hT hω hT22
    (own_cap_maximizes hP hbox hval hT hTarea)
  obtain ⟨v₁, U, hU, hTU, hUarea⟩ := equal_area_envelope hP hbox hval pi_div_two_mem_Ioc hrot
    (by rw [area_image_rot, hTarea])
  obtain ⟨b, hUG⟩ := right_angle_monotone_eq_gerver hP hbox hval hshape hU hUarea
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
with the area of Gerver's sofa onto Gerver's sofa: a rigid image of it lies in `G` and has the same
area, and `G` is the closure of its interior. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) (hshape : MaximizingShape P) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨g, -, hsub⟩ := maximizer_contained_in_gerver hP hbox hval hshape hS heq
  exact ⟨g, g.recover (isCompact_of_isMovingSofa hS).isClosed hsub (gerver_regularClosed hP hbox)
    (gerverSofa_volume_ne_top hP hbox) heq⟩

/-- **No rotation is needed.** The rigid map `g` of `maximizer_contained_in_gerver` maps `S` onto
`G` and turns by `ψ ∈ [0, π/2 - arcsec 2.2]`. As `S` lies in a horizontal strip of height one,
`G = g(S)` has width at most one in the direction `u_{π/2 + ψ}`, while the width of `G` exceeds one
in every direction `u_r`, `r ∈ (π/2, π]` (`gerver_width_gt_one`); so `ψ = 0`. -/
theorem translate_eq_gerver_of_volume_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) (hval : MaximizingValue P) (hshape : MaximizingShape P) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) (heq : volume S = volume (gerverSofa P)) :
    ∃ v : Plane, Rigid.translate v '' S = gerverSofa P := by
  obtain ⟨g, hψ, hsub⟩ := maximizer_contained_in_gerver hP hbox hval hshape hS heq
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
    (hval : MaximizingValue P) (hshape : MaximizingShape P) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P := by
  refine ⟨image_eq_gerver_of_volume_eq hP hbox hval hshape hS, ?_⟩
  rintro ⟨g, hg⟩
  rw [← g.volume_image S, hg]

/-- A moving sofa has the maximal area if and only if a rigid map takes it onto `G`. -/
theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) (hshape : MaximizingShape P) {S : Set Plane}
    (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P := by
  obtain ⟨hG, hle⟩ := gerver_sofa_optimal hP hbox hval
  constructor
  · intro hmax
    exact image_eq_gerver_of_volume_eq hP hbox hval hshape hS (le_antisymm (hle S hS) (hmax _ hG))
  · rintro ⟨g, hg⟩ S' hS'
    rw [← g.volume_image S, hg]
    exact hle S' hS'

/-- Gerver's sofa is a moving sofa, every moving sofa has at most its area, and the moving sofas
with its area are its rigid images. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (hval : MaximizingValue P) (hshape : MaximizingShape P) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) := by
  obtain ⟨hG, hle⟩ := gerver_sofa_optimal hP hbox hval
  exact ⟨hG, hle, fun _ hS => volume_eq_gerver_iff hP hbox hval hshape hS⟩

end Maximizing

end MovingSofaUniqueness
