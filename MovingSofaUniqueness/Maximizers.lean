module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Curvature

/-!
# Maximizing caps: the largest sofa area at the right angle

The first half of the second proof of Baek's optimality theorem (`rem:second` of the manuscript
`docs/paper`), which does not use Baek's Theorem 1.1.1. For every rotation angle there is a
maximizing cap whose cap minus niche is a monotone sofa (`exists_maximizing_cap`, Baek's Theorems
3.5.5 and 3.5.6). A maximizing right-angle cap `K` has `|G| ≤ 𝒜(K)`, as Gerver's cap is a
competitor; it satisfies the curvature bounds, so it lies in `𝒦^i` (`isKi_of_maximizes`), and
`𝒜(K) ≤ 𝒬(K, B_K, D_K) ≤ 𝒬(K_G, B_G, D_G) = |G|`. So `𝒜(K) = |G|`
(`right_angle_maximizer_value`), and the equality case makes `K` a horizontal translate of Gerver's
cap (`right_angle_maximizer_eq_gerver`). A monotone sofa of area at least `11/5` whose cap is
maximizing has a rotated copy that turns by a right angle (`maximizing_monotone_has_right_angle`).

The declarations are in the namespace `MovingSofaUniqueness.MaximizerRoute`. The module does not
import `MovingSofaUniqueness.Main`, whose results use Baek's theorem, and it writes maximality as
`∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K` instead of `IsMaxCap`, which `Main` defines. It
imports Baek's `MovingSofaOptimality.Main` (through `Rigidity`) for Corollary 8.5.8, which that
module shares with Theorem 1.1.1; `scripts/AuditMaximizerRoute.lean` checks that the second proof
does not use Theorem 1.1.1.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- `fact:exists` of the manuscript `docs/paper` (Baek's Theorems 3.5.5 and 3.5.6): for every
`ω ∈ (0, π/2]` there is a maximizing cap `K` such that `K \ 𝒩(K)` is a monotone sofa with cap `K`,
and every moving sofa with rotation angle `ω` has area at most `|K \ 𝒩(K)|`. -/
theorem exists_maximizing_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    ∃ K : Set Plane, IsCap K ω ∧ IsMonotoneSofa (K \ niche K ω) ω ∧
      capOf (K \ niche K ω) ω = K ∧
      (∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) ∧
      (∀ S, IsMovingSofaWithAngle S ω → area S ≤ area (K \ niche K ω)) := by
  obtain ⟨K, hK, hS, hcap, hmax⟩ := theorem3_5_6 hω
  exact ⟨K, hK.2.1, hS.1, hcap, theorem3_5_5 hK, hmax⟩

/-- A maximizing right-angle cap has sofa area at least `|G|`: Gerver's cap is a competitor. -/
theorem gerver_le_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane}
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    area (gerverSofa P) ≤ sofaArea (π / 2) K := by
  have h := hmax P.cap (GerverParams.gm_isCap hP hbox)
  rwa [GerverParams.gm_sofaArea_cap hP hbox] at h

/-- `prop:unified-caps` (a) of the manuscript `docs/paper`, first part: a maximizing right-angle cap
in `𝒦^i`. Its sofa area is at least `|G| > 0`, so it satisfies the curvature bounds
(`curvature_of_maximal_positive`) and the injectivity condition (`injectivity_of_curvature`). -/
theorem isKi_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    IsKi K := by
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hG := gerverSofa_area hP hbox
  have hpositive : 0 < sofaArea (π / 2) K := by linarith
  have hcurv := curvature_of_maximal_positive hK hpositive hmax
  refine ⟨hK, injectivity_of_curvature hK hcurv.1 hcurv.2, ?_⟩
  have hn : 0 ≤ area (niche K (π / 2)) := ENNReal.toReal_nonneg
  unfold sofaArea at hge
  linarith

/-- `rem:second` of the manuscript `docs/paper`: a maximizing right-angle cap has the sofa area
of Gerver's sofa, as `|G| ≤ 𝒜(K) ≤ 𝒬(K, B_K, D_K) ≤ 𝒬(K_G, B_G, D_G) = |G|` (Baek's Theorems
8.2.4, 8.1.8 and 8.4.6 and Corollary 8.5.8). -/
theorem right_angle_maximizer_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane} (hK : IsCap K (π / 2))
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    sofaArea (π / 2) K = area (gerverSofa P) := by
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hbound := theorem8_2_4 hbox.1 hKi
  have hQ := corollary8_5_8 hP hbox (theorem8_1_8 hbox.1 hKi)
  have hGQ := theorem8_4_6 hP hbox
  have hGA := GerverParams.gm_sofaArea_cap hP hbox
  linarith

/-- `prop:unified-caps` (b) of the manuscript `docs/paper`, by the equality analysis: a maximizing
right-angle cap is a
horizontal translate `K_G + (a, 0)` of Gerver's cap, and its sofa is `G + (a, 0)`, by `prop:kernel`
and `lem:translate` of the manuscript. -/
theorem right_angle_maximizer_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2))
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hvalue := right_angle_maximizer_value hP hbox hK hmax
  have hmid := ki_maximizer_equality_conditions hP hbox hKi hvalue (1 / 2)
    (by constructor <;> norm_num)
  have hker := capKernel_of_triple_midpoint (GerverParams.gm_φ_mem_Ioo hP hbox)
    (gerverTriple hP hbox) (kiExtensionTriple hbox.1 hKi) hmid
  change CapKernel P.φ (fun t => supp K t - supp P.cap t) at hker
  let a := -(supp K π - supp P.cap π)
  have hsupp : ∀ t ∈ Icc (0 : ℝ) π, supp K t - supp P.cap t = a * cos t :=
    hker.eq_horizontal_translation (GerverParams.gm_φ_mem_Ioo hP hbox)
  have hGcap := GerverParams.gm_isCap hP hbox
  refine ⟨a, cap_eq_translate_of_upper_support hK hGcap a hsupp, ?_⟩
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  rw [hGset]
  exact sofa_eq_translate_of_upper_support hK hGcap a hsupp

/-- `lem:right-motion` of the manuscript `docs/paper`: a monotone sofa with rotation angle
`ω ∈ [arcsec(11/5), π/2]` and area at least `11/5` whose cap is maximizing has a rotated copy, by
`π/2 - ω`, that moves with the rotation angle `π/2`. For `ω < π/2` its cap satisfies the pinned
bounds (`pinned_bounds_of_maximal_positive`). -/
theorem maximizing_monotone_has_right_angle {S : Set Plane} {ω : ℝ}
    (hS : IsMonotoneSofa S ω) (hω : ω ∈ Icc arcsec22 (π / 2))
    (harea : (2.2 : ℝ) ≤ area S)
    (hmax : ∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω (capOf S ω)) :
    IsMovingSofaWithAngle (rot (π / 2 - ω) '' S) (π / 2) := by
  rcases eq_or_lt_of_le hω.2 with hright | hsmall
  · simpa [rot_zero, hright] using hS.isMovingSofaWithAngle
  · have hcap := theorem2_4_1 hS.1 hS.isMovingSofaWithAngle hS.isStandardPosition
    have hpositive : 0 < sofaArea ω (capOf S ω) := by
      rw [theorem2_5_10 hS]
      linarith
    have hpin := pinned_bounds_of_maximal_positive ⟨hS.1.1, hsmall⟩ hcap hpositive hmax
    exact right_angle_motion_of_pinned_bounds hS ⟨hω.1, hsmall⟩ harea hpin.1 hpin.2

end MovingSofaUniqueness.MaximizerRoute
