module

public import MovingSofaUniqueness.Curvature
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Rigid

/-!
# Maximizing caps

A cap with the largest sofa area exists at every angle (`exists_maximizing_cap`, Baek's
Theorems 3.5.5 and 3.5.6). A maximizing right-angle cap satisfies the injectivity condition
(`isKi_of_maximizes`), and Gerver's cap competes with it (`gerver_le_of_maximizes`). If a maximizing
cap has an angle `ω < π/2`, a rotated copy of its sofa moves with the right angle
(`maximizing_monotone_has_right_angle`). `MovingSofaUniqueness.MaximizerRoute` proves the same
four results (`lem:max-right` and `lem:right-motion` of the manuscript `docs/paper`); they are
proved again here because its module imports `MovingSofaUniqueness.Rigidity`, the equality analysis
that the coercive route replaces.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaExtremal

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

/-- A monotone sofa with rotation angle `ω ∈ [arcsec 2.2, π/2]` and area at least `2.2` whose cap
is maximizing has a rotated copy, by `π/2 - ω`, that moves with the rotation angle `π/2`. For
`ω < π/2` its cap satisfies the pinned bounds (`pinned_bounds_of_maximal_positive`). -/
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

end MovingSofaExtremal
