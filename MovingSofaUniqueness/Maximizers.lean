module

public import MovingSofaUniqueness.Rigidity
public import MovingSofaUniqueness.AngleExtension
public import MovingSofaUniqueness.Curvature

/-!
# Maximizer-level geometry and rigidity

This module starts with maximality, not with equality to a previously known optimal value.
It deliberately does not import `MovingSofaUniqueness.Main`. The primitive maximality hypothesis
is the one accepted by the selection, curvature, and pinned-bound lemmas. The existing public
`IsMaxCap` definition remains in `Main` and can supply these hypotheses without an import cycle.

The order is: existence at a fixed angle; Gerver as a competitor; injectivity for every
right-angle maximizer; the value from Baek's quadratic bound; rigidity of the equality case.
The right-angle motion lemma applies to a specified maximizing monotone sofa of area at least
`11/5`, not merely to one already known to have Gerver's area.

Baek's library is unchanged. Its intermediate theorems are used here, but not its final global
optimality theorem. `Rigidity` imports the upstream `Main` for the quadratic bound; this is not
an assertion of an import-level separation. See `docs/maximizer-first/README.md`.

Status: the new assembly has not been compiled or kernel-audited in this refactor.
-/

@[expose] public section
noncomputable section

open Set Real MeasureTheory MovingSofaOptimality

namespace MovingSofaUniqueness.MaximizerRoute

/-- Fixed-angle maximizers exist and one is the cap of a monotone sofa. We retain this part of
Baek's compactness construction, without using the selected cap's balancedness for geometry. -/
theorem exists_maximizing_cap {ω : ℝ} (hω : ω ∈ Ioc 0 (π / 2)) :
    ∃ K : Set Plane, IsCap K ω ∧ IsMonotoneSofa (K \ niche K ω) ω ∧
      capOf (K \ niche K ω) ω = K ∧
      (∀ C, IsCap C ω → sofaArea ω C ≤ sofaArea ω K) ∧
      (∀ S, IsMovingSofaWithAngle S ω → area S ≤ area (K \ niche K ω)) := by
  obtain ⟨K, hK, hS, hcap, hmax⟩ := theorem3_5_6 hω
  exact ⟨K, hK.2.1, hS.1, hcap, theorem3_5_5 hK, hmax⟩

/-- The lower comparison uses only that Gerver's cap is a competitor. -/
theorem gerver_le_of_maximizes {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {K : Set Plane}
    (hmax : ∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ sofaArea (π / 2) K) :
    area (gerverSofa P) ≤ sofaArea (π / 2) K := by
  have h := hmax P.cap (GerverParams.gm_isCap hP hbox)
  rwa [GerverParams.gm_sofaArea_cap hP hbox] at h

/-- Every maximizing right-angle cap is in the injectivity domain. Neither its optimal value
nor a global upper bound for moving sofas is assumed. -/
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

/-- The value of a right-angle maximizer follows from the two opposite comparisons:
Gerver is a competitor, and `A(K) ≤ Q(x_K) ≤ Q(x_G) = |G|`. -/
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

/-- A specified right-angle maximizer is a horizontal translate of Gerver's cap, and its
cap-minus-niche set is the same translate of Gerver's sofa. This classifies the maximizer
without first invoking the global optimality theorem. -/
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

/-- The same specified maximizing monotone sofa has a right-angle motion, after rotation by
`π/2 - ω`. Its area need only be at least `11/5`; no comparison with Gerver's area is used. -/
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
