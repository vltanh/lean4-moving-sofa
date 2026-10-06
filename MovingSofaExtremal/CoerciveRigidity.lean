module

public import MovingSofaExtremal.Geometry
public import MovingSofaExtremal.HorizontalTranslation
public import MovingSofaStability.SharpCapDistance

/-!
# Zero deficit gives right-angle rigidity

Uncompiled proof source. The value comes from Gerver as a competitor and the
nonsmooth Q certificate. The shape comes from the quantitative cap-distance
estimate at zero deficit. No old midpoint-equality, tangent-kernel, or CapKernel
classification is used, and global sofa stability is not imported.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness
open MovingSofaStability

namespace MovingSofaExtremal

/-- On the wide triple domain, zero Q deficit fixes the cap up to translation.
This does not assert uniqueness of the two auxiliary bodies. -/
theorem wide_zero_deficit_cap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (hQ : wideUpperQ P.φ x = area (gerverSofa P)) :
    x.1.1.1 = shiftedReferenceCap P.cap x.1.1.1 := by
  have hd := sharp_wide_cap_distance_bound hP hbox x
  rw [hQ, sub_self, sqrt_zero, mul_zero] at hd
  exact EuclideanClose.eq_of_zero hd

/-- The canonical triple of a maximizing right-angle cap has Gerver's value.
This proves the value; it does not assume the known global sofa optimum. -/
theorem right_angle_maximizer_certificate {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane}
    (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    ∃ hKi : IsKi K,
      sofaArea (π / 2) K = area (gerverSofa P) ∧
      wideUpperQ P.φ (toWideTriple (MovingSofaStability.kiExtensionTriple hbox.1 hKi)) =
        area (gerverSofa P) := by
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hA := theorem8_2_4 hbox.1 hKi
  let x := toWideTriple (MovingSofaStability.kiExtensionTriple hbox.1 hKi)
  have hQ := wideUpperQ_le_gerver hP hbox x
  rw [wideGerver_value hP hbox] at hQ
  have hAx : sofaArea (π / 2) K ≤ wideUpperQ P.φ x := hA
  have hvalue : sofaArea (π / 2) K = area (gerverSofa P) := by linarith
  have hQvalue : wideUpperQ P.φ x = area (gerverSofa P) := by linarith
  exact ⟨hKi, hvalue, hQvalue⟩

theorem right_angle_maximizer_value {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane}
    (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    sofaArea (π / 2) K = area (gerverSofa P) := by
  obtain ⟨_, hvalue, _⟩ := right_angle_maximizer_certificate hP hbox hK hmax
  exact hvalue

/-- The coercive classification, with the translation fixed by the left support. -/
theorem right_angle_maximizer_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane}
    (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  obtain ⟨hKi, _, hQ⟩ := right_angle_maximizer_certificate hP hbox hK hmax
  let x := toWideTriple (MovingSofaStability.kiExtensionTriple hbox.1 hKi)
  have hcap := wide_zero_deficit_cap hP hbox x hQ
  let a := -(supp K π - supp P.cap π)
  have hcap' : K = Rigid.translate (a, 0) '' P.cap := hcap
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  refine ⟨a, hcap', ?_⟩
  rw [hcap', cap_minus_niche_translate (GerverParams.gm_isConvexBody_cap hP hbox), ← hGset]

/-- The sign and zero-deficit conclusions in one right-angle theorem. -/
theorem right_angle_extremal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    (∀ C, IsCap C (π / 2) → sofaArea (π / 2) C ≤ area (gerverSofa P)) ∧
      (∀ K, IsCap K (π / 2) → MaximizesCap (π / 2) K →
        ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap ∧
          K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P) := by
  constructor
  · intro C hC
    obtain ⟨K, hK, _, _, hmax, _⟩ := exists_maximizing_cap pi_div_two_mem_Ioc
    exact (hmax C hC).trans_eq (right_angle_maximizer_value hP hbox hK hmax)
  · intro K hK hmax
    exact right_angle_maximizer_eq_gerver hP hbox hK hmax

end MovingSofaExtremal
