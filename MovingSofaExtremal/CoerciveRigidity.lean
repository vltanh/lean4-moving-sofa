module

public import MovingSofaExtremal.Geometry
public import MovingSofaExtremal.HorizontalTranslation
public import MovingSofaStability.CoerciveCertificate

/-!
# Maximizing right-angle caps, from the coercive certificate

Let `K` be a right-angle cap that maximizes the sofa area. Gerver's cap competes with `K`, so
`|G| ≤ A(K)` (`gerver_le_of_maximizes`); `K` satisfies the injectivity condition
(`isKi_of_maximizes`), so `A(K) ≤ 𝒬(ξ_K)` for its canonical triple `ξ_K` (Baek's Theorem 8.2.4);
and `𝒬(ξ_K) ≤ |G|` by the first part of the coercive certificate. Hence `A(K) = 𝒬(ξ_K) = |G|`
(`right_angle_maximizer_certificate`). The second part of the certificate, at zero deficit, puts
`K` at distance zero from a horizontal translate of Gerver's cap, so `K` is that translate
(`wide_zero_deficit_cap`, `right_angle_maximizer_eq_gerver`). Neither the equality analysis of
`MovingSofaUniqueness.Rigidity` nor the stability theorem is used.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness
open MovingSofaStability

namespace MovingSofaExtremal

/-- A triple of the enlarged domain with `𝒬(x) = |G|` has as its cap a horizontal translate of
Gerver's cap: the coercive certificate puts the two caps at distance zero. Nothing is said about
the two auxiliary bodies of the triple. -/
theorem wide_zero_deficit_cap {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) (hQ : wideUpperQ P.φ x = area (gerverSofa P)) :
    x.1.1.1 = shiftedReferenceCap P.cap x.1.1.1 := by
  have hd := (coercive_certificate hP hbox x).2
  rw [hQ, sub_self, sqrt_zero, mul_zero] at hd
  exact EuclideanClose.eq_of_zero hd

/-- A maximizing right-angle cap `K` satisfies the injectivity condition, and both its sofa area
and the value of `𝒬` at its canonical triple are `|G|`: `|G| ≤ A(K) ≤ 𝒬(ξ_K) ≤ |G|`. -/
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
  have hQ := (coercive_certificate hP hbox x).1
  have hAx : sofaArea (π / 2) K ≤ wideUpperQ P.φ x := hA
  have hvalue : sofaArea (π / 2) K = area (gerverSofa P) := by linarith
  have hQvalue : wideUpperQ P.φ x = area (gerverSofa P) := by linarith
  exact ⟨hKi, hvalue, hQvalue⟩

/-- A maximizing right-angle cap has sofa area `|G|`. -/
theorem right_angle_maximizer_value {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane}
    (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    sofaArea (π / 2) K = area (gerverSofa P) := by
  obtain ⟨_, hvalue, _⟩ := right_angle_maximizer_certificate hP hbox hK hmax
  exact hvalue

/-- A maximizing right-angle cap is the horizontal translate of Gerver's cap with the same
leftmost abscissa, and its sofa is the same translate of Gerver's sofa. -/
theorem right_angle_maximizer_eq_gerver {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) {K : Set Plane}
    (hK : IsCap K (π / 2)) (hmax : MaximizesCap (π / 2) K) :
    ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap ∧
      K \ niche K (π / 2) = Rigid.translate (a, 0) '' gerverSofa P := by
  obtain ⟨hKi, _, hQ⟩ := right_angle_maximizer_certificate hP hbox hK hmax
  let x := toWideTriple (MovingSofaStability.kiExtensionTriple hbox.1 hKi)
  have hcap := wide_zero_deficit_cap hP hbox x hQ
  let a := -(supp K π - supp P.cap π)
  have hcap' : K = Rigid.translate (a, 0) '' P.cap := by
    rw [Rigid.coe_translate]
    exact hcap
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  refine ⟨a, hcap', ?_⟩
  rw [hcap', cap_minus_niche_translate (GerverParams.gm_isConvexBody_cap hP hbox), ← hGset]

/-- Every right-angle cap has sofa area at most `|G|`, and the maximizing ones are the horizontal
translates of Gerver's cap. -/
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
