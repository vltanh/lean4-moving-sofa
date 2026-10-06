module

public import MovingSofaUniqueness.Maximizing
public import MovingSofaStability.CoerciveCertificate

/-!
# Optimality and uniqueness from the coercive certificate

Let `K` be a right-angle cap that maximizes the sofa area. Gerver's cap competes with `K`, so
`|G| ≤ A(K)` (`gerver_le_of_maximizes`); `K` satisfies the injectivity condition
(`isKi_of_maximizes`), so `A(K) ≤ 𝒬(ξ_K)` for its canonical triple `ξ_K` (Baek's Theorem 8.2.4);
and `𝒬(ξ_K) ≤ |G|` by the first part of the coercive certificate. Hence `A(K) = 𝒬(ξ_K) = |G|`
(`right_angle_maximizer_certificate`). The second part of the certificate, at zero deficit, puts
`K` at distance zero from a horizontal translate of Gerver's cap, so `K` is that translate
(`wide_zero_deficit_cap`, `right_angle_maximizer_eq_gerver`). Neither the equality analysis of
`MovingSofaUniqueness.Rigidity` nor the stability theorem is used.

The assembly of `MovingSofaUniqueness.Maximizing` turns these two facts into optimality
(`gerver_sofa_optimal`, `area_le_gerver`) and uniqueness (`image_eq_gerver_of_volume_eq`,
`translate_eq_gerver_of_volume_eq`), the steps of `MovingSofaUniqueness.Main` with this
classification of the maximizing caps.
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory MovingSofaOptimality MovingSofaUniqueness
open MovingSofaStability

namespace MovingSofaExtremal

/-- A triple of the enlarged domain with `𝒬(x) = |G|` has as its cap a horizontal translate of
Gerver's cap: the coercive certificate puts the two caps at distance zero. -/
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
      wideUpperQ P.φ (toWideTriple (kiExtensionTriple hbox.1 hKi)) = area (gerverSofa P) := by
  have hKi := isKi_of_maximizes hP hbox hK hmax
  have hge := gerver_le_of_maximizes hP hbox hmax
  have hA := theorem8_2_4 hbox.1 hKi
  let x := toWideTriple (kiExtensionTriple hbox.1 hKi)
  have hQ := (coercive_certificate hP hbox x).1
  have hAx : sofaArea (π / 2) K ≤ wideUpperQ P.φ x := hA
  exact ⟨hKi, by linarith, by linarith⟩

/-- A maximizing right-angle cap has sofa area `|G|`. -/
theorem right_angle_maximizer_value {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MaximizingValue P :=
  fun _ hK hmax => (right_angle_maximizer_certificate hP hbox hK hmax).2.1

/-- A maximizing right-angle cap is the horizontal translate of Gerver's cap with the same
leftmost abscissa, and its sofa is the same translate of Gerver's sofa. -/
theorem right_angle_maximizer_eq_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) : MaximizingShape P := by
  intro K hK hmax
  obtain ⟨hKi, -, hQ⟩ := right_angle_maximizer_certificate hP hbox hK hmax
  have hcap := wide_zero_deficit_cap hP hbox (toWideTriple (kiExtensionTriple hbox.1 hKi)) hQ
  let a := -(supp K π - supp P.cap π)
  have hcap' : K = Rigid.translate (a, 0) '' P.cap := by
    rw [Rigid.coe_translate]
    exact hcap
  have hGset : gerverSofa P = P.cap \ niche P.cap (π / 2) :=
    theorem2_4_3 (GerverParams.gm_isMonotone hP hbox)
  refine ⟨a, hcap', ?_⟩
  rw [hcap', cap_minus_niche_translate (GerverParams.gm_isConvexBody_cap hP hbox), ← hGset]

/-! ## Optimality -/

/-- Every right-angle cap has sofa area at most `|G|`. -/
theorem right_angle_cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {C : Set Plane} (hC : IsCap C (π / 2)) : sofaArea (π / 2) C ≤ area (gerverSofa P) :=
  Maximizing.right_angle_cap_area_le_gerver (right_angle_maximizer_value hP hbox) hC

/-- The maximizing right-angle caps are the horizontal translates of Gerver's cap. -/
theorem right_angle_maximizes_iff_translate_gerver {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    MaximizesCap (π / 2) K ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap :=
  Maximizing.right_angle_maximizes_iff_translate_gerver hP hbox
    (right_angle_maximizer_value hP hbox) (right_angle_maximizer_eq_gerver hP hbox) hK

/-- A right-angle cap has sofa area `|G|` if and only if it is a horizontal translate of Gerver's
cap. -/
theorem right_angle_sofaArea_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {K : Set Plane} (hK : IsCap K (π / 2)) :
    sofaArea (π / 2) K = area (gerverSofa P) ↔ ∃ a : ℝ, K = Rigid.translate (a, 0) '' P.cap :=
  Maximizing.right_angle_sofaArea_eq_gerver_iff hP hbox
    (right_angle_maximizer_value hP hbox) (right_angle_maximizer_eq_gerver hP hbox) hK

/-- Every moving sofa has area at most `|G|`. -/
theorem area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) : area S ≤ area (gerverSofa P) :=
  Maximizing.area_le_gerver hP hbox (right_angle_maximizer_value hP hbox) hS

/-- **Optimality.** Gerver's sofa is a moving sofa, and every moving sofa has area at most that
of Gerver's sofa: the statement of Baek's Theorem 1.1.1, from the coercive certificate. -/
theorem gerver_sofa_optimal {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      ∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P) :=
  Maximizing.gerver_sofa_optimal hP hbox (right_angle_maximizer_value hP hbox)

/-- Every cap of every angle has sofa area at most `|G|`. -/
theorem cap_area_le_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {C : Set Plane} {ω : ℝ} (hC : IsCap C ω) : sofaArea ω C ≤ area (gerverSofa P) :=
  Maximizing.cap_area_le_gerver hP hbox (right_angle_maximizer_value hP hbox) hC

/-! ## Uniqueness -/

/-- **Uniqueness.** A rotation about the origin followed by a translation maps every moving sofa
with the area of Gerver's sofa onto Gerver's sofa. -/
theorem image_eq_gerver_of_volume_eq {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (heq : volume S = volume (gerverSofa P)) : ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.image_eq_gerver_of_volume_eq hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS heq

/-- **No rotation is needed.** Every moving sofa with the area of Gerver's sofa is a translate of
Gerver's sofa. -/
theorem translate_eq_gerver_of_volume_eq {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S)
    (heq : volume S = volume (gerverSofa P)) :
    ∃ v : Plane, Rigid.translate v '' S = gerverSofa P :=
  Maximizing.translate_eq_gerver_of_volume_eq hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS heq

/-- A moving sofa has the area of Gerver's sofa if and only if a rigid map takes it onto `G`. -/
theorem volume_eq_gerver_iff {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.volume_eq_gerver_iff hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS

/-- A moving sofa has the maximal area if and only if a rigid map takes it onto `G`. -/
theorem isMaximal_iff_image_eq_gerver {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    {S : Set Plane} (hS : MovingSofaOptimality.IsMovingSofa S) :
    (∀ S', MovingSofaOptimality.IsMovingSofa S' → volume S' ≤ volume S) ↔
      ∃ g : Rigid, g '' S = gerverSofa P :=
  Maximizing.isMaximal_iff_image_eq_gerver hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox) hS

/-- **Optimality and uniqueness.** Gerver's sofa is a moving sofa, every moving sofa has at most
its area, and the moving sofas with its area are its rigid images. -/
theorem gerver_sofa_optimal_and_unique {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox) :
    MovingSofaOptimality.IsMovingSofa (gerverSofa P) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, MovingSofaOptimality.IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ g : Rigid, g '' S = gerverSofa P)) :=
  Maximizing.gerver_sofa_optimal_and_unique hP hbox (right_angle_maximizer_value hP hbox)
    (right_angle_maximizer_eq_gerver hP hbox)

end MovingSofaExtremal
