module

public import MovingSofaStability.SharpCapDistance

/-!
# The coercive certificate

One estimate for Baek's upper bound `𝒬` on the enlarged domain of triples carries optimality,
uniqueness and stability. For every triple `x` of the enlarged domain, `𝒬(x) ≤ |G|`
(`wideUpperQ_le_gerver`, from the concavity of `𝒬` and its first variation at Gerver's triple),
and the cap of `x` lies within Euclidean Hausdorff distance `(2 / cos φ) √(|G| - 𝒬(x))` of
Gerver's cap, translated horizontally so that their leftmost points have the same abscissa
(`sharp_wide_cap_distance_bound`, from the residual energies of the deficit).

The first part bounds the value of a maximizing right-angle cap, which gives optimality
(`MovingSofaExtremal.gerver_sofa_optimal`). At zero deficit the second part says that such a cap
is a translate of Gerver's cap, which gives uniqueness
(`MovingSofaExtremal.image_eq_gerver_of_volume_eq`). At small deficit both parts give the local
estimate of the stability theorem (`nearby_cap_distance`, `unrestricted_stability`).
-/

@[expose] public section
noncomputable section

open Real Set MeasureTheory
open MovingSofaOptimality MovingSofaUniqueness

namespace MovingSofaStability

/-- **The coercive certificate.** For every triple `x` of the enlarged domain, Baek's upper bound
satisfies `𝒬(x) ≤ |G|`, and the cap of `x` lies within Euclidean Hausdorff distance
`(2 / cos φ) √(|G| - 𝒬(x))` of Gerver's cap translated horizontally. -/
theorem coercive_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ area (gerverSofa P) ∧
      EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
        x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1) :=
  ⟨(wideUpperQ_le_gerver hP hbox x).trans_eq (wideGerver_value hP hbox),
    sharp_wide_cap_distance_bound hP hbox x⟩

end MovingSofaStability
