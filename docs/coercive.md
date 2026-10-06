# The coercive route

[Back to the README](../README.md)

One estimate proves that Gerver's sofa is optimal, that it is unique, and that it is stable. The
library [`MovingSofaExtremal/`](../MovingSofaExtremal) derives optimality and uniqueness from it, and the stability library
[`MovingSofaStability/`](../MovingSofaStability) derives stability from it and from that uniqueness. The route was written by ChatGPT
Pro 6 (pull request #9), without compiling it, and compiled and completed here; no person has reviewed
the argument, and Lean's kernel checks every proof ([verification](verification.md)). Baek's paper does not
contain it.

Throughout, `P` is the solution of Romik's system in the box (`P.IsSolution`, `P.InBox`), `G` is
Gerver's sofa `gerverSofa P`, and the definitions of moving sofas, caps and areas are Baek's
([definitions](definitions.md)); [Stability](stability.md) defines the deficit, the normalization and [`EuclideanClose`](../MovingSofaStability/Basic.lean#L141).

## The certificate

Baek's upper bound `𝒬` is a function of a right-angle cap and two auxiliary convex bodies. The proof
of stability extends it to an enlarged domain of triples, on which the cap may have corners
([Stability](stability.md#the-proof), step 1). On that domain, `𝒬` is at most the area of Gerver's sofa, and
the gap bounds the distance from the cap to Gerver's cap:

```lean
theorem coercive_certificate {P : GerverParams} (hP : P.IsSolution) (hbox : P.InBox)
    (x : WideTriple P.φ) :
    wideUpperQ P.φ x ≤ area (gerverSofa P) ∧
      EuclideanClose ((2 / cos P.φ) * sqrt (area (gerverSofa P) - wideUpperQ P.φ x))
        x.1.1.1 (shiftedReferenceCap P.cap x.1.1.1)
```

[`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1748) is the conjunction of two theorems of the stability library:
[`MovingSofaStability.wideUpperQ_le_gerver`](../MovingSofaStability/Deficit.lean#L481), from the concavity of `𝒬` and its first variation at Gerver's triple, and
[`MovingSofaStability.sharp_wide_cap_distance_bound`](../MovingSofaStability/CapEstimate.lean#L1679), from the residual energies of the deficit. `shiftedReferenceCap P.cap K` is
Gerver's cap translated horizontally so that its leftmost point has the abscissa of the leftmost
point of `K`.

## Optimality, uniqueness and stability

```lean
theorem gerver_sofa_optimal_unique_stable {P : GerverParams} (hP : P.IsSolution)
    (hbox : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧
      (∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P)) ∧
      (∀ S, IsMovingSofa S →
        (volume S = volume (gerverSofa P) ↔ ∃ v : Plane, Rigid.translate v '' S = gerverSofa P)) ∧
      UnrestrictedStability P ∧ TerminalAngleStability P
```

[`MovingSofaExtremal.gerver_sofa_optimal_unique_stable`](../MovingSofaExtremal/Unified.lean#L38): Gerver's sofa is a moving sofa; every moving sofa has at most its area; the
moving sofas with its area are its translates; and the two stability theorems of [Stability](stability.md)
hold. Each part comes from the certificate:

- **Optimality.** Let `K` be a right-angle cap of maximal sofa area `A(K)`. Gerver's cap competes with
  it, so `|G| ≤ A(K)`; `K` satisfies Baek's injectivity condition, so `A(K) ≤ 𝒬(ξ_K)` for its canonical
  triple `ξ_K` (Baek's Theorem 8.2.4); and `𝒬(ξ_K) ≤ |G|` by the first half of the certificate.
  Hence every right-angle cap has sofa area at most `|G|`, and so has every moving sofa (Section 11
  of the [manuscript](paper/README.md)). With Baek's own bound `𝒬(ξ_K) ≤ |G|` in place of the certificate,
  the same argument is the second proof of optimality of [`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean), which a remark at
  the end of Section 8 of the manuscript describes.
- **Uniqueness.** For the same `K`, `𝒬(ξ_K) = |G|`, so the second half of the certificate puts `K` at
  distance zero from a horizontal translate of Gerver's cap: `K` is that translate. The rest is the
  first proof of uniqueness: a moving sofa of area `|G|` lies, after a rigid motion, in a right-angle
  monotone sofa of area `|G|`, whose cap maximizes the sofa area; that sofa is a translate of `G`,
  and as `G` is the closure of its interior, the rigid image of the sofa is `G`. The rigid motion turns
  by less than a right angle and `G` is wider than one in every direction but the vertical, so it is
  a translation.
- **Stability.** The proof of stability uses the certificate for the local estimate near Gerver's cap,
  and the optimality and uniqueness above for the sign of the deficit and for the compactness step
  that brings every sofa of small deficit near Gerver's.

So the first half of the certificate bounds the value, its second half at zero deficit fixes the shape,
and at small deficit it bounds the distance.

## The proof

1. **Maximizing caps** (`Geometry`). A cap of maximal sofa area exists at every angle
   (`MovingSofaExtremal.exists_maximizing_cap`, Baek's Theorems 3.5.5 and 3.5.6); a maximizing right-angle cap satisfies the
   injectivity condition (`MovingSofaExtremal.isKi_of_maximizes`), through the curvature bounds of the uniqueness proof; and a
   rotated copy of a maximizing monotone sofa of angle `ω < π/2` moves with the right angle
   (`MovingSofaExtremal.maximizing_monotone_has_right_angle`).
2. **The maximizing right-angle caps** (`CoerciveRigidity`, `HorizontalTranslation`). Their sofa area
   and the value of `𝒬` at their canonical triple are `|G|` ([`MovingSofaExtremal.right_angle_maximizer_certificate`](../MovingSofaExtremal/Main.lean#L43)), and they are the
   horizontal translates of Gerver's cap, with sofas the same translates of `G`
   ([`MovingSofaExtremal.wide_zero_deficit_cap`](../MovingSofaExtremal/Main.lean#L34), [`MovingSofaExtremal.right_angle_maximizer_eq_gerver`](../MovingSofaExtremal/Main.lean#L64)).
3. **Optimality** (`Optimality`): [`MovingSofaExtremal.gerver_sofa_optimal`](../MovingSofaExtremal/Main.lean#L107), through `MovingSofaExtremal.right_angle_area_le_gerver` and, for a sofa of area at
   least 2.2 and its rotation angle from Baek's Theorem 1.5.1, `MovingSofaExtremal.area_le_gerver_of_large`.
4. **Uniqueness** (`Uniqueness`): [`MovingSofaExtremal.image_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L121) and [`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L129), step by step as in
   [`MovingSofaUniqueness/Main.lean`](../MovingSofaUniqueness/Main.lean), with the classification of step 2 in place of the equality
   analysis of [`MovingSofaUniqueness/Rigidity.lean`](../MovingSofaUniqueness/Rigidity.lean).
5. **Stability** ([`MovingSofaStability`](../MovingSofaStability)). The sign of the deficit ([`MovingSofaStability.sofaDeficit_nonneg`](../MovingSofaStability/Global.lean#L36)) and the compactness
   step ([`MovingSofaStability.maximizing_subsequence`](../MovingSofaStability/Global.lean#L498), [`MovingSofaStability.pinned_maximizer_eq_gerver`](../MovingSofaStability/Recovery.lean#L142)) use steps 3 and 4; the local estimate
   ([`MovingSofaStability.nearby_cap_certificate`](../MovingSofaStability/LocalBound.lean#L1121), [`MovingSofaStability.nearby_cap_distance`](../MovingSofaStability/LocalBound.lean#L1160)) takes both bounds from the certificate, the distance with
   coefficient `2 / cos φ`, which the rest of the proof carries.

## What the route does not use

[`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) follows the proofs through the bodies of all repository declarations, private and
generated ones included. It checks that none of the 958 declarations of [`MovingSofaExtremal`](../MovingSofaExtremal),
[`MovingSofaStability`](../MovingSofaStability) and [`SolutionCoercive`](../SolutionCoercive.lean) reaches Baek's Theorem 1.1.1, the results of his balance argument
(Theorems 1.5.2, 4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6, Corollary 6.4.4 and Theorem 8.1.1 (2)), a
declaration of the first proof of uniqueness ([`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean), [`MovingSofaUniqueness.Rigidity`](../MovingSofaUniqueness/Rigidity.lean)) or of the second proof of
optimality (`MovingSofaUniqueness.Maximizers`, `.Optimality`, `.Alternative`), or [`Solution`](../Solution.lean); that all use only the standard
axioms; that the optimality and uniqueness of the route do not reach the stability theorem, which uses
them; that the route uses the certificate where it should (twenty positive controls); and that the
older proofs do reach what they are known to reach (eight negative controls, which show that the
traversal sees proof bodies).

The route shares the rest of Baek's paper: the reduction to monotone sofas and caps, the existence of
maximizing caps, the injectivity condition, the bound `A(K) ≤ 𝒬(ξ_K)`, and the rotation angle of
Theorem 1.5.1. It also shares the steps of the first proof of uniqueness that do not classify caps:
the curvature bounds, the right-angle motion, and the recovery of the sofa from its area.

Three modules prove again results of modules that the route must not import, so that the audit can
exclude those modules whole: `MovingSofaExtremal/Geometry.lean` those of
`MovingSofaUniqueness/Maximizers.lean` on maximizing caps,
`MovingSofaExtremal/HorizontalTranslation.lean` and
`MovingSofaStability/MamikonFoundation.lean` translation identities and Mamikon displacements of
[`MovingSofaUniqueness/Rigidity.lean`](../MovingSofaUniqueness/Rigidity.lean).

## A second solution of the Challenge

[`SolutionCoercive.lean`](../SolutionCoercive.lean) proves the fifteen theorems of [`Challenge.lean`](../Challenge.lean) again, through the route, in the
namespace `CoerciveSolution`: optimality and uniqueness from [`MovingSofaExtremal`](../MovingSofaExtremal), stability from
[`MovingSofaExtremal.gerver_sofa_optimal_unique_stable`](../MovingSofaExtremal/Unified.lean#L38), and the bridge to formal-conjectures as in [`Solution.lean`](../Solution.lean). The audit checks that each
theorem has the type of the theorem of [`Solution.lean`](../Solution.lean) with the same name after the namespace, for
example [`CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa`](../SolutionCoercive.lean#L148) for formal-conjectures' open statement. Comparator checks
[`Solution.lean`](../Solution.lean), whose stability theorems now also go through the route.

## The Lean code and the pull request

ChatGPT Pro 6 wrote the route, the module `MamikonFoundation`, [`SolutionCoercive`](../SolutionCoercive.lean) with twelve statements,
and the audit, without compiling or running them. One proof did not compile (a `change` in
`HorizontalTranslation` whose two sides are not definitionally equal, now a rewrite) and one linter
warning remained. The pull request left one step for later, which was done here: the certificate is now
one theorem; the route proves that no rotation is needed; the stability library takes its four uses of
the earlier proofs (the sign of the deficit, the compactness step, the pinned maximizer, and the lemma
that a moving sofa lies in a strip of height one, now in [`MovingSofaUniqueness/Rigid.lean`](../MovingSofaUniqueness/Rigid.lean)) from the route
or from neutral modules, and its local estimate from the certificate; the packaged theorem states the
three results; [`SolutionCoercive`](../SolutionCoercive.lean) covers the fifteen statements; and the audit was rewritten for the
whole route and run. The pull request's notes, written before the compilation, are in
[`docs/archive/coercive/`](archive/coercive).
