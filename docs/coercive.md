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
([definitions](definitions.md)); [Stability](stability.md) defines the deficit, the normalization and [`EuclideanClose`](../MovingSofaStability/Basic.lean#L119).

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

[`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120) is the conjunction of two theorems of the stability library:
[`MovingSofaStability.wideUpperQ_le_gerver`](../MovingSofaStability/Deficit.lean#L343), from the concavity of `𝒬` and its first variation at Gerver's triple, and
[`MovingSofaStability.sharp_wide_cap_distance_bound`](../MovingSofaStability/CapEstimate.lean#L1061), from the residual energies of the deficit. `shiftedReferenceCap P.cap K` is
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

1. **Maximizing caps** ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean)). A cap of maximal sofa area exists at every angle
   ([`MovingSofaUniqueness.exists_maximizing_cap`](../MovingSofaUniqueness/Maximizing.lean#L44), Baek's Theorems 3.5.5 and 3.5.6); a maximizing right-angle cap satisfies the
   injectivity condition ([`MovingSofaUniqueness.isKi_of_maximizes`](../MovingSofaUniqueness/Maximizing.lean#L61)), through the curvature bounds of the uniqueness proof; and a
   rotated copy of a maximizing monotone sofa of angle `ω < π/2` moves with the right angle
   ([`MovingSofaUniqueness.maximizing_monotone_has_right_angle`](../MovingSofaUniqueness/Maximizing.lean#L77)).
2. **The maximizing right-angle caps** ([`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean)). Their sofa area and the value of `𝒬` at their
   canonical triple are `|G|` ([`MovingSofaExtremal.right_angle_maximizer_certificate`](../MovingSofaExtremal/Main.lean#L43)), and they are the horizontal translates of
   Gerver's cap, with sofas the same translates of `G` ([`MovingSofaExtremal.wide_zero_deficit_cap`](../MovingSofaExtremal/Main.lean#L34),
   [`MovingSofaExtremal.right_angle_maximizer_eq_gerver`](../MovingSofaExtremal/Main.lean#L64)).
3. **Optimality and uniqueness** ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean), [`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean)). One assembly turns the value
   and the shape of the maximizing right-angle caps into optimality and uniqueness, step by step as in
   [`MovingSofaUniqueness/Main.lean`](../MovingSofaUniqueness/Main.lean): [`MovingSofaUniqueness.Maximizing.gerver_sofa_optimal`](../MovingSofaUniqueness/Maximizing.lean#L151) needs the value, and
   [`MovingSofaUniqueness.Maximizing.image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Maximizing.lean#L275) and [`MovingSofaUniqueness.Maximizing.translate_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Maximizing.lean#L287) need both. With step 2 they give
   [`MovingSofaExtremal.gerver_sofa_optimal`](../MovingSofaExtremal/Main.lean#L107), [`MovingSofaExtremal.image_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L121) and [`MovingSofaExtremal.translate_eq_gerver_of_volume_eq`](../MovingSofaExtremal/Main.lean#L129). The second
   proof of optimality ([`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean)) uses the same assembly, with the value from Baek's
   bound and the shape from the equality analysis of [`MovingSofaUniqueness/Rigidity.lean`](../MovingSofaUniqueness/Rigidity.lean).
4. **Stability** ([`MovingSofaStability`](../MovingSofaStability)). The sign of the deficit ([`MovingSofaStability.sofaDeficit_nonneg`](../MovingSofaStability/Global.lean#L32)) and the compactness
   step ([`MovingSofaStability.maximizing_subsequence`](../MovingSofaStability/Global.lean#L377), [`MovingSofaStability.pinned_maximizer_eq_gerver`](../MovingSofaStability/Recovery.lean#L128)) use step 3; the local estimate
   ([`MovingSofaStability.nearby_cap_certificate`](../MovingSofaStability/LocalBound.lean#L756), [`MovingSofaStability.nearby_cap_distance`](../MovingSofaStability/LocalBound.lean#L783)) takes both bounds from the certificate, the distance with
   coefficient `2 / cos φ`, which the rest of the proof carries.

## What the route does not use

[`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) follows the proofs through the bodies of all repository declarations, private and
generated ones included. It checks that none of the 743 declarations of [`MovingSofaExtremal`](../MovingSofaExtremal),
[`MovingSofaStability`](../MovingSofaStability) and [`SolutionCoercive`](../SolutionCoercive.lean) reaches Baek's Theorem 1.1.1, the results of his balance argument
(Theorems 1.5.2, 4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6, Corollary 6.4.4 and Theorem 8.1.1 (2)), a
declaration of the first proof of uniqueness ([`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean), [`MovingSofaUniqueness.Rigidity`](../MovingSofaUniqueness/Rigidity.lean)) or of the second proof of
optimality ([`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean)), or [`Solution`](../Solution.lean); that all use only the standard axioms; that the
optimality and uniqueness of the route ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean), [`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean)) do not reach the stability proof
after the certificate, which uses them; that the route uses the certificate where it should (twenty
positive controls); and that the older proofs do reach what they are known to reach (eight negative
controls, which show that the traversal sees proof bodies).

The route shares the rest of Baek's paper: the reduction to monotone sofas and caps, the existence of
maximizing caps, the injectivity condition, the bound `A(K) ≤ 𝒬(ξ_K)`, and the rotation angle of
Theorem 1.5.1. It also shares the steps of the first proof of uniqueness that do not classify caps:
the curvature bounds, the right-angle motion, and the recovery of the sofa from its area. The
helpers that the first proof and the route both use are in neutral modules:
[`MovingSofaUniqueness/Mamikon.lean`](../MovingSofaUniqueness/Mamikon.lean) (square integrals and Mamikon displacements) and
[`MovingSofaUniqueness/Rigid.lean`](../MovingSofaUniqueness/Rigid.lean) (horizontal translates of caps, niches and sofas).

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

On 6 October 2026 the route was consolidated with the second proof of optimality: the maximizing caps
and the assembly from them to optimality and uniqueness, which both proofs had repeated, are now one
module ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean)); the helpers that the route restated from [`MovingSofaUniqueness.Rigidity`](../MovingSofaUniqueness/Rigidity.lean) moved
to neutral modules; and the route itself is two modules ([`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean), [`MovingSofaExtremal.Unified`](../MovingSofaExtremal/Unified.lean)).
