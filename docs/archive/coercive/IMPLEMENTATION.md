# Coercive extremal route: implementation and handoff

## Status

PR #9 now contains intended Lean proof source for a coercive derivation of
optimality and uniqueness, and a second solution of the existing Challenge
statements through the unchanged bridge. The lower quantitative input includes
PR #8's improved coefficient `2 / cos(phi)`.

**None of the new Lean source has been compiled, elaborated, or kernel-checked.**
The dependency audit and statement-type comparison are written but have NOT
been run. Errors may remain in proof terms, API calls, tactic applications,
imports, or mathematical arguments. This document does not report successful
formal verification or certify the independence claim.

The branch first incorporated PR #8 through merge commit
`68e811cdb371b5f982ef43e48ba5af79dcdad965`, with PR #8 handoff
`8b25774885537fd6e668f322ba0e710f2ba6ce50` as its second parent. The puncture and
sharp-constant additions remain in PR #8 for integration in the other session.

## Public entry points

The new optional library is `MovingSofaExtremal`. Its source entry points are:

| Module | Main declarations |
| --- | --- |
| `Geometry.lean` | `MaximizesCap`, `exists_maximizing_cap`, `isKi_of_maximizes`, `maximizing_monotone_has_right_angle` |
| `HorizontalTranslation.lean` | `niche_translate_horizontal`, `cap_minus_niche_translate`, `sofaArea_translate_horizontal` |
| `CoerciveRigidity.lean` | `wide_zero_deficit_cap`, `right_angle_maximizer_certificate`, `right_angle_maximizer_eq_gerver`, `right_angle_extremal` |
| `Optimality.lean` | `gerver_sofa_optimal`, `cap_area_le_gerver`, `right_angle_sofaArea_eq_gerver_iff` |
| `Uniqueness.lean` | `image_eq_gerver_of_volume_eq`, `gerver_sofa_optimal_and_unique`, `isMaximal_iff_image_eq_gerver` |
| `All.lean` | Import root for the new mathematical route |

All the theorem names above are in `MovingSofaExtremal`. They do not replace
existing names in either older proof route.

## Mathematical assembly

For a maximizing right-angle cap K, Gerver's cap is a competitor, so

    M <= A(K).

The selection/variation/curvature machinery supplies `IsKi K`. Baek's
intermediate geometric estimate gives `A(K) <= Q(xi_K)`. The new wide-domain
certificate gives `Q(xi_K) <= M`. Thus the value and Q deficit are determined:

    A(K) = M,    Q(xi_K) = M.

`wide_zero_deficit_cap` now applies
`MovingSofaStability.sharp_wide_cap_distance_bound`, rewrites the deficit to
zero, and invokes `EuclideanClose.eq_of_zero`. This yields the cap as the
explicit horizontally shifted Gerver cap. The niche translation identity then
gives equality of the nonconvex cap-minus-niche sets.

This step does not call the original midpoint-equality or CapKernel
classification. The quantitative bound, not the final global stability theorem,
is the input.

Fixed-angle existence and the maximality-derived remaining-angle motion give
global optimality. The envelope, rotated motion, second envelope, and regular
closedness argument give global actual-set uniqueness. These final global
steps intentionally share the mathematical reductions of the older route.
The independence sought is independence from Baek's final optimality theorem
and the original equality/CapKernel classification, not independence from all
of Baek's mathematics or from the new maximality geometry.

## Conservative dependency separation

The initial roadmap proposed physically moving shared declarations out of
`MovingSofaUniqueness.Rigidity` and splitting the historical `Maximizers` module.
This implementation instead preserves both original files unchanged while
isolating the required neutral material in new namespaces:

- `MovingSofaStability/MamikonFoundation.lean` contains square-integral algebra,
  tangent displacements, their integrability and linearity, the elementary
  displacement formulas, and canonical triple/reference-value infrastructure.
- `MovingSofaStability/MamikonEnergy.lean` imports that foundation instead of
  `MovingSofaUniqueness.Rigidity`.
- `MovingSofaExtremal/Geometry.lean` contains the independent maximizer geometry.
- `MovingSofaExtremal/HorizontalTranslation.lean` contains elementary translation
  identities without importing the old rigidity module.

These low-level identities are reproduced in the new namespaces, not aliases
that invoke the old proof. Within the quantitative namespace, downstream
unqualified references now resolve to the neutral definitions. Their formulas
have the same mathematical meaning as the old utilities.

This is deliberately a small amount of duplication rather than a risky rewrite
of the established proof under a no-compilation instruction. A future checked
refactor may deduplicate the utilities with compatibility exports, but that is
not necessary for the new route's dependency separation.

The new library lives outside the default-target uniqueness library. Merely
adding a new module to the latter would include it in its existing glob. The
separate `MovingSofaExtremal` library avoids changing that default build scope.

## Dependency graph

    Baek's pre-final geometry and Q machinery
       + selection / variation / curvature / angle extension
                |
          maximizer geometry
                |
          wide Q certificate -------------------------+
                |                                    |
          optimal value                       cap coercivity
                |                                    |
                +-------- zero-deficit cap rigidity --+
                                   |
                        global optimality/uniqueness
                                   |
                      unchanged semantic bridge
                                   |
                    CoerciveSolution Challenge results

The new route does NOT import `MovingSofaStability.GlobalStability`,
`QualitativeEntry`, or the global `Statement` layer. Those currently use the
original uniqueness result. Keeping them out is necessary to avoid circular
use of uniqueness through the global stability theorem.

Baek's `Main` module is still imported for intermediate Q/reference results
that share a source file with his final theorem. A module import is not itself
a proof dependency on every theorem in the module. The new audit therefore
checks transitive declaration dependencies, while separately checking that old
uniqueness/rigidity modules do not enter the independent route.

## Same bridge and same external statements

`SolutionCoercive.lean` imports `ChallengeDefs`, the new extremal theorem, and
`MovingSofaBridge.GerverSofa`. It does not import the canonical `Solution`.

The twelve corresponding statements are declared under `CoerciveSolution`,
with identical intended types but distinct names. This allows both solution
families to coexist in a single environment. The bridge itself is reused, not
rewritten; `Challenge.lean`, `ChallengeDefs.lean`, and all four bridge modules
are unchanged.

The principal external result is

    CoerciveSolution.formal_volume_eq_sofaConstant_iff_congruent_gerversSofa.

The audit compares its type with the existing

    FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa,

and likewise compares the other eleven pairs. This comparison has not been
executed. No new submission to formal-conjectures or change to its definitions
is part of this continuation.

## Audit source

`scripts/AuditCoerciveRoute.lean` includes:

1. Standard-axiom checks on the loaded lower quantitative modules, new extremal
   modules, and `SolutionCoercive`, including private/generated declarations.
2. Transitive traversal through repository proof bodies, not just direct calls
   and not stopping at numbered intermediate theorems.
3. A forbidden set containing Baek's final theorem and the historical
   balance-derived step-(3) list, plus declarations owned by the original
   uniqueness/rigidity/maximizer-route modules, the global stability layer,
   and the canonical `Solution`.
4. Positive controls requiring the new cap classification to reach the actual
   wide deficit identity, sharp cap distance theorem, and zero-distance set
   equality; the external uniqueness result must reach the new internal proof
   and the actual bridge.
5. Negative controls that must find the known forbidden dependencies in the
   older proof routes, so an invisible-body traversal cannot silently pass.
6. Definitional comparison of all twelve corresponding Challenge statement
   types, with universe parameters checked separately.

The audit imports the older routes only for negative controls and coexistence.
The new theorem modules themselves do not import those routes. The audit
source is NOT an audit result; a successful run is a remaining acceptance gate.

## Preserved files and optional follow-up

The faithful Baek library, original uniqueness library, historical alternative
route, bridge, Challenge files, canonical solution, existing audits, and
manuscript are not rewritten by this implementation. Existing default targets
are unchanged. The new library and second solution are optional targets.

The optional roadmap phase that switches global stability's qualitative entry
to the new uniqueness theorem is deferred. It requires a translation/pinning
adapter and should be done only after checking this route; the new proof's
independence does not require changing global stability.

Manuscript integration is explicitly left to the user's other session. The
paper must continue to distinguish source-written results from checked results.
The old proof of optimality should remain as the faithful Baek track; the new
material can be described as a coercive extremal route sharing the lower
certificate with stability, once its proofs and dependency audit are checked.

## Validation actually performed

No Lean, Lake, CI, remote build, or TeX compilation has been run. All commits
carry `[skip ci]`. Source inspection was used to separate dependencies and
preserve the existing interface. No new kernel axiom audit, statement-type
comparison, or whole-repository Lean import check is reported as passed.

PR #8's 179 numerical analytic-formula comparisons remain its own diagnostic
record; they do not validate this new extremal formalization or its audit.
