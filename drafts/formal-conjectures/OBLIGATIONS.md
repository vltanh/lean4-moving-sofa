# Uncompiled draft: explicit proof-obligation inventory

This draft is **incomplete as a Lean proof**, not merely uncompiled. There are
nine intentional admissions in the new source. The absence of `sorry` in the
final target body does not remove its dependence on these admissions. Ordinary
elaboration, API, tactic and version-porting errors can also remain; none has
been ruled out by a Lean run.

## Paper-to-Lean obligations

All six are in `SofaUniqueness/Draft/PaperReductions.lean`.

| ID | Declaration | Mathematical content still to formalize |
| --- | --- | --- |
| P1 | `capKernel_of_mamikon_midpoint` | Split the four cap gaps, establish integrability, obtain a.e. equality of displacement functions, and solve/integrate the support equations including endpoints. |
| P2 | `curvatureBounds_of_isMaxCap` | Compact specified-cap selection, exact finite-angle variations, per-facet error budget, and endpoint-safe weak limits for every maximizer. |
| P3 | `injectivity_of_curvatureBounds` | Curvature-density regularity, absolutely continuous arms, the analytic maximum-deficit bootstrap, and strict inner-corner derivative signs. |
| P4 | `pinnedBounds_of_isMaxCap` | Pinned-strip feasibility, common interior-ball estimates, actual/assigned support comparison, signed defect control, and fixed-atom limits. |
| P5 | `right_angle_motion_of_pinned` | The two-threshold triangle-cut geometry and an explicitly continuous additional motion of the same sofa. |
| P6 | `regularClosed_gerver` | The existing envelope facts imply that the concrete library Gerver sofa is the closure of its interior. |

The draft includes proof scripts for the steps downstream of these statements:
the four-interval kernel matching, recovery of caps and niches as actual sets,
construction of the two containing monotonizations, composition of their rigid
maps, and exact recovery of the original closed equal-volume subset.

The abstract selection comparison and penalty limit are also drafted. They do
not supply the geometric hypotheses of P2 or P4 by themselves.

## Upstream bridge obligations

These three are in `drafts/formal-conjectures/Coordinates.lean.inc`.

| ID | Declaration | Mathematical/API content still to formalize |
| --- | --- | --- |
| B1 | `real_angle_lift` | An identity-start continuous path in E(2) stays orientation-preserving and admits a normalized continuous real angle lift. Pointwise argument selection does not suffice. |
| B2 | `realization_coordinates` | The chosen canonical oriented Euclidean rotation has the library's counterclockwise coordinate formula; translation is applied after rotation. |
| B3 | `realization_continuous` | Continuity of that realization into the exact induced topology on E(2) declared by the upstream file. |

The remaining bridge code supplies coordinate inverses and volume preservation,
transports closedness/connectedness, extends time by a continuous clamp, and
normalizes a library motion by its initial translation so that the resulting
upstream motion starts at the identity. This avoids a false assumption that
an arbitrarily placed library sofa is already in `horizontalHallway`.

## Why no explicit Gerver-parameter conversion is needed

The adapter first turns an upstream maximizer into a library maximizer. To
compare it with every library competitor, the reverse bridge produces an
identity-start upstream placement of that competitor with the same volume.
The definition of `sofaConstant` supplies the comparison.

The same argument applies to upstream's concrete `gerversSofa`, using its
existing moving-sofa and optimality statements. The internal theorem
`globalMax_congruent` then compares those two specified maximizers through a
single internal Gerver witness. No definition-level equality between Gerver's
and Romik's parameterizations is asserted or needed.

## Upstream solved placeholders are separate dependencies

The inspected upstream file contains four pre-existing admissions in previously
solved statements: `GerversSofa.ABφθSpec.existsUnique`,
`isMovingSofa_gerversSofa`, `sofaConstant_eq`, and
`sofaConstant_eq_volume_gerversSofa`. The exporter preserves those statements
and bodies. The target uses the moving-sofa and volume-optimality results;
its concrete constants also depend on the parameter-existence result. It does
not use `sofaConstant_eq` as a proof shortcut.

To obtain a standalone kernel-checked solution with only standard axioms, the
appropriate upstream solved-result proofs must also be supplied rather than
counting their placeholders as verified facts. Their published proof links
are metadata, not proofs imported by this draft.

## Dependency path

```text
upstream target
  -> upstream_maximizer_is_library_maximizer (B1, B2, B3)
  -> globalMax_congruent
     -> actual containing monotonizations and angle extension (P4, P5)
     -> arbitrary-maximizer injectivity (P2, P3)
     -> four Mamikon equalities and support kernel (P1)
     -> exact cap/niche recovery
     -> closed-subset recovery using regularClosed_gerver (P6)
  -> realizeRigid (B2)
```

The reverse implication only needs affine-isometry volume invariance and the
upstream solved equality of the sofa constant and Gerver's volume.

## Checks actually performed

The Python source-export utility has twelve passing synthetic regression tests
for identifier relocation, comment/string preservation, exact-statement
matching, duplicate/circular target rejection, and explicit placeholder
handling. These tests do not parse or elaborate Lean and do not establish any
mathematical theorem. The full exported project has not been compiled or run.

The original library remains in its original namespace. The source overlay
relocates a copy to `SofaLegacy` to avoid the upstream `MovingSofa` collision.
The toolchain mismatch (`v4.35.0-rc3` versus upstream `v4.33.1`) remains explicit;
neither pin is changed or represented as tested.
