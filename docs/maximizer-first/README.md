# Parallel maximizer-first optimality and uniqueness

## Status and scope

This work extends PR #5, based on `paper/uniqueness-arxiv` at
`1ade045936f32cf76572ee668ed8aa1627772bde`. The new Lean sources and audit are
**uncompiled and not kernel-checked in this work**. No Lean build, Lean audit,
Comparator run, or CI/workflow dispatch has been attempted. All commits use
`[skip ci]`. Historical verification of the base commit does not certify the
new route.

The integration policy is now **parallel formalization, minimal paper
integration**. The earlier PR revision redirected the original uniqueness
entry point and changed the existing audit; those changes have been undone.
`MovingSofaUniqueness/Main.lean` and `scripts/Audit.lean` are restored to their
exact base blobs, not just to equivalent statements. The cumulative change
against the base is additions only.

## Two proof routes

The original route is unchanged:

```text
Baek's original optimality proof
  -> MovingSofaUniqueness.Main
  -> the existing Challenge/Solution and bridge statements
```

The new route is separate:

```text
shared intermediate Baek and uniqueness machinery
  -> MovingSofaUniqueness.Maximizers
       actual maximality -> geometry -> value -> cap rigidity
  -> MovingSofaUniqueness.Optimality
       right-angle bound -> global bound -> all-angle cap bound
  -> MovingSofaUniqueness.Alternative
       the given sofa's own envelopes -> exact-set equality case
```

Import `MovingSofaUniqueness.Alternative` to use the complete parallel route.
Its declarations are in `MovingSofaUniqueness.MaximizerRoute`. The new modules
do not import the original uniqueness `Main`, and the original route does
not import them. Short containment-assembly proofs are repeated locally to
avoid coupling the two final proof paths; the substantial selection,
variation, curvature, Mamikon, and regular-closedness proofs are shared.

## Public statements of the new route

All names below have prefix `MovingSofaUniqueness.MaximizerRoute`.

| Declaration | Role |
| --- | --- |
| `exists_maximizing_cap` | Fixed-angle existence and cap/sofa comparison |
| `isKi_of_maximizes` | Injectivity from actual maximality |
| `right_angle_maximizer_value` | Determine the optimal value by opposite comparisons |
| `right_angle_maximizer_eq_gerver` | Identify the maximizing cap and its sofa |
| `right_angle_maximizes_iff_translate_gerver` | Both directions of the maximizer classification |
| `right_angle_sofaArea_eq_gerver_iff` | Equality cases of the right-angle bound |
| `right_angle_optimality_and_rigidity` | Universal cap bound and its equality characterization |
| `maximizing_monotone_has_right_angle` | Motion from maximality and area at least `11/5` |
| `gerver_sofa_optimal` | Feasibility and the global volume bound |
| `image_eq_gerver_of_volume_eq` | Recover the original closed sofa as a set |
| `volume_eq_gerver_iff` | The exact-set equality case in both directions |
| `gerver_sofa_optimal_and_unique` | Feasibility, optimality, and uniqueness together |
| `isMaximal_iff_image_eq_gerver` | Classification of global maximizing sofas |

Maximality is written with the primitive hypotheses `IsCap K omega` and
`forall C, IsCap C omega -> sofaArea omega C <= sofaArea omega K`. This avoids
importing the original `IsMaxCap` definition from `Main.lean`.

## Preservation boundary

All files present at the pinned base are left unchanged in the cumulative PR
diff, including the complete `MovingSofaOptimality/` library, all eight original
uniqueness modules, `scripts/Audit.lean`, the bridge, Challenge/ChallengeDefs/
Solution, toolchain, build configuration, workflow files, Baek's route tables,
and the manuscript's TeX and PDF. New modules are added alongside the originals.

The distinction between imports and proof dependencies matters. The shared
`Rigidity.lean` imports `MovingSofaOptimality.Main` because that file contains
`gerverTriple` and `corollary8_5_8`. Baek's final theorem can therefore be in
the environment without being used in a new proof. Independence from the
final theorem must be checked transitively, not inferred from file names or
an axiom list.

## Separate audit, prepared but not run

`scripts/AuditMaximizerRoute.lean` imports both routes with proof visibility and
checks all declarations owned by the three added modules. It rejects
non-standard axioms and transitive dependence on:

- `MovingSofaOptimality.theorem1_1_1` and `MovingSofaOptimality.gm_area_le`;
- every declaration owned by the original `MovingSofaUniqueness.Main`.

The traversal continues through numbered intermediate results and private
helpers. Negative controls require it to detect the old bounds inside the
original proofs. The script is separate from the unchanged original audit:
passing the original audit alone would not establish the new route's
independence. Both the script and its intended checks still need verification.

For a later authorized pass, explicitly build the new entry point and run the
separate audit; this work has not executed either command:

```sh
lake build MovingSofaUniqueness.Alternative
lake env lean scripts/AuditMaximizerRoute.lean
```

## Paper and attribution

[Paper notes](../paper/optimality-reorganization.md) describe a compact
"Optimality revisited" subsection and provide a proof outline. The main
uniqueness narrative can continue to use Baek's original optimality theorem;
there is no need to reroute or rewrite it to record the alternative result.

The mathematical claim is a **maximizer-first strengthening of Baek's
argument**, using his intermediate results and characterizing the equality
cases. It is not independent of his methods. Uniqueness is not automatic from
concavity: selection, Mamikon-kernel rigidity, and set recovery remain
substantive. Fixed-angle existence is an explicit input; a statement about
every maximizer alone does not assert that a maximizer exists.

[Review status](REVIEW.md) distinguishes source-level preservation checks from
the compilation and proof-dependency audit that remain outstanding.
