# Formal-conjectures interface: two internal solution routes

The bridge remains a permanent interface. No bridge file, Challenge definition,
Challenge statement, or canonical solution has been changed by PR #9.

`SolutionCoercive.lean` now contains the intended second solution source.
**It has not been compiled, and its statement-comparison audit has not run.**
No new upstream submission is made by this continuation.

## Preserved canonical route

`Solution.lean` continues to use:

    faithful Baek optimality
    + main equality/CapKernel uniqueness
    + the existing bridge.

This preserves both the formalization's provenance and the currently recorded
external interface. The new route does not replace its proofs.

## Added coercive route

`SolutionCoercive.lean` uses:

    MovingSofaExtremal optimality
    + MovingSofaExtremal coercive uniqueness
    + the SAME bridge and ChallengeDefs.

It does not import `Solution.lean` or `MovingSofaUniqueness.Main`. Its declarations
are in `CoerciveSolution` rather than duplicating the canonical global names.
Consequently both solution families can coexist for dependency and statement
comparison. Their intended theorem types, not their declaration names, agree.

The optional `SolutionCoercive` library is not added to default targets.

## Twelve corresponding statements

| Existing canonical declaration | New declaration in `CoerciveSolution` |
| --- | --- |
| `Baek.gerver_params_exists` | `gerver_params_exists` |
| `Baek.gerver_params_unique` | `gerver_params_unique` |
| `Baek.gerver_sofa_area` | `gerver_sofa_area` |
| `Baek.gerver_sofa_optimal` | `gerver_sofa_optimal` |
| `Baek.gerver_sofa_unique` | `gerver_sofa_unique` |
| `Bridge.isMovingSofa_iff` | `bridge_isMovingSofa_iff` |
| `Bridge.sofaConstant_eq` | `bridge_sofaConstant_eq` |
| `Bridge.gerversSofa_eq` | `bridge_gerversSofa_eq` |
| `FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique` | `gerver_constants_existsUnique` |
| `FormalConjectures.MovingSofa.isMovingSofa_gerversSofa` | `formal_isMovingSofa_gerversSofa` |
| `FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa` | `formal_sofaConstant_eq_volume_gerversSofa` |
| `FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa` | `formal_volume_eq_sofaConstant_iff_congruent_gerversSofa` |

The Gerver-constants result is already proved in the shared definitions/bridge
infrastructure. Reusing it is intentional: independence concerns the extremal
proof, not finding a different construction of Gerver's constants.

## What the bridge still does

The same three semantic correspondences are used:

- moving sofas agree after accounting for initial position and coordinates;
- the sofa constant agrees with the internal supremum of areas;
- Gerver's construction from four constants agrees with the Romik/Baek set.

The existing coordinate map preserves volume. Its realization map transports
the internal rotation/translation witness to the affine-isometry formulation.
The converse direction of the external uniqueness equivalence uses affine
isometries preserving volume, exactly as in the canonical solution.

No alternative hallway, motion, Gerver, congruence, or maximal-area definition
has been introduced to make the new theorem easier.

## Statement and provenance checks

`scripts/AuditCoerciveRoute.lean` imports both solutions for comparison and
negative controls. It compares the types of all twelve pairs by definitional
equality, checks universe parameters, and traverses the new solution's proof
dependencies. The new external uniqueness theorem must reach both the new
internal uniqueness theorem and `MovingSofaBridge.gerversSofa_eq`.

The canonical solution is forbidden as a proof dependency of the new solution;
it is not enough for the latter to be a wrapper around the former. The same
applies to Baek's final optimality theorem and the old main/kernel uniqueness
route. See [DEPENDENCIES.md](DEPENDENCIES.md).

These are committed audit commands, not successful audit results. The existing
Challenge/Comparator workflow is left unchanged; a future adapter may register
the different new names with that workflow after the new files are checked.
The local twelve-pair comparison is not represented as an already-run upstream
Comparator check.

## Upstream integration boundary

The target external uniqueness statement remains
`volume_eq_sofaConstant_iff_congruent_gerversSofa`. The bridge ensures that the
internal representation can be connected to that statement without changing
its definitions. Eventual upstream packaging and acceptance requirements must
be checked against formal-conjectures at submission time; this continuation
does not assume a policy about external dependencies or modify that repository.

Do not expand the Challenge solely to advertise stability. The stability theorem
and puncture sharpness have separate proof sources, and proposing additional
external statements is a distinct task. Keeping the current interface fixed
avoids coupling that task to the new extremal route.

## Verification policy

No Lean, Lake, CI, remote build, or TeX compilation was run. Both newly written
proof terms and the comparison audit may require corrections. Keep the original
verification claims separate until these new artifacts are actually checked.
