# Dependency contract and audit source

The implementation is in `MovingSofaExtremal`, the lower quantitative modules,
and `SolutionCoercive`. The audit source is
`scripts/AuditCoerciveRoute.lean`. **It has not been executed.** This contract
records intended checks, not a successful dependency or axiom audit.

## Preserved routes

The faithful Baek optimality theorem, the original main uniqueness proof,
the historical `MaximizerRoute`, and the bridge/canonical Challenge solution
remain unchanged. The new declarations have different namespaces and coexist
with them. The audit imports the old routes only for negative controls and
statement comparison; the new theorem modules do not import them.

## Allowed shared mathematics

The coercive route may use Baek's pre-final geometry, fixed-angle compactness
and existence, his intermediate Q construction and reference maximization,
Gerver's explicit geometry, selection/variation/curvature from maximality,
remaining-angle motion, elementary rigid/translation identities, and
regular-closed recovery. It also uses the new residual-energy and cap-distance
estimates. The bridge is used at the external solution layer.

Importing `MovingSofaOptimality.Main` for its intermediate Q/reference results
is not forbidden. Depending on the final optimality declaration in that file
is forbidden. The audit traverses declaration proof bodies rather than treating
every theorem in an imported module as used.

## Forbidden declaration dependencies

### Baek's final optimality

    MovingSofaOptimality.theorem1_1_1
    MovingSofaOptimality.gm_area_le

### Baek's historical balance-derived step-(3) route

    MovingSofaOptimality.theorem1_5_2
    MovingSofaOptimality.theorem4_1_2
    MovingSofaOptimality.theorem4_1_4
    MovingSofaOptimality.theorem4_2_5
    MovingSofaOptimality.theorem6_1_1
    MovingSofaOptimality.theorem6_3_3
    MovingSofaOptimality.theorem6_4_3
    MovingSofaOptimality.corollary6_4_4
    MovingSofaOptimality.theorem6_5_6
    MovingSofaOptimality.theorem8_1_1_balanced

### Entire old proof modules

All declarations owned by the following modules are forbidden, including
private and generated declarations:

    MovingSofaUniqueness.Main
    MovingSofaUniqueness.Rigidity
    MovingSofaUniqueness.Maximizers
    MovingSofaUniqueness.Optimality
    MovingSofaUniqueness.Alternative
    Solution

Forbidding the entire Rigidity module is stronger than forbidding just
`ki_maximizer_equality_conditions`, `capKernel_of_triple_midpoint`, and
`CapKernel.eq_horizontal_translation`. The neutral Mamikon utilities needed
by the quantitative route are now defined separately in
`MovingSofaStability.MamikonFoundation`; they do not alias the old proof.

### Global stability, to prevent circular use of uniqueness

    MovingSofaStability.Statement
    MovingSofaStability.QualitativeEntry
    MovingSofaStability.GlobalStability

The new extremal route uses the lower cap-distance theorem, not the global
stability theorem. The latter's current dependence on existing uniqueness is
preserved and does not enter the new route.

## Positive dependency controls

The audit requires
`MovingSofaExtremal.right_angle_maximizer_eq_gerver` to reach:

    MovingSofaExtremal.isKi_of_maximizes
    MovingSofaExtremal.right_angle_maximizer_certificate
    MovingSofaStability.sharp_wide_cap_distance_bound
    MovingSofaStability.wide_deficit_eq_slack_add_integrals
    MovingSofaStability.EuclideanClose.eq_of_zero

It also requires the new optimality theorem to reach `wideUpperQ_le_gerver`,
the new global uniqueness theorem to reach the coercive cap classification,
and the new formal-conjectures uniqueness theorem to reach both the new
internal theorem and `MovingSofaBridge.gerversSofa_eq`.

Thus absence of old dependencies is not the only test: a route that bypasses
the quantitative mechanism does not meet the contract.

## Negative controls and visibility

The old Baek proof must expose its final assembly and balance-derived steps.
The old main uniqueness area wrapper must expose Baek's final theorem. The
historical maximizing-cap classification must expose both the midpoint kernel
construction and `CapKernel.eq_horizontal_translation`.

The audit uses `import all` for repository intermediate modules so proof bodies
are available under Lean's module system. Traversal visits types and values of
theorems, definitions, and opaque declarations, as well as inductive interfaces.
It does not stop at numbered results. Negative controls must fail the audit
when the expected old proof bodies cannot be seen.

A successful audit still requires inspecting the import/ownership coverage for
the pinned Lean version. Merely writing this traversal is not proof that all
expected bodies are visible or that the traversal itself elaborates.

## Axioms and interface comparison

Every loaded lower-quantitative/extremal declaration and every declaration of
`SolutionCoercive` is checked against the standard-axiom list:

    propext
    Classical.choice
    Quot.sound

The twelve external statement pairs are separately compared by type, after
checking their universe parameters. The new names live in `CoerciveSolution`,
so both solutions can coexist without duplicate global names. The canonical
`Solution` is imported only into the audit for comparison and negative controls.

This is a local same-statement audit, not an already-run Comparator result or
an upstream formal-conjectures submission. No change to the existing Challenge
is required.

## Source and verification boundary

The audit source has been committed but neither it nor the new proof modules
have been compiled. No axiom, dependency, positive-control, negative-control,
or statement-equivalence check is reported as passed. No Lean, Lake, or CI is
to be run until the user explicitly changes the current instruction.
