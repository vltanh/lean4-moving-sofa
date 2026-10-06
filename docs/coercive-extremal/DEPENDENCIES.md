# Dependency contract for the coercive extremal route

This file records the intended dependency boundaries for the new route. It is a
design contract for later Lean audits; it is not itself a proof or audit result.

## Public theorem families to preserve

The repository should continue to expose all of the following simultaneously.

### Faithful Baek optimality

From \`MovingSofaOptimality\`:

- \`theorem1_1_1\` and its supporting numbered results;
- the same theorem dependencies and corrections already documented by the
  existing route checks.

This route may not be rewritten merely to simplify the new proof.

### Main uniqueness proof

From \`MovingSofaUniqueness.Main\`:

- the current uniqueness theorem;
- the current maximal-sofa characterization;
- the current proof path through Baek optimality and the original
  equality/CapKernel mechanism.

### Coercive extremal proof

New declarations should establish:

- right-angle optimality;
- right-angle rigidity;
- global optimality;
- global uniqueness;
- maximal-sofa characterization;

using the quantitative deficit/coercivity machinery in place of the old
right-angle equality classification.

### Stability

The current stability theorem remains available. It may later use the coercive
uniqueness theorem for qualitative entry, but that change is a second-stage
cleanup and is not required to establish independence of the extremal route.

## Allowed dependencies of the coercive route

The coercive route may use:

- low-level geometry and convex-body infrastructure from
  \`MovingSofaOptimality\`;
- existence of maximizing caps;
- the selection, variation, pinned-bound, angle-extension and curvature
  machinery proved from maximality;
- Gerver's explicit geometry and area bounds;
- Baek's upper-bound functional before his final optimality theorem;
- the new quantitative deficit, residual-energy and cap-coercivity modules;
- elementary rigid-motion, translation, regular-closedness and recovery facts;
- the bridge only at the external solution layer, not inside the geometric
  theorem.

## Forbidden dependencies

The new route is intended to be stronger than the current historical
\`MaximizerRoute\` audit. Its final extremal theorems must not depend transitively
on any declaration in the following groups.

### A. Baek's final optimality theorem

At minimum:

\`\`\`text
MovingSofaOptimality.theorem1_1_1
MovingSofaOptimality.gm_area_le
\`\`\`

### B. Baek's balance-derived construction of step (3)

Preserve the current forbidden list from \`scripts/AuditMaximizerRoute.lean\`:

\`\`\`text
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
\`\`\`

The purpose is to retain the current “maximality replaces balance” distinction.

### C. Main uniqueness proof

All declarations owned by:

\`\`\`text
MovingSofaUniqueness.Main
\`\`\`

must be forbidden for the coercive route.

### D. Old right-angle equality classification

The new right-angle classification must not use the old kernel route. At
minimum forbid:

\`\`\`text
MovingSofaUniqueness.ki_maximizer_equality_conditions
MovingSofaUniqueness.capKernel_of_triple_midpoint
MovingSofaUniqueness.CapKernel.eq_horizontal_translation
MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_eq_gerver
\`\`\`

Depending on the refactor, the audit should also forbid the module that owns
the old classification as a whole.

## Required positive dependencies

An independence audit should not only prove absence of forbidden theorems. It
should also check that the new route really reaches the intended quantitative
mechanism.

The new right-angle classification should transitively depend on declarations
corresponding to:

1. maximality \(\Rightarrow \mathcal K^i\);
2. maximizing value \(\mathcal A(K)=|G|\);
3. cap area deficit \(\Rightarrow\) residual/Q deficit;
4. residual/Q deficit \(\Rightarrow\) support or Euclidean cap distance;
5. zero Euclidean distance \(\Rightarrow\) set equality.

Concrete names may change during refactoring, but likely positive controls are:

\`\`\`text
MovingSofaUniqueness.MaximizerRoute.isKi_of_maximizes
MovingSofaUniqueness.MaximizerRoute.right_angle_maximizer_value
MovingSofaStability.ki_cap_distance_bound
MovingSofaStability.EuclideanClose.eq_of_zero
\`\`\`

After the maximizer-geometry split, the first two should move to the neutral
geometry module and the positive controls should be updated.

## Negative controls

The audit should verify that its dependency traversal is capable of finding:

- \`theorem1_1_1\` through the old main uniqueness proof;
- \`capKernel_of_triple_midpoint\` through the old right-angle classification;
- balance-derived step-(3) declarations through Baek's original proof.

Without these negative controls, an empty forbidden-dependency result would not
establish that proof bodies were visible to the traversal.

## Coexistence checks

The final audit should \`#check\` all of these theorem families at once:

- Baek's original optimality theorem;
- main uniqueness theorem;
- current maximizer-route theorem, if retained;
- coercive optimality theorem;
- coercive uniqueness theorem;
- unrestricted stability theorem;
- formal-conjectures bridge theorem(s).

The intended result is coexistence, not replacement.

## Import-layer goal

The source graph should eventually admit this schematic layering:

\`\`\`text
MovingSofaOptimality
  ├─ faithful final optimality theorem
  └─ pre-final upper-bound / geometry infrastructure
                │
MovingSofaUniqueness
  ├─ Main / old Rigidity
  └─ MaximizerGeometry
                │
MovingSofaStability
  ├─ low coercivity layer
  └─ global stability layer
                │
Coercive extremal route
                │
MovingSofaBridge / Challenge solutions
\`\`\`

The low coercivity layer used by the coercive extremal route must not import the
global stability layer, because global qualitative entry currently invokes
uniqueness. This boundary is essential to avoid a hidden cycle.

## Compilation policy

Until explicitly changed by the user:

- do not run Lean;
- do not run Lake;
- do not dispatch or rerun CI;
- do not claim that the planned audits pass;
- keep \`[skip ci]\` on commits in this branch.

The eventual audit commands belong to the implementation roadmap, not to the
current validation status.
