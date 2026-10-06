# Coercive extremal route

**Status: intended extremal and bridge proof source is written; no Lean
compilation or verification has been performed.** The new dependency audit is
also source only and has not been executed. The optional global-stability
relink and manuscript integration are deferred.

This branch is stacked on `research/quantitative-stability`. It first merged
PR #8's punctured-sofa sharpness and improved cap coefficient at
`8b25774885537fd6e668f322ba0e710f2ba6ce50`, then implemented the new route.

## Read first

- [IMPLEMENTATION.md](IMPLEMENTATION.md): actual modules, theorem entry points,
  conservative separation from the old proof, and verification limitations.
- [ROADMAP.md](ROADMAP.md): milestone status and remaining acceptance gates.
- [DEPENDENCIES.md](DEPENDENCIES.md): the actual transitive audit contract.
- [FORMAL_CONJECTURES.md](FORMAL_CONJECTURES.md): the twelve corresponding
  statements and unchanged bridge/Challenge interface.

## Mathematical entry points

`MovingSofaExtremal/CoerciveRigidity.lean` determines the value of a maximizing
right-angle cap and then its shape:

    Gerver as competitor + maximality geometry + Q certificate
      -> A(K)=Q(xi_K)=M
      -> zero cap distance by sharp_wide_cap_distance_bound
      -> K is a horizontal translate of K_G.

`MovingSofaExtremal/Optimality.lean` and `Uniqueness.lean` provide:

    MovingSofaExtremal.gerver_sofa_optimal
    MovingSofaExtremal.image_eq_gerver_of_volume_eq
    MovingSofaExtremal.gerver_sofa_optimal_and_unique

The lower cap coefficient is `2 / cos(phi)`, below 2.002 on the source box.
Its numerical value is irrelevant at zero deficit, but using the same theorem
makes the quantitative mechanism explicit. It is not a global sofa constant.

## Proof tracks preserved

The faithful `MovingSofaOptimality` proof, the original main uniqueness proof,
and the historical maximizing-cap alternative remain unchanged. The new route
has separate declarations and does not import the original Rigidity/Main or
historical alternative modules. Shared neutral square/displacement facts are
isolated in `MovingSofaStability/MamikonFoundation.lean` rather than obtained
by importing the old CapKernel proof.

Global stability still uses the original uniqueness theorem for qualitative
entry. The new extremal route does not import global stability, avoiding that
circular route to uniqueness. Switching global entry to the new proof is an
optional subsequent refactor.

## External interface

`SolutionCoercive.lean` supplies a second intended proof of the same twelve
Challenge statements under the distinct `CoerciveSolution` namespace. The
bridge, `Challenge.lean`, `ChallengeDefs.lean`, and canonical `Solution.lean`
are unchanged. Both solution families can coexist.

`scripts/AuditCoerciveRoute.lean` is designed to check standard axioms,
transitive exclusion of the old proof routes, positive use of coercivity,
negative visibility controls, and equality of all twelve statement types.
**None of these checks has been run.**

The new `MovingSofaExtremal` and `SolutionCoercive` libraries are optional and
excluded from existing default targets. No workflow has been changed.

## Handoff boundaries

PR #8's additions are documented separately in
`docs/stability/SHARPNESS_HANDOFF.md`. They were completed in source before this
branch's implementation. The user's other session handles manuscript
integration; this branch does not modify the paper or its verification claims.

No Lean, Lake, CI, remote build, or TeX compilation was run. All commits carry
`[skip ci]`. Successful elaboration, mathematical review, and executed route
and statement audits remain necessary before describing the new work as a
verified independent proof.
