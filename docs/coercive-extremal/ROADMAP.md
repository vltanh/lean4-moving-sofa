# Roadmap: coercive extremal framework

This PR is stacked on `research/quantitative-stability`. The initial planning
commits are preserved in history. Implementation has now begun and the core
extremal/bridge route has intended proof-source entry points. See
[IMPLEMENTATION.md](IMPLEMENTATION.md) for the actual module map and limitations.

**No Lean, Lake, CI, remote build, or TeX compilation has been run.** A completed
source milestone is not a successfully elaborated or verified theorem.

## Assets to preserve

The faithful Baek formalization in `MovingSofaOptimality`, the original main
uniqueness/CapKernel proof, the historical maximizing-cap alternative route,
and the bridge/Challenge interface remain available. The new route must not
replace them or silently extend their kernel-verification claims.

Manuscript integration is for the user's other session. The current task is
proof source and dependency separation, not editing the paper.

## Mathematical target

Write M=area(G). On the appropriate right-angle cap/triple domain, the shared
certificate controls both value and shape:

    A(K) <= Q(xi_K) <= M,
    Euclidean cap distance(K, K_G + horizontal shift)
      <= (2 / cos(phi)) * sqrt(M-Q(xi_K)).

For an exact maximizer, Gerver as a competitor gives M<=A(K). The maximality
geometry gives Ki, where the canonical triple and geometric area inequality
are available. Thus A(K)=Q(xi_K)=M, and zero cap distance gives actual cap
identity. Niche translation gives the nonconvex cap-minus-niche identity.

Fixed-angle existence and the remaining-angle motion give global optimality.
Envelope and regular-closed recovery give global uniqueness. The independent
route uses the lower cap coercivity theorem, not the global stability theorem
whose qualitative entry currently invokes uniqueness.

## Milestones and acceptance gates

| Phase | Source status | Remaining acceptance gate |
| --- | --- | --- |
| 1. Neutral dependencies | Written in `MamikonFoundation`, `Geometry`, `HorizontalTranslation` | Elaborate; inspect transitive dependencies |
| 2. Zero-deficit cap rigidity | Written in `CoerciveRigidity` | Check actual use of cap distance and absence of old kernel route |
| 3. Global extremal theorem | Written in `Optimality`, `Uniqueness`, `All` | Elaborate and audit all new declarations |
| 4. Switch global stability to new uniqueness | Optional, deferred | Add translation/pinning adapter after the new route is checked |
| 5. Same formal-conjectures interface | Written in `SolutionCoercive` | Compare all twelve types and check bridge dependencies |
| 6. Route audit | Written in `AuditCoerciveRoute.lean`, NOT RUN | Execute only when compilation is permitted |
| 7. Manuscript integration | Deferred to the user's other session | Reflect actual verification status, not merely source completion |

All acceptance gates involving Lean remain pending under the current explicit
no-compilation instruction.

## Phase 1: neutral dependencies

The implementation preserves the old source files instead of physically moving
their declarations during an uncompiled refactor:

- `MovingSofaStability/MamikonFoundation.lean` supplies neutral square-integral,
  displacement, and canonical-triple facts in the quantitative namespace.
- `MamikonEnergy.lean` imports it instead of the original `Rigidity` module.
- `MovingSofaExtremal/Geometry.lean` supplies maximizing-cap existence,
  maximality-to-Ki, and the remaining-angle turn.
- `MovingSofaExtremal/HorizontalTranslation.lean` supplies elementary niche and
  sofa translation identities.

This duplicates a small amount of neutral infrastructure in separate namespaces
rather than changing the established proof. Later checked deduplication is
optional, not a dependency of the new theorem. No wrapper that calls the old
classification counts as an independent replacement.

## Phases 2 and 3: coercive classification and global assembly

The new `MovingSofaExtremal` entry points are:

    wide_zero_deficit_cap
    right_angle_maximizer_certificate
    right_angle_maximizer_eq_gerver
    right_angle_extremal
    gerver_sofa_optimal
    image_eq_gerver_of_volume_eq
    gerver_sofa_optimal_and_unique
    isMaximal_iff_image_eq_gerver

The key proof explicitly calls `sharp_wide_cap_distance_bound`, rewrites the
Q deficit to zero, and calls `EuclideanClose.eq_of_zero`. It does not call the
old midpoint-equality or CapKernel classification.

The library is separate and optional, so new uncompiled modules do not enter
the existing default uniqueness-library glob. The original default targets
remain unchanged.

## Phase 4: optional stability dependency cleanup

The current global stability source uses the original uniqueness theorem for
qualitative local entry and the zero-deficit case. That is a valid dependency
ordering, not a defect that must be repaired to obtain quantitative stability.

After checking the new extremal route, it is possible to replace those calls
with a translation/pinning refinement of its uniqueness theorem. This optional
change is not implemented here and does not affect the new route's independence:
its own imports stop at cap coercivity, before global stability/local entry.

## Phase 5: bridge and external statements

The canonical `Solution.lean`, all bridge files, and both Challenge files stay
unchanged. `SolutionCoercive.lean` supplies the second route under distinct
`CoerciveSolution` names, allowing both theorem families to coexist.

Its twelve intended statement types are the same as the corresponding canonical
Challenge results. `AuditCoerciveRoute.lean` compares these types; it has not run.
No external formal-conjectures repository has been modified by this work.

## Phase 6: independence audit

The new audit is stricter than the historical maximizing-route audit. It checks
all loaded quantitative/extremal declarations and the second solution, including
private/generated declarations. It traverses intermediate proof bodies and
forbids:

- Baek's final optimality theorem and its final assembly lemma;
- the historical balance-derived step-(3) list;
- all original main uniqueness and Rigidity declarations;
- the old maximizing-cap alternative modules;
- global stability/local-entry/Statement modules and the canonical Solution.

Positive controls require the new cap classification to reach the actual
quantitative deficit and sharp cap-distance theorems. Negative controls require
the older routes to expose their known forbidden dependencies. All twelve
external statement types are compared separately. See
[DEPENDENCIES.md](DEPENDENCIES.md) for the precise contract.

## Phase 7: presentation and merge strategy

Retain the faithful Baek proof. The current new 'second proof of optimality'
material can be absorbed into the wider coercive route rather than removed.
The paper may present optimality, uniqueness, and stability in that natural
order, while explaining the independent zero-deficit derivation as a common
framework, subject to the actual dependency audit.

PR #8's sharpness additions are handed off separately in
`docs/stability/SHARPNESS_HANDOFF.md`. PR #9 merged that handoff without rewriting
its history. Integrate/review #8 first, then rebase or retarget #9 onto the chosen
integration branch without discarding either proof track. Do not merge solely
because top-level theorem source exists.

When explicitly permitted, the next verification stage is elaboration of the
lower certificate, both extremal/solution routes, the new transitive audit, and
the existing preservation audits. Only successful verification permits changing
paper claims from 'proof source' to 'kernel-checked'.
