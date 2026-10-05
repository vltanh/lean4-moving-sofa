# Source review of the parallel maximizer-first route

## Status

**Uncompiled draft.** No Lean executable, Lake build, Lean audit, Comparator,
CI run, or workflow dispatch was attempted. The new proof source and its
separate audit still require elaboration and kernel/dependency checking.
There is no claim of a successful build or successful dependency audit.

The paper TeX and PDF are unchanged. The
[paper notes](../paper/optimality-reorganization.md) now recommend a compact
side subsection backed by the separate formalization, not a rewrite of the
main proof. [README.md](README.md) records the current architecture.

## Change of integration policy

The first seven PR commits explored replacing the dependency route inside
`MovingSofaUniqueness/Main.lean` and extending `scripts/Audit.lean`. The later
parallel-route revision undoes those two changes exactly:

| Restored file | Base and restored blob SHA |
| --- | --- |
| `MovingSofaUniqueness/Main.lean` | `e531c44ef935920475f498091ca5b475dabccd77` |
| `scripts/Audit.lean` | `fa1a1f80472a4f2fa5a2a9f365cf7b8e96caa0fc` |

Restoration commit: `b22ab6386b7223e8284fdb16488bc905bec8ad70`.
The source objects came from the pinned base
`1ade045936f32cf76572ee668ed8aa1627772bde`. This preserves the original proof
bodies, statements, imports, audit behavior, and source-line positions.
No history was rewritten; the restoration is a new commit on the same PR.

## What the parallel route contains

`Maximizers.lean` exposes fixed-angle existence, Gerver as a competitor,
injectivity from actual maximality, the value and rigidity of a right-angle
maximizer, and the specified fixed-angle maximizer's right-angle motion.

`Optimality.lean` derives the universal right-angle bound, both directions
of the cap-maximizer and cap-equality classifications, and then the global
area/volume bounds. The all-angle cap bound is a consequence, not an input.

`Alternative.lean` uses only those new bounds to assemble the own-envelope
containment argument, exact-set recovery, the equality-case equivalence,
classification of global maximizers, and `gerver_sofa_optimal_and_unique`.
All its declarations are in `MovingSofaUniqueness.MaximizerRoute`, separate
from the original declarations. It does not invoke the original final
uniqueness theorem.

The short containment assembly is repeated rather than extracted out of
`Main.lean` so that the original implementation remains byte-for-byte intact.
The substantial geometric and analytic proofs remain shared.

## Checks actually performed

The current PR metadata, base file objects, new module sources, relevant
shared theorem signatures, and cumulative changed-file list were inspected.
At code commit `5e6195251943debd6e27c5af919836904cf3bf88`, GitHub's comparison
against the pinned base reported **seven added files and no modified,
deleted, or renamed files**:

- `MovingSofaUniqueness/Maximizers.lean`, `Optimality.lean`, `Alternative.lean`;
- `scripts/AuditMaximizerRoute.lean`;
- the three new architecture, review, and paper-note Markdown files.

Subsequent commits in this revision update only those added documentation
files. Thus the add-only preservation boundary covers every file present
at the base, not just a selected list: Baek's library, all original uniqueness
modules, the original audit, bridge, Challenge/Solution, toolchain, build and
workflow configuration, route tables, and manuscript TeX/PDF remain intact.

The source-level dependency order is `Maximizers -> Optimality -> Alternative`.
None imports the original uniqueness `Main`. The original source files have
no imports of the new modules. Inspection of this source structure is not a
certificate of transitive proof-term independence.

## Separate audit prepared for later execution

`scripts/AuditMaximizerRoute.lean` is a new script, not a modification or
invocation of the original audit. It imports proof bodies with `import all`,
checks standard axioms for every declaration owned by the three new modules,
and traverses types and proof values through repository helpers and numbered
intermediate results. It rejects dependence on:

- `MovingSofaOptimality.theorem1_1_1` or `MovingSofaOptimality.gm_area_le`;
- any declaration owned by `MovingSofaUniqueness.Main`, including its
  bound-dependent wrappers and final uniqueness theorem.

The intended negative controls require detection of `gm_area_le` inside
Baek's original main theorem, Baek's theorem inside the original uniqueness
area wrapper, and the original containment theorem inside the original
uniqueness theorem. The original proofs are imported for these controls and
coexistence checks, not as permitted dependencies of the new proofs.

The script does not run the original audit or write its route table. The
existing audit is left intact and does not import the new modules, so running
only that audit would not certify the added route.

## Remaining verification obligations

A later authorized pass must elaborate the new modules and the added audit,
check their actual theorem types, and run the forbidden-dependency checks.
Namespace resolution, implicit arguments, tactics, and measure conversions
in the new source have not been compiler-checked. The audit implementation
and its negative controls likewise remain untested.

Only after that pass should the paper claim the alternative proof has been
verified, with a new pinned verification commit and dictionary entries.
The existing manuscript sections and their source-line links do not need
refreshing merely because of this add-only change. Historical verification
and registry statements continue to describe the old route; they must not
be silently extended to the parallel route.
