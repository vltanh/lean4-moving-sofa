# Source review of the maximizer-first refactor

## Status

**Uncompiled draft.** No Lean executable, Lake build, Lean audit, Comparator,
CI run, or workflow dispatch was attempted. The new proof terms and audit
extension still require elaboration and kernel/dependency checking. No claim
of a successful build or successful dependency audit is made.

The paper TeX and PDF are unchanged. The integration work is documented in
[`docs/paper/optimality-reorganization.md`](../paper/optimality-reorganization.md).
The implementation boundary is in [README.md](README.md).

## Changes delivered

The new `MovingSofaUniqueness/Maximizers.lean` exposes fixed-angle existence,
comparison with Gerver as a competitor, injectivity for an actual right-angle
maximizer, its value, its cap/sofa rigidity, and a right-angle motion for a
specified maximizing monotone sofa with area at least `11/5`.

`MovingSofaUniqueness/Optimality.lean` derives the right-angle bound and then
the global bound. It does not import the uniqueness entry point. The all-angle
cap bound is a consequence, not an input.

`MovingSofaUniqueness/Main.lean` retains its existing public statements and
uses those newly derived bounds. It adds the `IsMaxCap`-vocabulary wrappers
and `gerver_sofa_optimal_and_unique`. Its containment, regular-closed recovery,
and final width arguments are retained.

`scripts/Audit.lean` now imports both new modules, includes the new route in
its result list, and contains a forbidden-dependency check with a negative
control. These additions are prepared for a later run; they have not been run.

## What was actually reviewed

The GitHub changed-file list and the displayed patches for `Main.lean` and
`scripts/Audit.lean` were inspected against the pinned base
`1ade045936f32cf76572ee668ed8aa1627772bde`. The existing public theorem signatures
in the displayed Main diff are unchanged; changes are imports, proof bodies,
documentation, and added declarations. The exact-set recovery and width proof
bodies remain the same apart from comments.

The audit patch preserves its existing `paperResults`, `uniquenessResults`,
`solutionResults`, and the numbered-paper route extraction. It adds a separate
maximizer result list and tests forbidden dependencies by traversing through
numbered intermediate results, instead of stopping at them. The negative
control requires the old main theorem to expose its use of `gm_area_le` so a
missing proof environment is not silently treated as success.

At code commit `3ef9c27db38a5263b6f3c4d06afc4387423b7114`, comparison of the Git tree
entries with the pinned base confirmed these exact preserved objects:

| Object | Identical Git object at base and code commit |
| --- | --- |
| Entire `MovingSofaOptimality/` tree | `0cd0c6ab09afedd51d5255f78df77aaf2335989a` |
| Entire `MovingSofaBridge/` tree | `e8c8a19516adcf8df9ad0f72a676b0af48572ca3` |
| Entire `.github/` tree | `ee9ce8ff0faf7d70dfa5420c7917ec649b22fd1a` |
| `Challenge.lean` | `9a6d18e67254d255c9c7d2958fc8c0cff4ed5189` |
| `ChallengeDefs.lean` | `8048eca1d7a0daf664a633173b4241eb610420e8` |
| `Solution.lean` | `321a177e771087381c3a7c340018f38be63800da` |
| `lakefile.toml` | `ed6ffd31e893834288c61517dc12c2a1992ef680` |
| `lake-manifest.json` | `8ea991e23b8b32133976a694091ac17093c0f687` |
| `lean-toolchain` | `f0e00b3338bac0d6f050d9a64e277314a9f7830f` |

Baek's route tables, the manuscript sections and its PDF are absent from the
changed-file list. No source-level references to the old final bound are used
in the new proof bodies; mentions in comments explain the boundary. This
inspection is not a proof of transitive declaration independence.

## Remaining verification obligations

The Lean elaborator must check theorem applications, implicit arguments,
namespace resolution, tactics, and measure conversions in the new assembly.
The forbidden-dependency guard must then run successfully on the actual proof
terms. It checks `MovingSofaOptimality.theorem1_1_1` and `gm_area_le` for the
new route and the listed public uniqueness consumers; it intentionally does
not reject their use in Baek's preserved original optimality theorem.

The existing documentation contains line-number links into `Main.lean` that
will need refreshing once the code is stable. The root README, manuscript
verification statements, registry metadata, and recorded base audit describe
the old verified commit, not this uncompiled refactor. They must not be cited
as verification of this branch. Update those claims only after a later
successful verification pass and an intentional paper/metadata revision.
