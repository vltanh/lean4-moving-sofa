# Shared moving-sofa uniqueness: uncompiled source and exact-reference boundary

## Current status

Start with [MovingSofaUniquenessFC/Final.lean](../../MovingSofaUniquenessFC/Final.lean),
[the paper-coordinate assembly](../../MovingSofaUniqueness/Main.lean),
and [the current obligation inventory](OBLIGATIONS.md).

The local source now has explicit proof bodies for all six paper reductions
P1-P6 and the three model bridges B1-B3. In particular the last two intentional
admissions in `Draft/PaperReductions.lean` have been replaced. No Lean compiler,
Lake build, CI runner, Comparator or independent kernel check was run.

**The exact formal-conjectures theorem naming its concrete `gerversSofa` is
NOT complete under the requested prohibition on decision-kernel certificates.**
The current final module proves the shared all-maximizers statement and the
version naming the paper's concrete Gerver formula. It does not take the
upstream theorem's name for a different reference shape.

## Current source endpoints

`MovingSofaOptimality.Canonical.maximizers_congruent` states, in the canonical Euclidean
motion model, that any two sets attaining `sofaConstant` are congruent. There
is no smoothness, injectivity, balancedness or regular-closedness assumption
on either input sofa.

`MovingSofaOptimality.Canonical.volume_eq_constant_iff_congruent_paper_gerver` identifies
a canonical maximizer with `Bridge.point '' MovingSofa.gerverSofa P`, the
actual Gerver construction used in the paper development, for a proved solution
P in the paper's parameter box.

`MovingSofaOptimality.Canonical.exists_unique_maximizer_modulo_isometry` includes actual
existence of a maximizer. It does not infer attainment merely from a supremum.

These are uncompiled proof scripts, not claims of accepted Lean declarations.

## How the two settings share one proof

[MovingSofaUniquenessFC/Model.lean](../../MovingSofaUniquenessFC/Model.lean) contains the exact
canonical hallway predicates, induced topology on affine isometries,
identity-start motion structure, and ENNReal supremum from the inspected
upstream source. It imports only Mathlib. It does not assume upstream's
parameter-existence or optimality theorems.

The publication retains its pair-coordinate presentation under explicit
`MovingSofaOptimality.Paper` kernel names for the two colliding definitions. The ordinary
Lean modules in [Bridge](../../SofaUniqueness/Bridge) establish the coordinate,
measure and motion relationships directly. The coordinate identification is
not falsely treated as an isometry for the ordinary product norm. Initial
placement is explicit when transporting a paper motion to an identity-start
canonical motion.

The core uniqueness proof is used once. The bridge proves equality of the
extremal values independently of uniqueness and transfers specified maximizers
to that proof. It does not choose an unrelated balanced maximizer in place of
the original set.

The old source exporter, its synthetic Python tests, and all three `.lean.inc`
insertion fragments have been deleted. No source-generation step is needed.
The repository's pre-existing documentation utilities are not proof inputs.

## What changed in P2 and P4

[SelectedCurvature](../../MovingSofaUniqueness/Curvature/SelectedCurvature.lean) gives the
first curvature inequality for a specified positive maximizing cap.
[MirroredCurvature](../../MovingSofaUniqueness/Curvature/MirroredCurvature.lean) now reflects it
to the second inequality, taking `[0,pi/2)` to `(pi/2,pi]` and `gPlus` to
`fMinus`. The endpoint pi is included without assuming atom-freeness.

[PinnedLimit](../../MovingSofaUniqueness/Variation/PinnedLimit.lean) supplies the pinned
inequalities for a specified positive maximizer. Its positivity premise is
proved at the shape-theorem caller from equality with Gerver's area. At a right
angle positivity follows by comparison with Gerver's cap itself.

The implementation uses persistent finite dyadic support samples with bounded
total weight and a fixed squared-support penalty. The total floating error is
bounded using the support distance tending to zero. This is not a claim that
exact unpenalized maximizers select every continuum maximizer.

## Exact upstream endpoint: the remaining issue

The requested declaration is still

```lean
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa
```

Once the concrete reference facts are proved in the same definition environment,
its final specialization is the ordinary term

```lean
by
  exact MovingSofa.Canonical.volume_eq_constant_iff_congruent hs
    isMovingSofa_gerversSofa sofaConstant_eq_volume_gerversSofa
```

This term is NOT by itself a completed submission. The catalog's solved-result
placeholders are not proofs, and its constants depend on the full parameter
existence-and-uniqueness theorem.

I prototyped an import of the published reference proofs in
RuifengCao/sofa-formal at `838baca722560f30ea8e60b8c711b20147626175`, but then
found `decide +kernel` in its parameter proof (`mapOK_true`), as well as its
localization-certificate approach. That violates the stricter restriction for
this work even though such proof terms can have only standard axioms. The
reference dependency was removed and the Mathlib-only manifest restored.
The rejected prototype remains only in Git history, not in the active proof.

[Note 21](../../docs/uniqueness/21-reference-dependency-audit.md) records the
finding and the resulting boundary. The exact upstream statement is preserved
as an independent fixture in `MovingSofaUniquenessFC/ChallengeUniqueness.lean`; that
Challenge is not imported by the solution modules.

[ReferenceEquations](../../MovingSofaUniquenessFC/ReferenceEquations.lean) and
[ReferenceBoundary](../../MovingSofaUniquenessFC/ReferenceBoundary.lean) begin the
replacement with ordinary algebra and differentiation. They reconstruct A and
B from the two angles, reduce the four equations to two scalar equations, and
exclude phi=0 and phi=theta. They do NOT yet prove global existence/uniqueness
of those angle roots or identify the two concrete Gerver formulas.

## Comparison configuration and verification limits

[comparator.shared-uniqueness.json](../../comparator.shared-uniqueness.json)
compares `MovingSofaOptimality.Canonical.maximizers_congruent` against the independent
Mathlib-only `SofaSubmission.SharedChallenge` and checks the shared definitions.
The permitted axioms are exactly `propext`, `Quot.sound`, and `Classical.choice`,
with the independent checker enabled. This configuration is unexecuted and does
not target the still-unfinished concrete-reference specialization.

No `sorry` or custom axiom was introduced to close P2/P4 or the model bridges.
The independent Challenge files intentionally contain statement placeholders;
they are not imported into the proof graph. Source examples in
[MovingSofaUniquenessFC/Tests/Endpoints.lean](../../MovingSofaUniquenessFC/Tests/Endpoints.lean)
are unexecuted too. No test-pass claim is attached to them.

The root toolchain remains `v4.35.0-rc3`; the inspected upstream repository
uses `v4.33.1`. A port and full elaboration are still untested. The comparison
configuration is not Palomar certification; further repository packaging and
policy checks also remain before any submission is presented as accepted.
