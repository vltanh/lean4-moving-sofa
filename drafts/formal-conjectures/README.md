# Uncompiled formal-conjectures uniqueness draft

Start with the [exact target replacement](Target.lean.inc), the
[library uniqueness assembly](../../SofaUniqueness/Draft/ShapeUniqueness.lean),
and the [complete admission inventory](OBLIGATIONS.md).

**This is an uncompiled, incomplete Lean draft.** The requested theorem has an
explicit proof body with its original statement, but that body depends on nine
intentionally admitted helpers. No successful elaboration, axiom audit, or
solution of the open formal-conjectures theorem is claimed.

No Lean compiler, `lake`, CI runner, or external proof execution was used in
this phase. Commits use `[skip ci]`. Python was used only to test the text/source
export utility, not to check Lean proofs.

## The exact endpoint

The replacement preserves

```lean
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
```

No uniqueness premise, regularity assumption on `s`, new axiom, or asserted
instance is added to the statement. The upstream `research open` category is
retained. The forward implication transfers both specified upstream maximizers
to the library and composes their rigid maps. The reverse implication uses
volume invariance and the upstream solved optimality statement.

## Draft files

| File | Purpose |
| --- | --- |
| [Rigid](../../SofaUniqueness/Draft/Rigid.lean) | Explicit product-coordinate rotations/translations, inverses, composition, volume invariance and closed-set recovery. |
| [Selection](../../SofaUniqueness/Draft/Selection.lean) | Penalized-selection comparison, vanishing-penalty limit, subsequential identification and a negative exact-argmax regression. |
| [CapKernel](../../SofaUniqueness/Draft/CapKernel.lean) | Four-interval support-kernel matching, including the integral middle equation and the horizontal-translation zero mode. |
| [CapGeometry](../../SofaUniqueness/Draft/CapGeometry.lean) | Recover the full cap and its cap-minus-niche sofa as actual translated sets. |
| [PaperReductions](../../SofaUniqueness/Draft/PaperReductions.lean) | Six named paper-to-Lean obligations, numerical cap maximality, and application of the existing Mamikon equality lemmas. |
| [ShapeUniqueness](../../SofaUniqueness/Draft/ShapeUniqueness.lean) | Preserve the actual original sofa through both monotonizations and the additional motion, then recover equality and compare any two maxima. |
| [Coordinates](Coordinates.lean.inc) | Euclidean/product coordinates, measurable volume equivalence and three named motion-bridge obligations. |
| [Motions](Motions.lean.inc) | Both movement conversions, including initial-placement translation and identity-start normalization; transfer of global maximality. |
| [Target](Target.lean.inc) | Replacement for the precise open upstream theorem, with both directions drafted. |

The existing `SetRecovery`, `AffineRecovery`, `SquareGap`, and
`MovingSofa.Optimality.Equality` modules are reused. No new proof holes are added
to those files or to the original optimality development.

## Source-only integration

The inspected upstream file is
`FormalConjectures/Wikipedia/MovingSofa.lean` in
`google-deepmind/formal-conjectures`, with Git blob SHA
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`.

Both projects declare `MovingSofa.hallway` and `MovingSofa.IsMovingSofa`, with
different types. They cannot simply be imported together. The exporter creates
a relocated copy of the old module root and namespace under `SofaLegacy`, then
inserts the adapter before the existing target theorem and replaces its body.
It never imports a theorem module that already imports the target itself.

With an existing local formal-conjectures checkout, source assembly is:

```sh
python3 scripts/export_uniqueness_draft.py \
  --formal-conjectures /path/to/formal-conjectures \
  --output /tmp/sofa-uniqueness-overlay
```

This writes a NEW source-overlay directory. It does not invoke Lean, Lake, git,
or a network service, and it does not edit either source checkout. Its output
contains the complete modified upstream file, the relocated supporting sources,
an augmented copy of the upstream Lake configuration, the legacy license and a
manifest with source hashes and admission counts. Existing default targets and
toolchain pins are preserved. The output directory must not already exist.

The source pin and exact theorem signature are checked before export. A changed
upstream file is rejected for review rather than silently patched. The
transform is lexical, not a Lean parser; the full overlay has not been compiled
or otherwise verified as an elaborating project.

The observed toolchains differ: this library pins `v4.35.0-rc3`, while the
inspected formal-conjectures checkout pins `v4.33.1`. This remains a porting
issue, not a compatibility claim. The exporter does not pretend that namespace
relocation resolves the toolchain mismatch.

## Why the two Gerver definitions need not be equated

Upstream uses `EuclideanSpace ℝ (Fin 2)`, a continuous affine-isometry path, and
an identity starting motion. This library uses `ℝ × ℝ`, a continuous lifted
real angle and an initial translation. The ordinary product norm is NOT the
Euclidean norm, so the coordinate map is treated as a homeomorphism/measurable
equivalence, not as a norm isometry.

A library motion `R_theta p+c(t)` is transferred to an upstream motion on the
initially placed sofa `S+c(0)` using `R_theta(q-c(0))+c(t)`. It starts at the
identity and preserves area. This lets upstream's supremum compare every
library competitor.

The adapter then applies internal uniqueness separately to the given upstream
maximizer and to upstream's concrete `gerversSofa`, using the latter's already
solved moving-sofa and optimality statements. It composes the resulting maps,
avoiding any unjustified definitional equality between the two Gerver paths or
parameter systems. Those upstream solved statements still have their original
placeholders in the inspected catalog source; this is listed separately in the
admission inventory.

## Remaining formal work

P1-P6 cover Mamikon-to-kernel extraction, arbitrary-maximizer curvature bounds,
the arm bootstrap, pinned-strip estimates, the angular extension, and Gerver
regular-closedness. B1-B3 cover real angle lifting, the explicit Euclidean
rotation formula, and continuity in upstream's exact topology.

These are real mathematical formalization obligations, not only anticipated
syntax repairs. `OBLIGATIONS.md` records each declaration, its dependency path,
and the relevant paper argument. Filling them is necessary before the target
can be presented as proved; an admission-free final body is not enough.

## Static tooling tests

Twelve Python tests passed on synthetic source fixtures: namespace and quoted
name relocation, preservation of strings/nested comments/similar identifiers,
code-only admission counting, exact target signature, rejection of circular or
duplicate target usage, and rejection of changed upstream anchors.

```sh
python3 -m unittest discover -s scripts -p 'test_export_uniqueness_draft.py'
```

This command tests source rewriting only. It does not run Lean or validate the
mathematics, the generated imports, or version-specific Mathlib APIs.
