# Uncompiled formal-conjectures uniqueness draft

The requested endpoint is the exact declaration
`MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa` in
`FormalConjectures/Wikipedia/MovingSofa.lean` of
`google-deepmind/formal-conjectures`.

This work is source-only. Do not interpret its presence in the repository as a
successful Lean elaboration or a completed kernel proof. No Lean compiler,
`lake`, CI runner, or external proof execution is used for this draft. Research
commits use `[skip ci]`.

## Integration constraints

The inspected upstream file has Git blob SHA
`59b6ed7eb42e11b208b09539c245da4d3f11ed00`.
It uses `EuclideanSpace ℝ (Fin 2)`, continuous paths in affine isometry
equivalences, and an identity starting motion. This library uses `ℝ × ℝ`, a
lifted real rotation angle, and permits an initial translation. The ordinary
product norm on `ℝ × ℝ` is NOT the Euclidean norm. A coordinate equivalence is
therefore not silently declared an isometry.

Both projects use the namespace `MovingSofa` and declare `hallway` and
`IsMovingSofa`. Their unmodified libraries cannot be imported together. The
source exporter will relocate the legacy module root and namespace, preserving
the original checked sources. The final proof is inserted into the upstream
file, not imported from a module which already imports the target theorem.

The observed toolchains also differ: this repository pins `v4.35.0-rc3`, while
the inspected formal-conjectures checkout pins `v4.33.1`. The draft does not
change either pin or assert compatibility has been checked.

## Avoid an unnecessary Gerver-identification theorem

The adapter will use the upstream solved results that its concrete
`gerversSofa` moves and attains `sofaConstant`. After transferring maximality,
apply the internal uniqueness argument separately to the candidate sofa and to
that concrete Gerver sofa; compose the resulting rigid transformations.

This avoids assuming that two different explicit parameterizations or path
conventions are definitionally equal. It does not assume the open uniqueness
statement. The identity-start requirement is handled by translating a library
sofa to its initial placement and conjugating its motion.

## Proof status

An uncompiled proof script and an admitted proof are different things. Any
intentional `sorry` in the new draft will have an obligation identifier and be
listed in the final inventory. The requested theorem will keep its exact
statement and will not gain a hidden uniqueness hypothesis, a new axiom, or an
unproved typeclass instance. A theorem depending on an admitted helper is still
incomplete, even when its final proof body contains no `sorry`.

The upstream file itself contains placeholders for previously solved results.
Using those named results is an explicit upstream dependency, not a claim that
this adapter removes their placeholders or passes an axiom audit.

The earlier paper manuscript is a guide to the formalization. Its completion
was not Lean verification; formalization obligations remain real work.
