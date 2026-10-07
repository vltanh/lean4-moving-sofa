# Lean-only numerical proof contract

**Scope:** PR #10, the quantitative stability/coercivity appendix.

## Meaning of certificate

A certificate is a **finite mathematical proof witness checked in Lean**:
an exact rational parameter rectangle, an exact finite cover of that rectangle,
sound outward interval bounds on each cover cell, sound connections to the real
analytic expressions, and a final exact rational inequality. The word does
**not** mean a successful external numerical experiment.

There must be no script-produced theorem premise, imported JSON assertion,
trusted native solver, unchecked numeric axiom, or replacement of a failed
comparison by a historical receipt. In particular **external Python scripts
are not part of the acceptance or trusted verification procedure**.

## Three numerical theorem chains

1. **Full-Q intrinsic upper bound:** `Certificates/CriticalExpression.lean`
   declares `closedCheck` and proves `closedCheck_sound` using the interval
   expression evaluator and binary-cover soundness. `FullQCertificate.lean`
   must prove `closedCheck 128 = true` by ordinary Lean `decide`, and then
   derive `CriticalOperatorBound` using
   `OperatorModelTransfer.operator_of_closed_check`.
2. **Feasible lower trial:** `TrialEnergyCertificate.lean` defines the
   Hermite-residual expression, exact rational mesh sums, and `closedCheck`.
   It must establish `closedCheck = true` by ordinary Lean `decide`.
   Soundness must justify every cell-to-integral bound and the exact
   identification of the computed model with the feasible triple's energy.
3. **Coarse rotation-angle exclusion:** `CoarseAngleCertificate.lean`
   defines rational polygons, rational clipping, a binary search and a
   `closedCheck` over the twenty slabs. Its covering and polygon-model
   theorems must show that acceptance excludes every specified actual
   moving sofa. `closedCheck = true` is to be established inside Lean,
   not asserted by an external script. A box-indexing bug (stride four
   rather than two for paired normal/tangent coordinates) was fixed in
   `599f2d9`; this remains uncompiled.

## Acceptance gates

The numerical result can be called kernel checked **only if all of the
following hold**:

- the analytic-to-expression theorem is accepted by Lean;
- the outward rational and trig enclosure lemmas are accepted by Lean;
- the finite cover/partition soundness lemma is accepted by Lean;
- all exceptional endpoints/zero denominators are dealt with in Lean;
- the closed Boolean reduction is proved true in Lean, by `decide` or
  another kernel-checked proof term;
- its final target theorem's exact type matches the paper statement;
- the axiom audit contains no new project-specific or unsound axioms.

A source file with `by decide` **does not establish** that the reduction
succeeds before elaboration. Under the standing prohibition on Lean/Lake/CI
runs, all three chains remain uncompiled and unverified. This is an important
open gate; it cannot be waived by a JSON file or Python report.

Historical scripts and numerical receipts may remain in the research
directory as **historical diagnostics only**. Nothing in the quantitative
theorem dependency closure may import them or use their pass/fail values.

The mandatory final target is the original-sofa `1/10^600` proposition.
Numerical certification alone does not prove it: its sector, normal, terminal
and global-entry geometry must also have kernel-checked proofs.
