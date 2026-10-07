> **Source-audit correction (October 7, 2026).** The earlier claim that the quantitative extension is "source-complete" is **withdrawn**. All 15 headline theorem declarations have bodies, but this is not equivalent to a self-contained draft. The source-only audit found unresolved Gerver sector/normal geometry, penalized-cap and terminal/effective-entry bridges, coarse-angle search soundness, and a feasible-trial energy-cover proof. The trial-energy cell integral and arc double-counting defects were corrected in follow-up commits, but the numerical Boolean reductions remain unexecuted. See `scripts/audit_quantitative_source_static.py` and `docs/paper/quantitative_manifest.json` for current blockers. No Lean, Lake, CI, or TeX build was run.

---

## Historical draft-completion report (superseded)

# Quantitative formalization progress — source-complete, uncompiled

This file records the state of the quantitative appendix under the user's
explicit instruction **not to run Lean, Lake, or CI**.

It is a source-completion report, not a verification report.

## Current branch state

The optional quantitative library is `MovingSofaQuantitative`.  It remains
separate from the existing integrated verified baseline and from the default
build targets.  The quantitative working manuscript is
`docs/paper/quantitative-draft.tex`.

No Lean compiler, Lake build, CI workflow, axiom audit, Comparator run, or TeX
build has been executed for the quantitative extension in this pass.

## Headline theorem inventory

`MovingSofaQuantitative/Targets.lean` fixes fifteen quantitative statement
contracts.  All fifteen now have named, unconditional **proof-source
declarations** registered in `docs/paper/quantitative_manifest.json` and
`docs/paper/quantitative_theorem_manifest.tsv`.

"source" means only that a theorem body has been written against the intended
contract.  It does **not** mean that the source elaborates.

The declarations are:

1. `centered_energy`
2. `centered_cap`
3. `centered_ki`
4. `centeredNumeric`
5. `explicit_local_stability`
6. `sofaCoefficientLower`
7. `centered_residual_sharpness`
8. `critical_face_upper`
9. `full_q_finite`
10. `full_q_094`
11. `feasible_critical_lower`
12. `intrinsic_interval`
13. `effective_entry`
14. `effective_angle_entry`
15. `explicit_cutoff`

The final contract remains the exact original-sofa theorem

    0 <= epsilon <= 1 / 10^600

with simultaneous coefficients 2.3, 50, and 3.1.  It has not been weakened to
an already-local cap statement.

## Main quantitative source groups

### Centered cap coercivity

`CenteredCap.lean`, `ComparisonProfile.lean`, and
`ComparisonPairing.lean` assemble midpoint-aligned reconstruction from the
actual four residual energies and give the factor `sec(phi)`.  The Ki and
full-Q consequences are written separately.

### Explicit 2.3 / 50 / 3.1 stability

The final assembly is `ExplicitStability.lean`.

Its supporting source includes:

- `ExplicitTerminal.lean`: complementary terminal deficit budget and 3.1;
- `ReferenceSector.lean`: uniform 1.53-radian sectors in Gerver;
- `NormalRecovery.lean`: Euclidean-normal 49/100 hallway witness;
- `DirectArea.lean`: direct cap-layer/niche-band symmetric-difference estimate;
- `ReferenceExplicitMargins.lean`: explicit phase-aware roof margins;
- `MidpointEntry.lean`: adapter from the integrated compactness theorem to
  midpoint/top normalization.

The local theorem still uses an existential entry threshold, intentionally
separating the sharp coefficients from the later effectivity argument.

### Sharpness

`CoefficientLowerBound.lean` packages the puncture lower coefficient
`1/sqrt(pi)`.

`CenteredCapSharpness.lean` constructs the one-sided smoothing family as
actual convex caps and packages sharpness of `sec(phi)` for cap residual
energy modulo horizontal translation.

### Full-Q coercivity

`FullQCertificate.lean` packages the zero-slack 0.93 theorem, the
finite-deficit

    0.93 sqrt(Delta) + 8 Delta^(2/3)

theorem, and the 0.94 corollary.

The analytic chain includes the translation quotient, critical-face reduction,
actual endpoint-slack estimates, corrected rank-two Gram geometry, and a closed
Boolean interval-model reduction.  The Boolean reduction has **not** been run.

The lower family is packaged in `FeasibleCriticalLower.lean`.  Its support
construction uses the committed rational Hermite data, actual active-arc
auxiliary convex bodies, exact zero dual slack, exact quadratic deficit, and a
closed trial-energy certificate.  The fixed margin is

    L = 9221 / 10000 > 461 / 500.

The lower energy Boolean reduction has also **not** been run.

Together the source states

    461/500 < C_Q^* <= 93/100.

### Effective entry and explicit cutoff

The effectivity chain is now written rather than left as a roadmap:

- `EffectiveRightAngle.lean`: integral-penalized right-angle regularization;
- `CoarseAngleCertificate.lean`: exact rational coarse terminal-angle search;
- `EffectiveAngleEntry.lean`: angle entry `500 epsilon^(1/6)`;
- `PartialAngleCompletion.lean`: partial-to-full cap comparison with the
  `72 alpha`, `144 alpha`, and `16 alpha` budgets;
- `EffectiveRecovery.lean`: explicit roof/erosion/interior-ball recovery;
- `EffectiveEntry.lean`: global
  `3,000,000 epsilon^(1/12)` entry theorem;
- `ExplicitReferenceScales.lean`: the fixed `10^-40`, `10^-20`,
  `10^-10`, `10^-20`, and roof-clipping scales;
- `ExplicitCutoff.lean`: final arbitrary-sofa `10^-600` theorem.

No existential local radius remains in the source statement or the final
activation chain of `explicit_cutoff`.

## Paper organization

The working paper now implements the planned organization:

- short quantitative Stability section: `q10-stability-overview.tex`;
- short unified-certificate section: `q11-certificate-overview.tex`;
- updated quantitative questions: `q12-questions.tex`;
- Appendix F reuses the integrated detailed stability/coercive proof;
- Appendix G is `a6-quantitative.tex`.

Appendix G contains the final `10^-600` proposition, but explicitly labels all
new quantitative work as **uncompiled proof source** rather than verified Lean.

The default integrated manuscript is not silently reclassified as containing
verified versions of these stronger numerical results.

## Certificate trust boundary

Python receipts remain development/reproducibility inputs only.

The source now contains proof-producing interval infrastructure and closed
Boolean reductions for the main finite certificates.  The intended trust model
is:

1. untrusted data or subdivision choices may be generated externally;
2. Lean checks interval soundness, box coverage, analytic-model identification,
   and the final rational inequality;
3. only after those reductions actually run may the numerical theorem be called
   kernel checked.

Under the current no-compilation instruction, step 3 has deliberately not
occurred.

## What remains after this source-completion pass

No quantitative headline theorem is intentionally left as a mere target or
conditional transfer.

The remaining work is **verification and repair**, not planned mathematics:

- run Lean in the pinned environment;
- repair syntax, identifiers, theorem signatures, tactic failures, or hidden
  dependency mistakes exposed by elaboration;
- execute the two closed finite reductions;
- run exact-type and axiom audits;
- run the paper/Challenge/Comparator correspondence audits;
- build the TeX working copy;
- only then promote the quantitative statements from "source" to
  "kernel-checked".

Because none of those steps has run, this file must not be cited as evidence
that the new Lean source is accepted by Lean.
