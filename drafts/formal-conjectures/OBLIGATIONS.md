# Proof-source status and verification obligations

## Current boundary

The earlier nine named local obligations P1-P6 and B1-B3 have explicit Lean
proof bodies. The additional exact-reference obligations now also have explicit
source proofs: full-domain parameter existence and uniqueness, parameter
correspondence, integral/path/set correspondence, canonical orientation, and
the concrete reference's motion and optimal volume.

`SofaSubmission/Final.lean` now states the exact upstream theorem over the actual
integral-defined `MovingSofa.gerversSofa`, without additional hypotheses.
The reference-identification chain does not use the new sofa uniqueness theorem.
No deliberate admission was added to fill these reference steps.

**This is source status, not verified formal-proof status.** No Lean, Lake, CI,
Comparator or independent kernel checker was executed. No elaborated dependency
closure or transitive source-policy audit has been computed. The entire source
may still contain elaboration, API, tactic, mathematical or version-porting
errors. These verification obligations remain; their absence cannot be inferred
from a final theorem body containing no `sorry`.

## The exact concrete-reference dependency chain

```text
SofaSubmission.Final: exact upstream uniqueness theorem
  -> SofaSubmission.Uniqueness: shared uniqueness API
  -> SofaSubmission.ReferenceFacts: actual reference motion and optimal volume
     -> Bridge.ReferenceShape: exact coordinate set equality
        -> Bridge.ReferenceRotation: the actual upstream orientation/rotation
        -> ReferencePath: R_t p(t)=x(t), endpoint hallways, exact set equality
           -> ReferenceContacts: X,Y are the actual outer-contact coordinates
              -> ReferenceRadius: integrability and one-sided FTC
           -> ReferenceExistence: full-domain parameter existence and uniqueness
              -> ReferenceUniqueness: monotone residual separation
                 -> analytic localization and explicit derivative bounds
              -> ReferenceFromPaper: explicit witness from the paper solution
                 -> ReferenceParameters and ReferenceSolution
```

`ReferenceDefs.lean` retains the exact upstream full parameter specification,
chosen constants, radius, integrals, path, rotation convention and endpoint
hallways. Its parameter theorem is locally proved by `Reference.spec_existsUnique`.
The catalog's pre-existing solved-result placeholders are NOT proof imports.

## Concrete-reference steps now written

| Step | Source | Content |
| --- | --- | --- |
| Global parameter uniqueness | `ReferenceDomainBounds`, `ReferenceDifferential`, `ReferencePhiLocalization`, `ReferenceResiduals`, `ReferenceSmallBounds`, `ReferenceDerivativeSigns`, `ReferenceUniqueness` | Exclude degenerate boundaries, prove `phi<1/20`, and separate roots by two residuals with complementary monotonicity. No small-box uniqueness premise replaces the full upstream domain. |
| Parameter existence and conversion | `ReferenceParameters`, `ReferenceSolution`, `ReferenceFromPaper`, `ReferenceExistence` | Explicit formulas in both directions; all phase junctions and contacts; a witness from the existing paper solution; the exact nested-product existence-and-uniqueness statement. |
| Integrals and path | `ReferenceRadius`, `ReferenceContacts`, `ReferencePath` | Piecewise integrability, finite-junction a.e. equality, one-sided FTC, exact X/Y normalizations, and the translation-before/after-rotation relation. |
| Exact Euclidean reference | `SofaSubmission.ReferenceDefs`, `Bridge.ReferenceRotation`, `Bridge.ReferenceShape` | The literal chosen reference, actual canonical orientation, both endpoint hallways, and equality of the actual sets under coordinates. |
| Motion and volume | `SofaSubmission.ReferenceFacts` | Canonical identity-start motion and maximal volume derived from the set correspondence and existing paper optimality. |
| Requested target | `SofaSubmission.Final` | `MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa` with the original competitor assumptions and concrete reference. |

The analytic details and dependency direction are documented in [note 22](../../docs/uniqueness/22-reference-correspondence.md).
The rejected external certificate dependency from [note 21](../../docs/uniqueness/21-reference-dependency-audit.md)
remains removed. The new proof does not rehabilitate that dependency or claim
that a standard-axiom report alone enforces the user's tactic restrictions.

## Former paper-to-Lean obligations

| ID | Source entry point | Written implementation |
| --- | --- | --- |
| P1 | `Draft.capKernel_of_mamikon_midpoint` | Four Mamikon square gaps, integrability and endpoint-safe support equations in `MamikonDisplacement`, `TangentEquality`, `SupportKernelEquations`, `MamikonCapKernel`. |
| P2 | `Draft.curvatureBounds_of_isMaxCap` | `SelectedCurvature` and `MirroredCurvature` for the specified maximizer, including normals zero and pi and the correct minus-arm convention. |
| P3 | `Draft.injectivity_of_curvatureBounds` | `CurvatureRegularity` and `InjectivityFromCurvature`: one-sided support regularity, absolutely continuous arms and the analytic deficit argument. |
| P4 | `Draft.pinnedBounds_of_isMaxCap` | `PinnedVariation` and `PinnedLimit`: actual selected polygons and signed defects; the caller proves the required positive area. |
| P5 | `Draft.right_angle_motion_of_pinned` | `AngleCertificates` and `Draft.AngleExtension`: exact angular estimates and a motion of the same sofa. |
| P6 | `Draft.regularClosed_gerver` | `RegularClosedEnvelope`, `GerverStrictHeight`, `GerverRegularClosed`: regular-closedness for the concrete paper Gerver set. |

The variational implementation uses fixed finite penalties with persistent
dyadic samples of bounded total weight. It does not silently identify that
implementation with the earlier paper notes' vanishing continuous penalty.
Actual selected polygons converge to the specified cap, and their summed errors
tend to zero without an inverse-mesh loss.

## Former model bridges

| ID | Source | Written implementation |
| --- | --- | --- |
| B1 | `Bridge.Orientation`, `Bridge.PathLifting` | Determinant sign along an identity-start path and a normalized continuous real-angle lift, rather than pointwise argument selection. |
| B2 | `Bridge.EuclideanRigid` | Construct an isometry with the paper rotation coordinates. The additional `ReferenceRotation` proves the formula for upstream's particular oriented rotation. |
| B3 | `Bridge.EuclideanRigid` | Continuity into the actual induced topology on affine isometries. |

`Bridge.Motions` gives the two-way motion relationship including initial
placement, and equality of the two supremum problems independently of shape
uniqueness. The canonical definitions are shared through `SofaSubmission.Model`.
There is no source relocation/exporter step or hidden initial-placement premise.

## Independent statements and unexecuted configurations

`SofaSubmission.SharedChallenge` and `SofaSubmission.ChallengeUniqueness` are
independent Mathlib-only statement environments. Their intentional target
placeholders are not imported by `SofaSubmission.Final` or its proof dependencies.
The latter also contains the parameter statement placeholder required to define
its independent concrete reference. The solution proves that parameter theorem
in its own environment instead of importing the placeholder.

`comparator.reference-uniqueness.json` now targets both the exact uniqueness
statement and the full parameter theorem, together with the concrete defining
constants, path, rotations, hallways and supremum. The configured permitted
axioms are `propext`, `Quot.sound`, `Classical.choice`, with an independent checker
enabled. `comparator.shared-uniqueness.json` retains the generic comparison.
Neither configuration has been executed. Neither is a source-level tactic audit
or evidence of Palomar acceptance.

`SofaUniqueness/Tests/Reference.lean` records the exact types and correspondence
claims as source examples; these have not run. No test-pass claim is made.

## Remaining verification work, not additional mathematical premises

The source must eventually be elaborated, corrected as needed, compared against
the independent exact statement, and subjected to both a full axiom-closure audit
and the requested source-method audit. None of these actions was performed in
this source-only task. The root uses Lean `v4.35.0-rc3`, while the inspected
upstream repository used `v4.33.1`; the port remains untested.

There is no external reference package, proof-source generator, decision-kernel
certificate, custom uniqueness axiom or asserted uniqueness typeclass instance
introduced by the new reference chain. This description of the written approach
must not be mistaken for an executed transitive audit of every imported theorem.
