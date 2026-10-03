# Proof-source status and remaining exact-reference obligations

## Verification boundary

The former nine named local obligations now have explicit Lean proof bodies.
The last two intentional admissions in `Draft/PaperReductions.lean` (P2 and P4)
were removed in this continuation. This is a SOURCE status, not a successful
Lean elaboration or a computed dependency audit.

**The full requested task is not complete.** The exact upstream theorem naming
its `gerversSofa` still needs compliant concrete-reference proofs. The proposed
published reference dependency was rejected after finding `decide +kernel`.
No compilation, CI execution, Comparator run, or independent kernel check has
been performed. Syntax, API, module-resolution and proof errors may remain.

## Former paper-to-Lean admissions: written proof bodies

| ID | Source entry point | Current source |
| --- | --- | --- |
| P1 | `Draft.capKernel_of_mamikon_midpoint` | `MamikonDisplacement`, `TangentEquality`, `SupportKernelEquations`, `MamikonCapKernel`: four separate square gaps, integrability and endpoint-safe support equations. |
| P2 | `Draft.curvatureBounds_of_isMaxCap` | `SelectedCurvature` proves the first half for the specified positive maximizer; `MirroredCurvature` gives the second half including pi and the correct minus-arm. The caller proves positivity by comparison with Gerver's cap. |
| P3 | `Draft.injectivity_of_curvatureBounds` | `CurvatureRegularity` and `InjectivityFromCurvature`: separate one-sided support regularity, absolutely continuous arms and the analytic deficit argument. No global C1 support hypothesis at the top edge is assumed. |
| P4 | `Draft.pinnedBounds_of_isMaxCap` | `PinnedVariation` and `PinnedLimit` use actual selected polygons and their signed defects. Positivity is explicit locally and proved from Gerver's area in `ShapeUniqueness`. |
| P5 | `Draft.right_angle_motion_of_pinned` | `AngleCertificates` and `Draft/AngleExtension`: exact two-threshold geometry and a motion of the same sofa. |
| P6 | `Draft.regularClosed_gerver` | `RegularClosedEnvelope`, `GerverStrictHeight`, and `GerverRegularClosed`: regular-closedness for the concrete paper Gerver set. |

The implementation of the variational selection uses fixed finite penalties
with persistent dyadic support samples. Their total weight is bounded; the
support distance to the specified limit tends to zero. Floating error sums
therefore tend to zero without an inverse-mesh loss. The earlier paper notes'
vanishing continuous penalty is not being silently identified with this
implementation.

## Former bridge admissions: ordinary shared modules

| ID | Source entry point | Current source |
| --- | --- | --- |
| B1 | `Bridge.real_angle_lift` | `Bridge/Orientation` and `Bridge/PathLifting`: determinant sign along an identity-start path and normalized continuous real-angle lifting. Not a pointwise choice of argument. |
| B2 | `Bridge.realization_coordinates` | `Bridge/EuclideanRigid`: construct a Euclidean rotation matrix directly, prove its norm preservation algebraically, and obtain the coordinate formula. The target needs an isometry, not a prescribed construction of it. |
| B3 | `Bridge.realization_continuous` | Continuity into the canonical model's actual induced topology, through the value at zero and the continuous linear part. |

`Bridge/Motions` then gives the two-way relationship, including initial
placement, and proves equality of the two supremum problems independently of
uniqueness. `MovingSofaUniquenessFC/Model.lean` is the one canonical definition layer;
there is no source relocation/exporter step.

## Statements actually provided by the current final source

`MovingSofaUniquenessFC/Final.lean` contains:

- `MovingSofaOptimality.Canonical.maximizers_congruent`: any two canonical moving sofas
  attaining the supremum are congruent as actual sets;
- `MovingSofaOptimality.Canonical.volume_eq_constant_iff_congruent_paper_gerver`: a
  canonical maximizer is congruent to the actual paper Gerver construction;
- `MovingSofaOptimality.Canonical.exists_unique_maximizer_modulo_isometry`: existence
  together with the unique-congruence-class conclusion.

These are not renamed copies of the exact upstream concrete-reference theorem.
The generic reference API takes its motion and optimality facts explicitly and
must not be presented as having proved those facts for an uninstantiated shape.

## Exact-reference obligations still unfinished under the source restrictions

The upstream reference chooses its constants from `ABφθSpec.existsUnique` on
the full non-strict domain `0<=phi<=theta<=pi/4`, `A,B>=0`. The paper library
proves its own parameter existence and uniqueness in a specified small box.
That is not a proof of the upstream global parameter theorem.

A proposed shortcut imported `RuifengCao/sofa-formal` at
`838baca722560f30ea8e60b8c711b20147626175`. Its `Sofa/GerverUnique.lean`, theorem
`mapOK_true`, uses `decide +kernel`; its localization uses an evaluated
branch-and-bound certificate. The alternative inspected GerverSofaLean release
also describes decision-kernel replay. These sources cannot be treated as
meeting the stricter ban merely because their axiom reports may be standard.
The dependency and prototype final import were removed from the active tree.
See [note 21](../../docs/uniqueness/21-reference-dependency-audit.md).

Work already written toward a replacement:

- `ReferenceEquations.lean` gives the exact four-equation predicate, proves
  `3 cos(phi)-cos(theta)>0` on the whole angle triangle, reconstructs A,B,
  derives the two reduced equations, and proves the reconstruction converse.
- `ReferenceBoundary.lean` excludes phi=0 and phi=theta by differentiation and
  the original equations, without interval-certificate evaluation.

Still needed: global existence and uniqueness of the remaining angle roots
under the required proof-method restriction, followed by actual upstream
Gerver motion/optimality proofs or a proved concrete formula correspondence
with the paper Gerver witness. No unproved theorem for these tasks is inserted
into the active proof graph.

## Independent challenge fixtures are not solution assumptions

`MovingSofaUniquenessFC/SharedChallenge.lean` imports only Mathlib and contains one
deliberate target placeholder for the shared canonical statement.
`MovingSofaUniquenessFC/ChallengeUniqueness.lean` preserves the exact upstream
concrete-reference definition and target; its deliberate placeholders are
parameter existence/uniqueness and the exact target.

Neither fixture is imported by `MovingSofaUniquenessFC/Final.lean`. The pre-existing
paper `Challenge.lean` and its comparator remain separate and unchanged.
Statement placeholders are not counted as proofs or imported as facts.

## Comparison and audit configuration

`comparator.shared-uniqueness.json` targets the shared canonical theorem and
compares the hallway, motion and supremum definitions. Its allowlist is
exactly `propext`, `Quot.sound`, `Classical.choice`, with the independent
checker enabled. It has not been executed. It does not certify the exact
upstream `gerversSofa` specialization or the source-level tactic restrictions.

The new source examples in `MovingSofaUniquenessFC/Tests/Endpoints.lean` have not been
run. No Lean test-pass claim, source-wide machine scan, or axiom-closure report
is being asserted. The root remains on Lean 4.35.0-rc3 and the inspected
upstream source on 4.33.1; compatibility remains untested.

The external source exporter and its test script have been deleted, along
with the three generated-insertion fragments. No external process, native
arithmetic certificate, custom axiom, or asserted uniqueness instance is used
to fill the former local admissions. The entire uncompiled source still needs
mathematical review and elaboration before it can be called a verified proof.
