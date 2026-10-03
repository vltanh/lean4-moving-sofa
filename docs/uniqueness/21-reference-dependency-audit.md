# 21. Rejected reference dependency and exact submission boundary

## Positive result in the current source

The two remaining variational admissions, P2 and P4, have been replaced by
explicit Lean proof scripts. Reflection gives the second curvature inequality,
including its endpoint pi and the correct fMinus convention. The pinned-bound
caller proves positivity from Gerver's area; no premise is added to the final
shape-uniqueness statement.

`SofaSubmission/Final.lean` now states the canonical all-maximizers congruence
theorem and the equivalence with congruence to the concrete paper Gerver witness.
All six paper reductions and the direct model bridges have written proof bodies.
They remain uncompiled: neither elaboration nor their axiom closure is certified.

## Negative result: the proposed concrete-reference provider violates the restriction

I prototyped the exact upstream specialization by importing the existing solved
reference proofs from RuifengCao/sofa-formal at
`838baca722560f30ea8e60b8c711b20147626175`. Its `SofaSubmission/Defs.lean` proves
the upstream parameter theorem and its `SofaSubmission/Solution.lean` proves the
concrete Gerver motion and volume equality. Those facts would specialize the
shared uniqueness theorem without comparing the two explicit Gerver formulas.

A subsequent source inspection found a prohibited operation in that dependency:

- `Sofa/GerverUnique.lean`, theorem `mapOK_true`, has the body `by decide +kernel`.
  This supplies the residual bound used in `maps_tbox`, then `exists_fixed`,
  and ultimately the parameter-existence proof.
- The same file's contraction proof uses `contrOK_target`, also described as a
  kernel-computed interval certificate.
- `Sofa/GerverConst.lean` uses a branch-and-bound certificate to localize every
  solution of the upstream four-equation system; its `check_top` is likewise
  documented as checked by `decide +kernel`.

These references are to the declaration names in the exact pinned source, not
an inference merely from a repository label or an empty search result.

The alternative inspected GerverSofaLean v1.1.0 release also documents
`decide +kernel` for its exact-rational replay. This investigation did not locate
an alternative ready-to-import reference proof meeting the stricter source ban.

A standard-axiom check alone would not reject a `decide +kernel` proof. The
user's source-level restriction is stricter in this respect and must not be
hidden by moving the computation into a dependency. Empty code-search results
are not a dependency audit.

## Action taken

The prototype reference import and package pin were removed from the active
configuration, and the original Mathlib-only manifest was restored. The exact
upstream specialization prototype remains in Git history at `82821bb`; it is
NOT the current accepted proof path. No modified copy of the external source,
unreviewed fork, compiled artifact, or native evaluator is substituted for it.

The source exporter and its synthetic Python tests were removed. The old
coordinate/motion/target insertion fragments were removed as well. The current
publication and shared theorem use ordinary Lean modules and no code generation.

The current `Final.lean` deliberately does NOT take the upstream target's name.
Doing so while switching its reference shape or adding a premise would not solve
the original problem. The exact independent target remains in
`SofaSubmission/ChallengeUniqueness.lean` as a statement fixture, not an imported
solution. Its deliberate statement placeholders are not proof dependencies.

## Remaining work for the exact named target under all restrictions

The shared uniqueness theorem already specializes to any actual reference sofa
once its motion and optimality facts are proved. For upstream's `gerversSofa`,
its definition also depends on the theorem choosing A, B, phi, theta from the
full `ABφθSpec` domain. A compliant source integration must provide:

1. A proof of that full parameter specification's existence and uniqueness,
   without the rejected certificate-evaluation tactics. The paper library's
   `romik_unique` only proves uniqueness in its stated small box and is not a
   substitute for global uniqueness on the upstream domain.
2. The concrete upstream Gerver motion and equality of its volume with the
   supremum, either through audited ordinary Lean reference proofs or through
   a proved formula/parameter correspondence with the paper witness.
3. Successful elaboration, independent declaration comparison and axiom checking
   before asserting a Palomar-verified result. None has been run here.

No additional shape-uniqueness hypothesis has been inserted into the written
source chain. The unfinished parts above concern the exact concrete-reference
integration, its stricter source restrictions, and verification of the entire
uncompiled formalization. Earlier descriptions that reduced all remaining work
to P2/P4 understated this integration issue.
