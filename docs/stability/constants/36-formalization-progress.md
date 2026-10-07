# Quantitative formalization progress — not complete

This records implementation of roadmap 34 after the user authorized proceeding.
It is deliberately not a completion or verification report.

## Integration and preservation

The quantitative branch now includes the integrated paper libraries at
`859ba93f8bb73ccc4378118a7b47415827710c2f`, through merge
`3635e01821a9c45bb3f5dd8ceedb29b5d098fad9`. The paper, both older uniqueness
routes, faithful Baek formalization, bridge, Challenge, and canonical solutions
were preserved from that baseline. Eleven older uncompiled constants prototypes
were archived byte-for-byte under `docs/archive/constants/lean-source/`, because
they imported modules removed by the integrated refactor.

The new optional library is `MovingSofaQuantitative`. It is separate from the
existing checked-library globs, and `defaultTargets` is unchanged. No workflow
was edited, dispatched, or rerun. All continuation commits use `[skip ci]`.

## What has proof source

`TranslationQuotient.lean` proves the rank-one uniform-approximation criterion by
intersection of scalar intervals, then the exact two-point supremum formula and
attainment of an optimal translation. Zero and sign-changing weights are treated
explicitly; no division by a zero cosine is hidden in the construction.

`Normalization.lean` separates the old left-support pin, midpoint alignment, and
free horizontal alignment. It proves the centered endpoint identities, residual
invariance, support-to-Euclidean-distance adapters for actual caps, and area/deficit
preservation of the original sofa's midpoint/top translation.

`CapQuotient.lean` identifies the geometric horizontal-translation distance with
the scalar quotient and proves attainment. Its operational definition of the
intrinsic Q coefficient uses the infimum of local uniform coefficients. It proves
nonemptiness from the integrated pinned certificate, so the infimum is not being
interpreted through an empty-set convention.

`CenteredKernel.lean` proves the six centered scalar profile identities, their
uniform upper bound, and a generic integral Cauchy--Schwarz estimate from actual
Gram integrals. It also supplies the rational source-box sec(phi) enclosure.
**It does not yet instantiate the actual four-residual kernel and covariance
integrals.** Therefore it is not a completed proof of centered cap coercivity.

`CoefficientLowerBound.lean` contains two proofs at exact registered target types:

- the scalar sec(phi) enclosure;
- the universal coefficient lower bound 1/sqrt(pi), derived from the integrated
  puncture theorem including its every-rigid-alignment lower bound.

All of this is uncompiled proof source. There are no successful Lean/axiom/type
check results for this extension in this session.

## Frozen statements, not assumed results

`Targets.lean` defines fifteen proposition contracts. These are definitions of
what must be proved, not theorem proofs, axioms, or admitted placeholders.
`docs/paper/quantitative_manifest.json` records two targets as `source` and
thirteen as `planned`. No target is recorded as kernel-checked.

The mandatory `Targets.ExplicitCutoff` states the simultaneous 2.3/50/3.1 result
for every original moving sofa with deficit between zero and the exact rational
1/10^600. It does not assume prior entry into a local neighborhood, does not
replace the sofa by a maximizing envelope, and contains no existential radius.

The actual-set, cap-energy, and full-Q deficits are distinct in the target types.
The midpoint and free-translation conclusions are also separate. The angle
conclusion quantifies over every admissible reduced motion.

## A corrected strictness condition

The earlier operational lower statement, 'for every eta there is a small-deficit
example with ratio greater than 461/500', does not alone prove that the asymptotic
coefficient is strictly greater than 461/500. Ratios might converge to that value
from above.

The registered target therefore requires a FIXED L>461/500, valid at arbitrarily
small deficits. `uniform_trial_lower_bound` and
`strict_intrinsic_lower_of_uniform_trial` prove the needed infimum implication.
The future feasible-family construction must supply that uniform margin; neither
a finite numerical sample nor pointwise strict inequalities can replace it.

## What is not implemented yet

The following are still substantive proof-source obligations, not merely pending
compilation of completed final theorems:

1. The concrete centered four-arc reconstruction/Gram identities and final cap
   energy/Q/Ki estimates.
2. Uniform sector and Euclidean-normal recovery for the actual reference boundary,
   the explicit terminal budget, and the combined 2.3/50/3.1 theorem.
3. The actual convex-cap smoothing family and limiting residual sharpness.
4. Critical-face reduction, nonzero-slack estimates, a Lean-sound interval/cover
   verifier and its data, and the continuously feasible lower Q family.
5. Effective penalized global entry, all numerical local geometry radii, and the
   final 10^-600 theorem.
6. The complete baseline-plus-extension paper claim map, proof-preserving TeX
   restructuring, Appendix G, and the final bridge/Comparator updates.

The analytic notes and their Python certificates remain research inputs to these
proofs. Their prior numerical success is not being reclassified as formalization.

## Gate and inventory infrastructure

`scripts/paper_claim_inventory.py` follows literal TeX inputs, ignores comments
and verbatim/listing bodies, preserves locations, groups sublabels with their
statement, and rejects duplicate labels, cyclic inputs, path escapes, and
unhandled dynamic/unbraced inputs. It is an inventory, not a proof checker;
custom macros and unnumbered mathematical prose require manual review.

The existing `docs/paper_routes.tsv` is left intact: it records the Baek source's
route extraction, not a complete numerical-appendix theorem inventory.

`scripts/quantitative_gate.py` separates three actions:

    python scripts/quantitative_gate.py --inventory
    python scripts/quantitative_gate.py --emit /tmp/QuantitativeStatements.lean
    python scripts/quantitative_gate.py --verify

Inventory and emission never create a verification receipt. Full verification
refuses planned targets. On a Lean-enabled machine it checks pinned dependency
revisions, builds the optional library, and runs a generated Lean audit that
compares each proof's exact type with its target and permits only the project's
standard axioms. It checks all declarations owned by the quantitative library,
including intermediates, and binds a successful receipt to source hashes.

`--verify --allow-partial` is explicitly a development check: a successful receipt
still lists all pending targets and cannot be called completion of the appendix.
No such receipt exists yet. Even the full extension gate is not a replacement
for the manual full-paper correspondence and the existing route/Comparator audits.

## Tests actually executed

The committed Python suite passed 24 regression tests. It covers TeX fixtures,
invalid or misleading manifest states, refusal to drop or weaken the cutoff,
missing toolchains producing no receipt, and exact rational verification of the
finite quotient formula in 702 three-point examples with zero/negative weights.

Run:

    python -m unittest discover -s scripts/tests -p test_quantitative_gate.py -v

`formalization-python-tests.json` records the exact tested source hashes. All
three tested Git blob hashes match their committed files. These tests do NOT
check Lean elaboration, the generated Lean audit, geometric arguments, the full
repository claim map, or any new numerical stability theorem.

## Execution blocker and next acceptance step

The current container has no Lean or Lake executable and no installed pinned
Mathlib environment. Direct network installation was unavailable. Fetching an
existing upstream Lean artifact, without starting a workflow, was rejected by
the connector's size limit. A remote execution plugin was suggested, but no
connected Lean-enabled machine was available during this work.

Accordingly no Lean, Lake, CI, axiom audit, Comparator run, or TeX build was
performed, and no complete-paper or kernel verification is claimed. The next
acceptance step is to elaborate these foundations in the pinned environment,
repair any errors, and then implement the six remaining groups above. The paper
continues to state its integrated baseline results until the stronger theorems
actually pass their gates. The requested cutoff has not been dropped.
