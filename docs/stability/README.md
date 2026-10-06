# Stability of Gerver's sofa: analytic argument and Lean source

**Status: end-to-end Lean proof source is now written for the unrestricted
stability and terminal-angle targets. It has not been compiled, elaborated,
or kernel-checked.** The analytic argument has not received independent
review. The PR remains draft; possible API, tactic, type, or mathematical
errors must not be mistaken for verified results.

Start with [FORMALIZATION.md](FORMALIZATION.md) for the current source route
and verification boundary, and
[GlobalStability.lean](../../MovingSofaStability/GlobalStability.lean) for the
headline declarations. [All.lean](../../MovingSofaStability/All.lean) imports
all 72 other stability modules. The earlier notes 01--09 give the mathematical
argument and its development history.

This work started from `paper/uniqueness-arxiv` at
`51c9be18d5b50d45561bfb93cb82d1aabca549bc`, preserving the incorporated
alternative optimality route. It is separate from numerical-discovery PR #6.
Changes are confined to `docs/stability/`, `MovingSofaStability/`, and the
optional, non-default library registration in `lakefile.toml`. Existing
verified libraries, audits, workflows, and manuscript files are unchanged.
No Lean, Lake, CI, remote build, or TeX compilation was run. Every research
commit carries `[skip ci]`.

## Headline source declarations

```lean
theorem unrestricted_stability {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P

theorem terminal_angle_stability {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P
```

These now have proof terms in `GlobalStability.lean`. The propositions in
`Statement.lean` are no longer merely targets with no assembling theorem.
No injective-envelope or stability hypothesis is supplied to either final
declaration. The source supplies the local geometric certificates, terminal
comparison, qualitative entry, and uniform choice of constants.

Write M=area(G) and epsilon=M-area(S). The targets assert that, for every
sufficiently near-optimal moving sofa S,

    d_H(S_hat,G) <= C sqrt(epsilon),
    area(S_hat symmetric_difference G) <= C_area sqrt(epsilon).

They concern the original actual nonconvex sets, not just caps or convex
hulls. No smoothness, curvature-density, injectivity, monotonicity, or
special-envelope hypothesis is imposed on S. In the manuscript's
initial-horizontal-strip convention, S_hat is a translation pinned by

    h_S_hat(pi/2)=1,     h_S_hat(pi)=h_G(pi).

For every admissible reduced rotation angle omega in [arccos(5/11),pi/2],
the second target gives

    0 <= pi/2-omega <= C_angle*epsilon.

The global constants and entry threshold are existential, not effectively
computed. `EuclideanClose` expresses both directed Euclidean distance bounds
with witnesses in the actual sets. The hyperspace's product metric is used
only for topology, with an explicit conversion factor.

## What completes the source route

### The nonsmooth algebraic certificate

The wide domain retains the original linear constraints on the cap and two
tail bodies, but permits curvature atoms. `WideGerverCertificate.lean` and
`WideResidualEnergy.lean` derive the exact deficit identity

    M-Q(xi) = nonnegative dual slack + six difference-square energies.

Only the reference Gerver core is differentiated in the first variation.
All cut and endpoint atoms are retained in the area bookkeeping. Dropping
the two nonnegative auxiliary-body terms controls cap energy without claiming
strict concavity in every triple variable.

### Cap coercivity and local area geometry

`CapCoercivity.lean` and `CapDistance.lean` connect the actual Mamikon integrals
to support error and Euclidean cap distance. **The assembled Lean source uses
the non-sharp coefficient 80.** It does not claim the analytic sharp coefficient
2 sec(phi) has been established along the full Lean route.

`CoreIntegral.lean` treats substitution and integration by parts using right
derivatives. Nearby cores stay strictly above the floor, permitting a simpler
three-region area proof. `LocalUpperBound.lean` packages a common neighborhood
where the canonical triple is feasible, the niche is inside the cap, and

    A(K) <= Q(xi_K) <= M.

Nearby nonsmooth caps are not asserted to belong to Ki.

### The terminal strip pays for missing angles

`FloorCoverage`, `PartialHallways`, and `OmittedWedgeArea` localize the added
area from omitted final hallway positions to two short endpoint windows in
a thin horizontal slab. `TerminalFloor` constructs a fixed left-wing floor
slice excluded by the tilted terminal strip. `TerminalComparison` makes the
excluded loss dominate the possible gain and derives

    area(S) <= A(K)-c*(pi/2-omega),
    area(S minus U) <= epsilon,
    area(U minus S) <= 2epsilon,

with U=K minus N(K). The proof neither extends the movement of S nor assumes
S is contained in U.

### Actual-set recovery and global entry

`SofaCoordinates` derives the closed supporting constraints from an actual
motion. `SofaCap` constructs its full-angle cap without extending that motion.
`LocalSofaRecovery` combines the terminal estimate, cap distance, roof margins,
erosion, interior balls and missing-area estimates.

`ConvexParallelArea` bounds an outer parallel layer by a homothetic comparison.
`SymmetricDifference` adds the vertical niche band and obtains the area rate.

`CompactSetLimits`, `SofaBounds`, `SofaLimitMotion`, and `QualitativeEntry`
handle arbitrary compact connected sofas. They establish one containing box,
closedness of the supporting conditions, a directly constructed limit motion,
and area upper semicontinuity. Existing uniqueness identifies a maximizing
limit. Compactness is used to enter a fixed neighborhood, not to infer a rate.
`GlobalStability` then handles zero and positive deficits and chooses the
constants uniformly.

## Analytic notes and results not claimed as Lean theorems

The mathematical reading order remains
[08: unrestricted theorem](08-unrestricted-theorem.md),
[05: nonsmooth certificate](05-nonsmooth-certificate.md),
[06: local upper bound](06-local-upper-bound.md), and
[07: terminal-angle loss](07-terminal-angle-loss.md).

[01-cap-coercivity.md](01-cap-coercivity.md) computes the exact Green-operator
constant 2 sec(phi), sharp in the pinned ambient residual space, with
2 sec(phi)<2.002 on the source parameter box. This sharper analytic calculation
is not the coefficient used in the assembled Lean proof source.

[09-sharp-exponent.md](09-sharp-exponent.md) gives the punctured-sofa argument:
removing an open interior disk of radius r preserves a connected moving sofa
with deficit pi*r^2 and rigid-alignment Hausdorff distance r. **This exponent
sharpness argument is not yet written as a Lean theorem.** It is not part of
either headline target above. No best symmetric-difference exponent or best
constant for monotone caps is claimed.

[02-global-qualitative.md](02-global-qualitative.md) and
[03-nonconvex-recovery.md](03-nonconvex-recovery.md) retain the earlier narrower
arguments and their historical descriptions of a missing unrestricted rate.
The later notes and current source supersede those progress statements, not
the historical record. [COMPLETION_REVIEW.md](COMPLETION_REVIEW.md) records the
analytic dependency audit and [CONTINUATION.md](CONTINUATION.md) the source
completion plan.

## Validation records

No Lean or CI validation was performed. A local Python check matched the 73
module filenames against the 72 imports of `All.lean`, detected no duplicate
names, and reproduced its committed Git blob SHA. The result is in
[source-manifest-check.json](source-manifest-check.json). **This is an import
manifest and byte check, not a Lean import-resolution or proof check.** There
was no whole-repository static proof scan.

Separate source-review fix commits preserve corrections concerning ENNReal
versus real area, nonconvex compact support continuity, missing helper names,
trigonometric APIs, witness order, and negated counterexample quantifiers.
They do not establish that all possible errors have been found.

Earlier numerical checks remain historical: 13 completion diagnostics and the
older 17-check suite are recorded in `completion-checks-summary.json`,
`checks-summary.json`, and `CHECK_LOG.md`. They were not rerun to validate the
new Lean files, and they are not interval certificates or formal proofs.

## Manuscript boundary

[paper-section.tex](paper-section.tex) is an earlier, pre-completion proposal
and is still excluded from `docs/paper/main.tex`. No manuscript statement
that its proofs are kernel-checked has been extended to this development.
Source assembly alone does not justify such an extension.

The prior polygonal optimizer outputs are not certified continuous feasible
triples; this source does not make their between-node constraints or arithmetic
rigorous. No boundary-Hausdorff theorem, computed global constant, effective
entry threshold, certified numerical optimizer, or formalized exponent
sharpness is asserted here.
