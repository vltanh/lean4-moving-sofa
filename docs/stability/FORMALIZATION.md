# Lean formalization of quantitative stability

This continuation starts at `4770c508a05295b26215435b5fc85b0a5121fb45`.
The mathematical target is note 08's unrestricted theorem, not just the earlier
conditional injective-cap theorem.

**Status: substantial uncompiled proof source; the unrestricted Lean theorem
is NOT complete.** The remaining work is not merely running a compiler.
The analytic proofs in notes 01--09 remain distinct from this partial Lean
formalization.

## Validation policy and integration

No Lean invocation, Lake invocation, CI dispatch, CI rerun, remote build, or
TeX compilation was performed. The user explicitly prohibited CI and Lean
compilation. Every continuation commit carries `[skip ci]`.

The development is in `MovingSofaStability/`, with an explicit import root
`MovingSofaStability/All.lean`. It is registered as an optional library in
`lakefile.toml`, but the existing default targets are unchanged. No existing
optimality, uniqueness, bridge, audit, workflow, or manuscript proof was edited.
No existing kernel-verification claim is extended to this directory.

Every theorem declaration supplied here has a proof term. No new axiom,
`sorry`, `admit`, or typeclass assumption of the final theorem was introduced.
This is a description of the written source, not a kernel axiom audit. Since
Lean was not invoked, elaboration, tactic completion, and successful imports
remain unverified and may require correction.

## Strongest concrete objective result

`wide_deficit_eq_slack_add_integrals` in `WideResidualEnergy.lean` states

    area(G) - wideUpperQ(xi)
      = wideDualSlack(xi) + wideResidualEnergy(xi_G, xi).

Here `xi` belongs to the genuinely enlarged domain `WideTriple`: its cap need
only be a normalized convex cap, not Ki. The objective is the original
`MovingSofaOptimality.upperQ`, not a newly defined substitute for the area.
`wideDualSlack_nonneg` proves the slack sign. `wideResidualEnergy` is the sum
of six half-integrals of squared differences of the actual Mamikon tangent
displacements. `wide_capResidualEnergy_le_deficit` drops the two nonnegative
auxiliary-body terms to bound the four cap integrals by the Q deficit.

These declarations have no assumption of the desired energy inequality or
of a nonsmooth-competitor derivative sign: those are derived through the
modules listed below. They still require the explicit linear constraints of
the wide triple domain. Showing that the cap associated with a near-optimal
sofa supplies such a triple is a separate geometric task, still outstanding.

## Dependency ledger

The labels below mean **proof source written**, **partly written**, or **not
yet implemented**. None denotes a compilation or verification result.

### Proof source written

1. **Quadratic deficit:** `QuadraticDeficit.lean` proves the exact segment
   identity, the equality of deficit with negative first variation plus
   quadratic energy, and the constant-one energy bound at a maximizer. The
   small-segment argument is explicit rather than an informal limit.
2. **Mamikon difference integrals:** `MamikonEnergy.lean` proves the quantitative
   convexity gap on arbitrary convex bodies. `BaekDeficit.lean` first connects
   it to the existing Ki-based domain and the actual cap area functional.
3. **Enlarged domain:** `WideDomain.lean` constructs `WideTriple`, its convex
   domain structure, the original functional on it, and the tail decomposition.
4. **Nonsmooth cap algebra:** `CBVAlgebra.lean`, `ArcAtoms.lean`,
   `NonsmoothBookkeeping.lean`, and `NonsmoothAffinity.lean` retain and cancel
   all five face contributions at the four cap arcs. The outer-minus-inner
   curve-area term is treated by bilinearity on continuous bounded-variation
   curves, with no C1 assumption on the competitor.
5. **Quadraticity and concavity:** `WideConcavity.lean` proves both properties
   on the enlarged domain, rather than applying the old Ki-only theorems to
   inadmissible inputs.
6. **First variation and reference certificate:** `MixedArea.lean` cancels
   periodic endpoint atoms instead of assuming they vanish.
   `ReferenceCoreVariation.lean` differentiates only the reference core.
   `WideFirstVariation.lean` assembles the six terms with a nonsmooth competitor.
   `WideGerverCertificate.lean` uses Gerver's existing measure decomposition to
   prove the sign, the enlarged-domain maximum, and the exact deficit identity.
   `WideResidualEnergy.lean` identifies that identity with all six integrals.
7. **Actual-set Euclidean geometry:** `EuclideanGeometry.lean` develops both
   directed Euclidean distance bounds, rigid invariance, and the implication
   from actual-set closeness to support closeness. `Statement.lean` pins the
   top and left supports and proves normalization invariance of area.
8. **Finite-measure bookkeeping:** `TerminalBookkeeping.lean` proves the terminal
   comparison and both missing-set estimates once the excluded-region and
   omitted-wedge area estimates are supplied. It never assumes S is contained
   in its full-angle envelope.

### Partly written: cap coercivity

`IntegralEstimates.lean` supplies real integral Cauchy--Schwarz, the four-term
square inequality, and the kernel-to-error estimate. `Residuals.lean` identifies
the tangent residuals, removes translation, and computes the integrating factor.
`ODEReconstruction.lean` integrates with right derivatives so that curvature
atoms are allowed. `GreenNorm.lean` bounds the four displayed Green norm
formulas and proves the rational inequality `2/cos(phi) < 2.002` on the source
box.

**Still missing:** the integral reconstruction on all four intervals with the
needed integrability and endpoint arguments, identification of the displayed
norm formulas with their kernel square integrals, and the final support-norm /
Euclidean cap-distance estimate. The scalar theorem
`green_evaluation_from_squared` explicitly takes its squared estimate as a
hypothesis; it is not mislabelled as the completed cap theorem.

### Not yet implemented

- Note 06: the local exposed-point estimates, canonical-body contacts, niche
  localization, and local geometric upper bound for arbitrary nearby caps.
- Note 07: construction of the fixed excluded floor rectangle and localization
  of omitted wedges. Only the subsequent finite-area comparison is in Lean.
- Notes 02 and 08: compactness of the relevant class of actual moving sofas,
  closedness under limits, and qualitative entry into the local neighborhood.
- Notes 03 and 08: reference erosion, uniform interior-ball property, directed
  nonconvex recovery, and symmetric-difference area estimate.
- Note 08: the unconditional final assembly with one choice of constants.
- Note 09: the punctured-sofa construction and sharpness after optimizing over
  rigid alignments.

`UnrestrictedStability` and `TerminalAngleStability` in `Statement.lean` are
**definitions of the target propositions**, not asserted theorems. There is no
proof of either target in `All.lean` or elsewhere in the new directory.

## Important modelling and proof details

The repository represents points by `Real × Real`, whose default metric is
not Euclidean. It also defines `hausdorffDist` by support functions; applying
that expression to nonconvex sets would compare only their convex hulls.
The target therefore uses `EuclideanClose`, with Euclidean point distances
from the repository's `norm2` and witnesses in both actual sets. For nonempty
compact sets this expresses the desired Euclidean Hausdorff bound. A separate
identification with a standard metric-space Hausdorff API is not used as a
shortcut in the theorem statement.

Curvature atoms at 0, phi, pi/2-phi, and pi cannot be deleted when extending
Baek's domain. They are present in `cap_area_four_arcs` and cancel through
`segArea_join_face`. Periodicity similarly cancels the endpoint atoms in mixed
area. The new proofs never infer Ki from Hausdorff closeness.

The raw Mamikon terms at Gerver need not vanish. The quantitative integrals
are squares of differences. Flat B,D directions are permitted throughout;
there is no assertion of strict concavity in every triple variable.

Every conversion from measure to real area in `TerminalBookkeeping.lean`
retains a finite-measure hypothesis. This prevents `ENNReal.toReal` at infinity
from invalidating an apparently elementary area comparison.

## Source-review corrections preserved in separate commits

- The outer-displacement subtraction needs ring algebra, not definitional
  equality; trigonometric denominators and translation signs were made explicit.
- The Mathlib cosine bound has an implicit `x` argument; the source now passes
  `(x := phi)` rather than applying it positionally.
- Mixed-area symmetry uses explicit equality of the two integrals rather than
  a brittle fixed-depth `congr` chain.

These are corrections found by reading source, not compiler diagnostics.
No claim is made that they exhaust possible elaboration problems.

## Environment record

A local `git clone` was attempted only to obtain source files and failed
because the runtime cannot resolve github.com. Repository reads and commits
were performed through the connected GitHub API. A separate materialization
attempt did not turn connector response citations into local source files.
Neither action involved Lean. No local whole-repository test or static scanner
was run, and no such run is claimed.
