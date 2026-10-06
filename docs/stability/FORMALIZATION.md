# Lean source for unrestricted stability

**Current status: the unrestricted theorem and angle-rate theorem now have
end-to-end Lean proof source. None of this development has been compiled or
kernel-checked.** Elaboration, tactic and API errors may remain. Source assembly
must not be described as a verified formalization.

This completion continuation starts at
`0d578d8337553dedbfd2a86f407acef1d6a03c9d`, after the earlier algebraic and local
geometric development. It does not modify the manuscript's incorporated
alternative optimality proof.

## Headline declarations

`MovingSofaStability/GlobalStability.lean` contains:

```lean
theorem unrestricted_stability {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    UnrestrictedStability P

theorem terminal_angle_stability {P : GerverParams}
    (hP : P.IsSolution) (hbox : P.InBox) :
    TerminalAngleStability P
```

Both have proof terms. The target propositions remain defined in
`Statement.lean`, but they are no longer merely unproved target definitions.
The final declarations do not assume a stability estimate, a special envelope,
Ki membership of the competitor, or an interface packaging the missing proof.

`reduced_sofa_stability` supplies a common set of constants for every admissible
reduced motion of every sufficiently near-optimal sofa. It handles the
zero-deficit case using the existing uniqueness theorem and the positive case
using the newly assembled local and compactness arguments.

The actual conclusions are:

- Euclidean closeness, in both directed distances, of the normalized original
  nonconvex set to Gerver at rate C sqrt(M-area(S));
- symmetric-difference area at the same square-root rate;
- terminal angle deficit pi/2-omega bounded linearly in M-area(S).

Only a translation is used in the manuscript's initial-horizontal-strip
convention. The global constants and entry threshold are existential, not
numerically computed.

## Proof route

### 1. Nonsmooth deficit certificate

The earlier modules through `WideResidualEnergy.lean` prove in source

    M - Q(xi) = nonnegative dual slack + six displacement-difference energies.

The objective is the original `MovingSofaOptimality.upperQ` and the domain
retains its linear wall constraints while allowing nonsmooth convex caps.
Curvature atoms are retained in the four-arc decomposition and cancelled
against their connector faces. Only the reference Gerver core is differentiated
in the first variation. The auxiliary-body null directions cause no problem:
their two nonnegative energies are discarded in the cap estimate.

### 2. Cap distance

`ResidualIntegrability`, `ResidualMass`, `ResidualPropagation`,
`FourArcCoercivity`, `CapCoercivity`, `SupportDistance`, and `CapDistance` connect
those integrals to upper support error, the full support circle, and actual
Euclidean cap distance.

**The completed source route uses the non-sharp cap coefficient 80.** The
analytic note's sharp pinned coefficient 2 sec(phi), and its bound below
2.002, are not silently substituted into this route. The unrestricted theorem
only requires existence of a finite constant.

### 3. Local area bound for arbitrary nearby caps

`CoreIntegral.lean` proves substitution through a continuous primitive and
right derivatives, not a C1 change-of-variables assumption on the competitor.
`CutSeparation`, `SeparatedWedges`, `CoreRegionGeometry`, and `CoreAreaBound`
supply the three disjoint niche regions. The reference core has positive height,
so the local proof does not need the source's auxiliary negative-height region.

`LocalUpperBound.lean` assembles the neighborhood theorem:

    canonical triple feasible, N(K) subset K, A(K) <= Q(xi_K) <= M.

All its hypotheses are obtained in a fixed support neighborhood of Gerver.
The competitor is not asserted to belong to Ki.

### 4. Terminal strip versus omitted angles

`FloorCoverage` proves that a fixed interior niche-floor interval has uniformly
strict forbidden-wedge witnesses at angles bounded away from pi/2.
`PartialHallways` bounds late wedge heights linearly in the omitted angle.
`OmittedWedgeArea` confines their new area to two arbitrarily short endpoint
windows. `TerminalFloor` constructs the excluded floor slice explicitly.

`TerminalComparison.lean` chooses the constants in the correct order and derives

    area(S) <= A(K) - c*(pi/2-omega),
    area(S minus U) <= epsilon,
    area(U minus S) <= 2*epsilon,

where U=K minus N(K). It also supplies approximate full-angle hallway slack.
It never assumes S subset U or extends the original motion to a right angle.

### 5. Actual-set recovery and area distance

`SofaCoordinates` derives supporting hallway and terminal strip constraints
from the original movement. `SofaCap` constructs the downward completion using
all upper supporting half-planes and proves that it preserves the original
set's upper supports. `LocalSofaRecovery` combines the cap estimate, roof
margins, erosion, interior balls and missing-area comparison.

`ConvexParallelArea` controls the outer layer of the reference cap by dilation
about an inscribed disk and Haar area scaling. `SymmetricDifference` adds a
thin vertical roof-band estimate. Thus small actual-set distance and the
original area deficit control symmetric-difference area; no continuity of
nonconvex area is assumed.

### 6. Qualitative entry and final assembly

`CompactSetLimits` uses the hyperspace of all nonempty compact sets, not just
convex bodies. It proves support convergence with changing angles, preservation
of connectedness, and upper semicontinuity of area.

`SofaBounds` gives a fixed rectangle using connectedness and the pi/4 hallway.
`SofaLimitMotion` passes the closed wall constraints and terminal width to the
limit and constructs a movement from its support function. It does not assume
convergence of the original movement paths. `QualitativeEntry` invokes the
existing pinned uniqueness and Gerver width results to identify a maximizing
limit and enter the fixed local neighborhood.

`GlobalStability` then chooses one set of constants and proves the two targets.

## Modelling and scope

The default metric on Real x Real is the product metric, and the source's
support-based `hausdorffDist` only sees convex hulls of nonconvex sets. The
headline uses `EuclideanClose`, with the repository's Euclidean `norm2` and
witnesses in both actual sets. The hyperspace's product-metric distance is used
only topologically and is converted with an explicit factor two.

The separate punctured-sofa exponent-sharpness argument in note 09 has NOT
been added as a Lean theorem. It is not part of either target above. The exact
sharp cap constant is likewise not the coefficient used in the assembled
source proof. The manuscript must not claim these extras are formalized on
the basis of the present files.

## Source review and preserved corrections

Separate commits record corrections found by reading source, not by compiling:

- `theorem1_1_1` bounds ENNReal volume; the real deficit sign now uses the
  existing real-area corollary.
- Compact support continuity is used directly for a nonconvex limit sofa;
  an initial invalid attempt to supply a convex-body witness was removed.
- A nonexistent reference-compactness shortcut was replaced with the actual
  moving-sofa compactness theorem.
- Rotation subtraction was supplied explicitly and the two-argument
  inverse-cosine API was corrected.
- The symmetric-difference theorem's existential witness order and the
  compactness counterexample quantifiers were made explicit.

These corrections do not certify that all possible source errors have been
found. No claim of successful elaboration, tactic completion, import resolution
inside Lean, or kernel axiom audit is made.

## Import coverage and validation policy

There are 73 Lean files in `MovingSofaStability/`, including `All.lean`.
The import root now lists the other 72 modules, including `GlobalStability`.
A local Python manifest-only check matched those names against the GitHub
changed-file list and reproduced the committed All.lean Git blob SHA
`81aa7b29ae18da039cf3abd75560735dcd1ebdb1`. See `source-manifest-check.json`.
This checks file coverage and bytes, not Lean syntax or proofs.

No Lean, Lake, CI, remote build, or TeX compilation was invoked. All continuation
commits carry `[skip ci]`. The optional stability library remains excluded from
default targets. Existing verified libraries, audits, workflows, and manuscript
files were not changed in this continuation.

DNS resolution still prevents a local clone. Repository reads and commits used
the connected GitHub API. There was no whole-repository static proof scan; the
only executed new source check was the import-manifest/hash check just described.
Earlier numerical test logs are historical and do not validate the new Lean.
