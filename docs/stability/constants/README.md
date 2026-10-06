# Analytic stability improvements: centered caps and actual sofas

Base paper checkpoint: `a8f7719fd43fa91b223d9f6c0eb53594e5a95716`.
This PR #10 branch is separate from the coercive-route PR #9. The present
analytic continuation starts at `f95fe45c4194ecc95d46ad5427bf58db2dcae157`.

**Formalization is frozen at the user's request.** This continuation changes
only analytic notes and Python diagnostics. No Lean file, library configuration,
workflow, bridge, Challenge statement, manuscript, or original proof is changed.
No Lean, Lake, CI, or manuscript build was run. New conclusions are written
analytic arguments requiring independent review, not kernel-checked results.

## Strongest current analytic statements

Write epsilon=|G|-|S|. For all sufficiently near-optimal original moving sofas:

| Object / normalization | New coefficient | Previous comparison |
| --- | --- | --- |
| Cap distance with horizontal midpoint alignment | `sec(phi) < 1.001` times square-root cap energy or Q deficit | `2 sec(phi) < 2.002` with the left-support pin |
| Actual sofa, same old left/top pin | `4.22 * sqrt(epsilon)` | `30.5 * sqrt(epsilon)` |
| Actual sofa, horizontal midpoint/top alignment | `2.3 * sqrt(epsilon)` | New stronger allowed-alignment theorem |
| Symmetric-difference area, midpoint/top alignment | `50 * sqrt(epsilon)` | `100` with the previous normalization/estimate |
| Missing angle of every admissible reduced motion | `3.1 * epsilon` | Unchanged |

The common positive entry threshold remains existential. These are not bounds
claimed for all possible deficits, nor sharp global-sofa coefficients. The two
normalizations are different and must be labelled. The cap constant is not the
actual-sofa constant. The midpoint theorem uses only translation, and thus also
bounds distance minimized over arbitrary rigid alignment.

## Reading order for this continuation

1. [11-centered-cap-coercivity.md](11-centered-cap-coercivity.md): midpoint
   alignment halves the kernel norm coefficient, with exact covariance and
   centered norm formulas. The abstract quotient norm is exactly sec(phi).
2. [12-boundary-cones-and-sector-recovery.md](12-boundary-cones-and-sector-recovery.md):
   audit every reference corner, rotate local charts, and recover missing area
   from whole eroded sectors. The outer floor angles are pi/2-phi, NOT pi/2.
3. [13-normal-slack-recovery.md](13-normal-slack-recovery.md): adapt hallway
   angles to Euclidean normal displacement. Forward recovery no longer pays
   for steepness in fixed vertical coordinates.
4. [14-centered-global-2p3.md](14-centered-global-2p3.md): the numerical global
   theorem and exact optimization/certification of its split deficit budget.
5. [15-feasible-cap-residual-sharpness.md](15-feasible-cap-residual-sharpness.md):
   the raw extremizing ray is infeasible in either sign, but one-sided Hermite
   smoothing realizes limiting sharpness among actual normalized convex caps.
6. [16-effective-entry-certificate-design.md](16-effective-entry-certificate-design.md):
   a finite convergent outer-pixel certificate design for a prescribed global
   neighborhood. No enumeration or numerical separation gap has been computed.

[10-analytic-continuation.md](10-analytic-continuation.md) preserves the initial
hypotheses and scope. Notes 01--09 preserve the earlier 84/80/30.5 stages and
remain useful inputs; their numerical conclusions are superseded where stated
above, not silently erased from the research history.

## Main mechanisms

### Center the width, not one endpoint

If f is the left-pinned support difference, replace it by

    g(t)=f(t)-(f(0)/2)*cos(t).

This removes the same translation kernel and makes the two extreme support
errors equal. The exact centered evaluation norm is at most sec(phi)^2/2;
since the residual square norm is twice the cap energy, the coefficient is
sec(phi). Endpoint width gives a matching quotient-space lower bound.

One-sided smoothing of the negative extremal direction yields genuine convex
caps approaching this residual coefficient. This is sharpness for E_cap, NOT
for M-Q: dual slack and the two auxiliary-body energies have not been shown
negligible. Determining the best feasible-Q or area-deficit constant still
requires a critical-cone analysis.

### Whole sectors replace one worst-case interior disk

The reference boundary has uniform translated interior sectors of aperture
beta=1.53 at sufficiently small scales. For erosion r and target radius rho,
the surviving sector area is

    rho^2 * [beta/2-asin(u)-u*sqrt(1-u^2)+u^2*cot(beta/2)], u=r/rho.

Optimizing this exact expression over complementary cap/missing-area budgets
gives sufficient-method limits approximately 2.299325 (centered) and 4.216330
(left-pinned). Exact rational Taylor bounds certify the strict choices 2.3 and
4.22. These are limits of a sufficient recovery method, not lower bounds for
actual sofa stability.

### Normals replace vertical roof depth

At a core point, choose the hallway-angle adjustment to balance the two inner
wall violations for a unit displacement direction w. Both first variations
are `[sqrt(a^2+b^2)/(a+b)]*<w,n>`. Nearest-point geometry, including the two
roof corners, yields a common coefficient strictly below 1/2. Using 49/100
makes the forward factor 100/49, rather than 10.2. Only the reference is
differentiated, never an arbitrary competing cap or sofa.

## Diagnostics actually run

Run locally, without Lean or Lake:

    python docs/stability/constants/check_centered_recovery.py
    python docs/stability/constants/check_cap_smoothing.py

The first script passed 3,126 assertions at 50 decimal digits, including 12
exact rational inequalities, 65 kernel quadratures, sampled normal witnesses,
exact sector stationary identities, and budget stress tests. Its committed
Git blob matches the tested source:

    f78a75069f6a4af1620d2f426c15ce06ec76e824.

The second integrates five one-sided Hermite residual witnesses. Their endpoint
quotient lower ratios approach 1.00076792405693346 from below. Its blob also
matches the tested source:

    3a4449a4e8cfc48b2ce5d3862ce3cc1c79f2c64c.

The exact outputs are `centered-recovery-checks.json` and
`cap-smoothing-checks.json`. The earlier `global-constant-checks.json` remains
its separate historical 3,212-assertion record; it was not rerun or relabelled
as validation of the new results.

These diagnostics do NOT establish uniform boundary charts by sampling, a
verified global entry threshold, feasibility of an extremal Q triple, or any
Lean theorem. The proofs of the uniform and limiting statements are the
analytic arguments in the notes.

## Negative findings preserved

The initial right-angle corner hypothesis failed: the two outer floor angles
are pi/2-phi. A quarter-plane sector cannot be used there. An initial kernel
test used a displacement below working precision at a breakpoint and recursed;
the endpoint kernel is now explicit. The raw extremal ray fails cap feasibility
in both signs, so it is not itself a Q sharpness witness. Coefficient 2.2 fails
the present sufficient sector budget, but that is NOT a counterexample among
actual sofas. The pixel-entry design must retain the small-area class by taking
the maximum of its enumerated upper bound and 2.2.

## Remaining goals

A numerical epsilon0 still needs certified reference chart/local-certificate
radii and a global separation calculation. Note 16 gives a convergent design,
not a completed practical solver. The 1e-14 downstream calculation from note 08
must not be used as an unconditional entry threshold, especially with the new
normal/cone charts.

Global coefficient 2.3 is not sharp; the puncture lower bound 1/sqrt(pi) remains
only a necessary lower bound. The cap residual constant sec(phi) is sharp in
its stated class, but a smaller coefficient for the full feasible Q deficit
may still be possible because that deficit contains additional nonnegative
terms. Manuscript integration and any future formalization remain separate.
