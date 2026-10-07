# Proof audit, rejected shortcuts, and remaining gaps

This ledger distinguishes the analytic result, the implemented Lean lemmas,
and the checks actually executed. No Lean, Lake, or CI has been invoked.

## What the new constants mean

The strongest written analytic conclusion is a common positive, existential
threshold with coefficients

    Hausdorff 61/2 = 30.5,
    symmetric difference 100,
    terminal angle 31/10 = 3.1.

The quantifier is over all sufficiently near-optimal moving sofas. It is not
a theorem that the same numbers work at every deficit, and it is not a claim
that any of these coefficients is sharp. The simpler Hausdorff31 argument uses
the old terminal comparison; 30.5 also uses the strengthened trapezoidal floor
loss and small surplus.

The proof is divided into actual mathematical steps, not a new interface that
assumes the desired final estimate. Its use of the earlier local certificate
and qualitative-entry theorem remains explicit. The original exact uniqueness
result handles zero-deficit shape equality. For the zero-deficit angle conclusion,
one may use the existing exact width/angle consequence, or the earlier angle
stability theorem restricted to zero deficit, before intersecting thresholds.
No numerical angle coefficient is imported into the positive-deficit proof.

## Rejected or insufficient shortcuts

### Improving the roof slope does not itself improve the hallway slack

At a core point x(phi), the same-angle slacks at x(phi)-(0,d) are exactly

    -d*sin(phi),     -d*cos(phi).

Since sin(phi)<0.04<5/51, the desired common coefficient5/51 is FALSE for that
fixed witness angle. A better estimate of |dy/dx| does not fix this.
The adaptive-angle calculation in note06 is therefore essential: it balances
the first variations by changing the witness angle with the depth.

### A roof slope of 9 is too optimistic

The diagnostic maximum is approximately9.3487385, near a core endpoint.
There is also a simple enclosure-based obstruction: at phi, a<0.095,
b>1.39, b<1.4, sin(phi)<0.04, cos(phi)>0.9992. Thus

    Y > 1.39*0.9992-0.095*0.04,
    X < 0.095+1.4*0.04,
    Y > 9*X.

So replacing the proved rational9.45 by9 would be a mathematical error,
not merely a tighter constant requiring more numerical precision.

### The cap and the missing set cannot each spend epsilon

The correct bookkeeping is e=M-|U| and m=epsilon-e+g. Bounds that put
sqrt(epsilon) into both independent costs before combining them are valid but
wasteful. The punctured family has e=0; treating it as if it also spent epsilon
on cap displacement illustrates this loss.

### The terminal error is not intrinsically of square-root size

Promoting B*epsilon to B*sqrt(epsilon) needlessly inserts B into the leading
coefficient. It remains valid, but obscures how an explicit coefficient can
exist without an effective entry threshold. In the new proof the linear
remainder is retained and then absorbed only by shrinking the threshold.

### Small-scale smoothness is not a license to choose a large interior-ball ratio

A better treatment of boundary normals might improve kappa dramatically, but
one must check every reference boundary junction and the cap's bottom corners.
Piecewise formulas alone do not exclude acute corners or prove a uniform cone
condition. Likewise, a normal-distance slack estimate is different from the
vertical-depth margin proved here; one cannot simply replace F=10.2 by3 in the
existing vertical formula. Such improvements are not included in the claimed
30.5 theorem.

### Numerical recovery does not compute global entry

The explicit downstream bound epsilon<=10^(-14) only meets radius, margin,
linear-remainder, and area-budget conditions AFTER the local cap and terminal
certificates apply. It does not establish that every sofa with that deficit
satisfies their geometric hypotheses. The existing compactness proof supplies
no numerical global separation gap. Earlier discretized Q optimizers with
sampled constraints cannot be used as certified upper bounds for that missing
step without a proved discretization error analysis.

## Lower bound and unresolved optimality

The punctured Gerver family has deficit pi*r^2 and rigid-Hausdorff distance r.
It forces every unrestricted near-optimal square-root coefficient to satisfy

    C >= 1/sqrt(pi) = 0.5641895...

`CoefficientLowerBound.lean` supplies intended proof source for this necessary
condition, including arbitrary rigid alignments and any positive entry threshold.
It does not identify the least admissible coefficient. The gap between this
obstruction and30.5 is substantial; rounding the cap coefficient's last decimal
is not the principal remaining loss.

## Lean source coverage

The source already supplies the split finite-area budget, exact-disk recovery,
and scalar quadrature. This continuation adds:

- exact orthogonal erosion with sqrt(2), for arbitrary normalized caps;
- improved scalar phase-velocity and balancing inequalities;
- actual-set reverse recovery with explicit30.5, conditional on the stated
  numerical interior-ball and local certificate inputs;
- direct roof-band localization from support error, without global Hausdorff
  conversion;
- necessary lower bound on any universal coefficient from punctured sofas;
- explicit rational smallness calculations for the downstream recovery stage.

The remaining formalization is not just running a compiler. In particular it
must connect the phase formula bounds and adaptive-angle derivative calculation
to a specialized `RoofSlackMargin` theorem, prove the explicit reference
interior-ball geometry, integrate the exact roof band and convex square layer,
construct the new terminal trapezoid, and assemble those geometric results with
local/global entry into the numerical theorem. The existing top-level global
stability statement has NOT been silently changed to assert30.5 or100.

## Checks actually run

`check_global_constants.py` ran locally with Python3.13.5 and mpmath1.3.0 at
60 decimal digits. All3212 assertions passed. They include exact rational
budgets and128 exact rational-polygon square-dilation identities, plus sampled
reference velocities, adapted hallway slacks, and split-budget stress tests.
`global-constant-checks.json` is the recorded output.

The tested source has Git blob SHA
`6ec33e06e8a6425e8179d5103cbc749068a6935d`, matching the committed file.
The sampled maximum slope, transversality minimum, and other diagnostics are
not interval certificates or substitutes for the analytic enclosure proofs.
No Lean elaboration, theorem dependency audit, uniform compactness argument,
or numerical epsilon0 certificate was tested by that script.

A separate source-review fix commit makes the orthogonal norm's squared identity
explicit before taking nonnegative square roots. This was found by reading the
proof source, not by running Lean. Other elaboration or proof errors may remain.

## Integration boundary

PR #8 was merged before this work. This branch is based on paper checkpoint
`a8f7719fd43fa91b223d9f6c0eb53594e5a95716` and is separate from PR #9.
The initial six constants commits ending at
`4acfa639976ce41eab7ae77f2485591b9e3f6bb9` were inherited; the continuation starts
after them and preserves their candidate84 and simpler80 stages in history.

The faithful Baek proof, old uniqueness proof, bridge, Challenge, canonical
Solution, manuscript, workflows, and lakefile have not been rewritten. Note
that the merged paper branch already includes MovingSofaStability in default
targets with a glob: the new Lean modules will enter that target when someone
later runs it. No claim is made that the old build scope excludes them.
`MovingSofaStability.Constants` provides a dedicated import root for review;
the existing All root is left unchanged.

No verification claims in the paper should be expanded until the new theorem
source is completed, checked, and audited. The analytic notes can be reviewed
independently of that process.
