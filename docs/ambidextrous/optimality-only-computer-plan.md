# Optimality-only computer-assisted program

**Purpose.** From this point, the primary target is only

[
sup{|S|:S	ext{ ambidextrous}}le M,
]

where (M) is the area of Romik's feasible candidate. Equality classification and uniqueness are deferred until the value is proved. This note is a proof plan, not a completed certificate.

The motivation is methodological. The successful width theorem used finitely many actually visited hallway positions, counted ordinary forbidden area, and admitted exact rational replay. The unsuccessful global routes generally optimized an auxiliary support functional and then failed at the ordinary-area linkage through clipping, winding, or uncovered material. The global computation should therefore keep ordinary area in the certified layer.

## 1. Normalized search domain

Use the established common incoming unit-height normalization and the analytic width restriction

[
2<Wle1+2sqrt2<4.
]

Translate horizontally so the body lies in a fixed rectangle ([0,4]	imes[0,1]). Branch on a rational interval for the actual horizontal width and on rational half-tangent intervals for the two reduced terminal angles.

No curvature, contact topology, symmetry, full turn, or candidate neighborhood is assumed in this global layer.

## 2. Eliminate hallway translations exactly

For an ordered orthonormal hallway frame ((u,v)), CF1 gives:

there exist hallway offsets containing a compact set (S) iff there are no (p,q,rin S) with

[
(q-p)cdot u>1,qquad (r-p)cdot v>1.
]

This eliminates the two placement translations. For a spatial cell partition, interval bounds on dot-product differences certify triples of cells that cannot all meet a feasible body.

For every endpoint-angle box, use only hallway frames proved to be actually visited throughout that box. The determinant/strip inequalities already used in AW-W and CF give these guarantees for both turns. All direction data should use rational half-angle parameters, so the final checker can work with exact rational arithmetic.

## 3. Occupancy relaxation and exact dual certificate

Let (z_Cin[0,1]) indicate whether the body meets spatial cell (C). Every certified forbidden triple gives

[
z_P+z_Q+z_Rle2.
]

The ordinary area is at most the sum of the cell areas times (z_C). Add any other universally valid cell exclusions or width/end-strip constraints only when their proof is explicit.

A numerical LP or combinatorial optimizer may propose a sparse dual certificate. The trusted checker must verify:

1. the endpoint/width boxes cover their claimed parameter range with no gaps;
2. every used hallway frame is guaranteed visited on its box;
3. every forbidden triple has strict rational separation (>1);
4. every dual weight is nonnegative rational;
5. the resulting ordinary-area upper bound is evaluated exactly;
6. comparison with a rational lower bound for (M) is exact.

The optimizer is not trusted. Only the replayed rational certificate is.

This is the direct generalization of the width certificate and CF2.

## 4. Why a pure finite grid is unlikely to finish equality

Romik's candidate itself is feasible. A coarse occupancy relaxation will normally upper-bound its neighborhood by (M+arepsilon), not exactly (M). Refining a single finite grid cannot by itself prove an irrational sharp equality unless the relaxation becomes exact for structural reasons.

Therefore the intended proof is **global computer localization plus local analysis**:

[
	ext{all non-candidate boxes}<M
quad+quad
	ext{one rigorously described local candidate neighborhood}le M.
]

The computer certificate only has to exclude the complement of that local neighborhood. It does not need to classify equality.

## 5. Local theorem needed for the surviving neighborhood

The local theorem should be an ordinary-area statement, not just an auxiliary maximum. Candidate options already under development are:

- the canonical two-wing functional, provided the local hypotheses force full turns, the required contact signs, zero/controlled cut slack, and zero winding/uncovered corrections;
- the signed one-turn problem plus an exact local two-turn clipping estimate.

The latest canonical-wing accounting writes the exact discrepancy as

[
|S|-widehat{mathcal W}=N+U-B,
]

where (N) is multiplicity-weighted negative winding and (U) is surviving material outside both wings not covered by positive winding. A valid local theorem must prove (N=U=0), or pay them quantitatively. Matching only the candidate or observing numerically zero winding is insufficient.

The latest weighted one-turn results give every signed maximizer height one, half-height end edges, (W^{2,infty}) open-quarter support, and the arm-dependent curvature bounds. They may make a local sharp theorem tractable, but they are not yet the global two-turn area inequality.

## 6. Alternative direct branch-and-bound

If occupancy LPs are too weak, branch directly on a finite list of support/placement variables at rational-angle frames. On each box:

- use interval arithmetic to bound the exact polygonal finite-position envelope area;
- keep both turns simultaneously;
- include clipping/empty-fiber corrections in the objective rather than dropping them;
- split boxes when the active combinatorics are ambiguous;
- emit a proof tree whose leaves contain exact/rational or outward-rounded interval inequalities.

This is closer to the old 11.7-million-node width certificate but in a higher-dimensional parameter space. It is acceptable if replay is simple and complete. A solver's global-optimality flag is not a certificate.

## 7. Acceptance criteria

The **optimal value** is closed once we have:

1. a finite, replayable certificate proving every normalized feasible body outside an explicitly defined local candidate neighborhood has area (<M); and
2. a written or separately certified local theorem proving every feasible body inside that neighborhood has area (le M).

No uniqueness conclusion is required for this milestone.

After value closure, equality cases can be analyzed separately. The existing coercive/equality machinery may then become useful without carrying the burden of the global upper bound.

## 8. Immediate implementation order

1. Reuse and extend `configuration-area-certificate.md` / `verify_configurations.py`.
2. Add width branching over (2<W<4) and both endpoint-angle boxes.
3. Search for rational dual certificates on increasingly fine spatial grids, recording the best exact margin per box.
4. Identify boxes that resist strict exclusion; inspect whether they concentrate near Romik's finite support/contact data.
5. Define the smallest robust local neighborhood containing all resistant boxes.
6. Prove the local ordinary-area theorem there using canonical wings or one-turn regularity.
7. Only after steps 1--6 succeed, assemble the value theorem.

## 9. Scope

This plan deliberately postpones uniqueness. It also deliberately avoids reusing false universal enclosures from AF4, GR1, AX1/SAT1, SC3, or the uncorrected winding formula. Those examples are regression tests for every global relaxation.

Computer assistance is encouraged for search and certificate generation. The final trusted surface should be a small exact verifier plus explicit mathematical lemmas connecting its finite objects to arbitrary feasible bodies.

No CI or Lean/Lake compilation is part of this program.
