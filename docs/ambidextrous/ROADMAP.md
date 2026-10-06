# Active roadmap: optimal value, ordinary area, and audited reductions

**Primary milestone: optimal value only. Unrestricted optimality is not proved.** Defer uniqueness until the sharp ordinary-area bound is established. Read [HANDOFF.md](HANDOFF.md) for the live-checkpoint procedure, provenance, executed-check status and failed routes. All written arguments remain self-reviewed, not independently verified infrastructure.

## 1. Acceptance criterion

For one attained global ambidextrous maximizer S, prove |S|<=M, where the known feasible reference has

$$
M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.
$$

This establishes the value. A proof for every maximizer and exact equality recovery are later uniqueness obligations, not prerequisites for this milestone.

An auxiliary maximum is useful only with a valid ordinary-area comparison. A decomposition with an uncontrolled positive correction is not such a comparison. Do not infer entry into a candidate neighborhood from the very optimality or uniqueness being sought.

## 2. Direct computer-assisted route: retain the fractional-barrier correction

The [optimality-only computer plan](optimality-only-computer-plan.md) proposes exact global localization plus a local ordinary-area theorem. Read its later [occupancy audit](occupancy-relaxation-audit.md) before implementation. A triple-only LP always admits z=2/3; with pairs, z=1/2 remains feasible. More angles or cells alone cannot overcome these barriers.

An adequate global computation must use certified occupied anchors and empty regions, integral branching or stronger justified inequalities, or exact area bounds for boxes of finite hallway placements. [CF](configuration-area-certificate.md) and the [anchored-terminal framework](anchored-terminal-certificates.md) provide stated necessary constraints, not a completed covering of all competitors.

Every retained angle must be proved visited. Every domain box needs complete coverage, including boundaries. Numerical solvers may propose rational certificates; a separate verifier checks the geometry and weights. No unresolved leaf is silently assigned to a candidate neighborhood. Finite support proximity does not automatically imply the C1 hypotheses of a local theorem.

The unpublished `optimality_anchor_followon.zip` from the prior session is a separate import/replay task. This arm review did not merge it or independently recheck its entire certificate.

## 3. Weighted one-turn route: current exact reduction

The signed objective is

$$
\Psi(U)=|U|-|N(U)|-W(U)/2,
$$

with the **full niche** subtracted. It is not clipped surviving area. The package [one-turn-arm-reduction.md](one-turn-arm-reduction.md), reviewed in [one-turn-arm-package-review.md](one-turn-arm-package-review.md), gives a useful sufficient endpoint condition.

Let [x_L,x_R] be a cap's horizontal projection and [x_tl,x_tr] its top face. At a weighted maximizer,

$$
d_R=x_R-x_{tl}=1+q(0),\qquad d_L=x_{tr}-x_L=1-p(\pi/2).
$$

AR7 and AR5' yield

$$
q(t)\le\max(q(0),1/8),\qquad p(t)\ge\min(p(\pi/2),-1/8).
$$

Therefore EA2, the two inequalities d_R,d_L<=2, supplies unit curvature. SR1 plus AF3 then gives Psi<=M/2, and the reference cap attains that value. **EA2 for one attained weighted maximizer suffices for the weighted value. It has not been proved for one.**

| Weighted subproblem | Current status |
|---|---|
| Attainment | PA2 supplies a global maximizer for the signed objective. |
| Height and floor | ST1 gives roof>=1/2; HV1 gives height one. |
| Selection and regularity | WP1--WP2 select any prescribed weighted maximizer with summable defects; WR1 gives bounded open-quarter curvature and exact half-height vertical end edges. |
| Endpoint-to-interior arms | AR7/AR5' give the sharper propagation and EA2 reduction. |
| Positive top face | TS1 proves full niche height<=1/2 whenever the top-face length T>0. |
| Coarse endpoint arms in that class | TS2 gives d_R,d_L<=9/4. This is not EA2. |
| Zero-length top face | Unresolved by TS1; its finite shortening needs T>0. |
| Sharp weighted value | Still open. Possible remaining long arms lie in (2,9/4] for positive-top maximizers. |

### Finite shortening rather than an assumed derivative

[TS1](one-turn-top-shortening.md) constructs a cap U_minus by shortening every horizontal section by epsilon in (0,T), with

$$
\Psi(U_{\rm minus})-\Psi(U)
\ge\varepsilon\bigl(H_N(U)-1/2-\varepsilon/2\bigr).
$$

The proof uses a niche Minkowski inclusion and interval growth, not a presumed smooth contact chart or differentiability of niche area. This proves H_N<=1/2 at a positive-top maximizer and hence niche containment using ST1. A rational support test gives the 9/4 arm bound.

### The proposed ODE is now solved, but not geometrically justified

[SP1](one-turn-saturated-passage.md) proves the proposed saturated ODE has strictly increasing first-passage time tau(q0) from (1/2,q0) to q=-1/2, with tau=pi/2 only at the reference q0. Its explicit formulas cover the reverse regime and all high-arm standard regimes.

This replaces one numerical observation by a hand proof. It does **not** prove that every maximizing cap follows that saturated law. The next geometric requirements on this alternative remain exact exposure balance, the needed niche-area derivative or a finite substitute, and activity in folded configurations. A solution of an assumed ODE is not a maximizing-body theorem.

## 4. Transfer from a weighted value to two-turn optimality remains separate

The original user proposal OT and its [audit](one-turn-proposal-audit.md) give, under full turns and nonempty two-turn fibers,

$$
|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.
$$

Thus even a sharp weighted bound yields |E|<=M+G. Empty fibers add a further positive correction. OT3--OT4's face classification and OA.3's full-turn rectangle test cover useful cases, but do not eliminate all exceptions. OT5's zero-clipping conclusion keeps its aligned-face and two-sided corner-positivity hypotheses.

The positive-top weighted maximizer from TS1 generates a connected reflected two-turn intersection through height 1/2, with

$$
|S_U|=2\Psi(U)+2\int\min(n,1-a)\,dx.
$$

This makes a weighted value above M/2 relevant to an actual counterexample, but is not an upper bound with the integral discarded. No such counterexample is provided.

| Two-turn obligation | Status |
|---|---|
| Actual angular coverage | Open globally; full turns cannot be inserted by convention. |
| Exceptional face placement | OT classifications give cases, not an exclusion of every case. |
| Point faces | Open; SC3 examples approach M and cannot be dismissed by a fixed lower threshold. |
| Clipping / ordinary-area correction | Open outside the stated no-clipping subcases. |
| Value assembly | Requires these premises or a direct certificate replacing them. |

## 5. Two-wing route remains available

TW/WS/WC, CS/SQ and NH retain convex wing areas rather than repaired hull area. Their calibrated domains are explicit. The canonical-admission upload adds its proposed extension and contact conditions; consult its review and [canonical-wing-winding-accounting.md](canonical-wing-winding-accounting.md).

The exact bookkeeping is

$$
|S|-\widehat{\mathcal W}=N+U-B,
$$

where N is multiplicity-weighted negative winding, U is surviving material outside both wings not covered by positive winding, and B>=0. Adding only a visually apparent loop area is insufficient without controlling U and multiplicities.

R2--R5 remain the critical admission tasks: required angles; actual convex safe wings with the calibrated height/width data; allowed cut slack; and an ordinary-area core comparison. Subadditivity means pairwise disjointness is unnecessary for the upper bound, but it does not identify a nonsimple signed integral with ordinary area. Exact algebra checks are not global admission.

## 6. Next acceptance test

Choose one of the following only when its claimed payoff and hypotheses are explicit:

- Prove EA2 for one weighted maximizer, starting with the remaining positive-top arm interval (2,9/4] or the T=0 case.
- Supply a justified exposure/balance theorem feeding SP1, including the required sign and first-passage properties; do not assume the saturated law.
- Bound the actual two-turn clipping/winding/uncovered correction in a covering class.
- Build a strengthened ordinary-area certificate that clears its stated parameter boxes, with all residual boxes accounted for.

Do not restart solved fixed-width calibration or refine unrelated local/perimeter statements. A negative auxiliary quadratic value is not a feasible-body counterexample; a numerical candidate match is not coverage.

## 7. Execution and regression requirements

The arm package's original four files are preserved at `0b187ac...`. All original numerical parts were freshly replayed; the old author record remains unchanged. The separate [review checker](computer-assisted/one-turn-arms/review_checks.py) and [record](computer-assisted/one-turn-arms/review-results.json) contain 23 exact identities, 213 rational local-offset tests, 200 interval-growth tests and two negative controls. The rational offset samples do not claim cap realizability. The fifty numerical passage comparisons do not certify geometric exposure laws.

Mandatory negative controls remain AF4, GR1, AX1/SAT1, SAC2, SC3 and TR1. Preserve the distinction between signed cap area, clipped surviving area and actual two-turn area. Preserve both positive clipping and uncovered-material terms. Keep exact inequality directions, endpoint hypotheses and finite proof coverage explicit.

Every substantive finding is committed with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Existing manuscript, Lean libraries and workflows are unchanged. Commit counts are not a measure of proximity to closure; PR #3 remains draft.
