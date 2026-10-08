# Canonical saturation does not rescue the rejected repair budget

This corrects the proposed next step in the preceding status discussion. The axis-cut examples cannot be dismissed merely because the original cuts are not saturated. Their saturation has the same hull, is a feasible connected body, and violates the same proposed inequality even more strongly.

This is a negative result about an attempted proof route, not a disproof of Romik optimality. No unrestricted optimum is identified here. Dependencies are the candidate and cut geometry established in [AX1](axis-cut-repair-budget-obstruction.md); the elementary saturation facts are proved again below. Labels SAT are local to this note.

## 1. Fixed-hull full-turn saturation

For a normalized compact convex K in 0<=y<=1, let W_-(K), W_+(K) be the unions of its canonical open forbidden quadrants over the full lower and upper quarter turns, respectively. Define

$$
\mathcal E(K)=K\setminus(W_-(K)\cup W_+(K)).
$$

Suppose S is compact, connected, follows both canonical full turns, and conv(S)=K. Then S is contained in E(K). Every vertical section of E(K) is a closed interval or empty: a section of K is an interval, the lower sweep is downward closed and the upper sweep upward closed. At every x in the projection of K the section is nonempty, since the connected S has the same interval projection as its convex hull.

E(K) is compact because the forbidden sweeps are open. It is connected: a separation into two compact nonempty pieces would assign each connected vertical fiber to one piece, giving two disjoint compact sets whose projections partition an interval. Every subset of E(K) satisfies the canonical hallway inequalities, and the incoming and terminal vertical strips are valid. Thus E(K) is a feasible compact connected body. Finally

$$
S\subseteq\mathcal E(K)\subseteq K=\operatorname{conv}(S)
\quad\Longrightarrow\quad
\operatorname{conv}(\mathcal E(K))=K.
\tag{SAT.1}
$$

In particular the operation is idempotent on such represented bodies: saturating E(K) again produces the same set because its hull and its canonical constraints have not changed. Saturation solves only the inclusion problem at a **fixed hull**, not maximization over different hulls.

## 2. Apply saturation to the axis-cut examples

Retain the notation of AX1:

$$
S_\tau=\Sigma\cap\{y+\tau(x-\ell)\leq1\},\qquad
K_\tau=K_*\cap\{y+\tau(x-\ell)\leq1\}
=\operatorname{conv}(S_\tau).
$$

These compact connected bodies inherit the candidate's full motions. Support tightening retains every point: its new outer bounds are the actual supports, and its new inner thresholds are no larger than those of the original placements. Hence they satisfy the canonical full-turn constraints of K_tau. Set

$$
T_\tau=\mathcal E(K_\tau).
$$

By SAT.1, T_tau is feasible, connected, fully canonically saturated, has exactly the hull K_tau, and contains S_tau. It has the candidate's horizontal width and unit vertical span.

Write R for the least curvature-dominated majorant from GM2 and let J_side denote AS.1. AX1 proved, for small positive tau and constants C,c>0 independent of tau,

$$
|S_\tau|\geq M-C\tau^{3/2},\qquad
\mathcal J_{\rm side}(h_{R(K_\tau)};h_{R(K_\tau)}-h_{K_\tau})
\leq M-c\tau.
$$

Therefore:

**Proposition SAT1 (saturated counterexamples to the proposed budget).** For all sufficiently small positive tau,

$$
\boxed{
|T_\tau|\geq|S_\tau|>
\mathcal J_{\rm side}(h_{R(\operatorname{conv}T_\tau)};
 h_{R(\operatorname{conv}T_\tau)}-h_{\operatorname{conv}T_\tau}).
}
\tag{SAT.2}
$$

**Proof.** The hull of T_tau is K_tau, so the right-hand side is exactly the same as for S_tau. Containment can only increase the left-hand side. Choose tau with C sqrt(tau)<c. QED.

Thus neither fixed-hull saturation nor a high-area threshold below M repairs AS.10. This conclusion does not require knowing the sign of |T_tau|-M.

## 3. Convergence is not a substitute for that sign

One also has T_tau converging in Hausdorff distance to Sigma, and |T_tau| tending to M. Here is a proof that does not presuppose optimality.

The cut bodies S_tau tend to Sigma in Hausdorff distance: the removed portions shrink to the two height-one tips, and those tips are limits of retained points. Alternatively the explicit local circle description in AX1 gives this directly. They are contained in T_tau. Conversely, if tau_n tends to zero and p_n belongs to T_tau_n, any convergent subsequence has limit p in K_*, since K_tau tends to K_*. At every fixed turn angle the two inner thresholds converge to the candidate thresholds. Each p_n satisfies their closed disjunction, so p satisfies the candidate's disjunction. Consequently p belongs to its full envelope Sigma. This proves the reverse directed Hausdorff convergence.

All sets lie in one fixed compact rectangle. For compact sets, Hausdorff convergence gives area upper semicontinuity: eventually T_tau is contained in any fixed closed neighborhood of Sigma, whose area decreases to |Sigma| as the neighborhood radius tends to zero. On the other hand |T_tau|>=|S_tau| tends from below to M by AX1. Hence |T_tau| tends to M.

These statements alone do not decide whether T_tau has area below or above M for an individual tau. That requires an actual area calculation, not the unproved global theorem. A separate note carries out the local calculation for this family.

## 4. Correction to the research direction

The suggestion that the latest obstruction was caused only by deliberately omitted material was insufficient. Such material can be added back through canonical saturation while preserving the same obstructed hull and the failed functional inequality. A global maximizer has properties beyond being a fixed point of this saturation operation.

Accordingly, a valid continuation must either use comparisons that change the hull and prove their actual area gain, or prove a different global ordinary-area upper bound. It cannot reuse AS.10 with the sole new premise that the input is canonically saturated. This correction narrows the failed route; it is not a claim that the required maximizing-body theorem has now been supplied.

This note is a written proof based on the cited candidate/cut facts, not independent verification of the full historical chain. No CI, Lean/Lake compilation, or numerical computation is used.
