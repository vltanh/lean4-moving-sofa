# 25. A uniform bounding box and attainment of the unrestricted maximum

This note closes the existence issue recorded in Note 24. It does not identify the maximizing body. The proof uses the general canonical reduction already established, not the support-curvature hypotheses of Theorem 52.

All feasibility statements refer to the compact connected, common-incoming-orientation problem posed in Note 1. No regular-closedness assumption is added to that admissible class.

## 25.1 The conventional diagonal placement

Normalize S to lie in 0<=y<=1, and suppose it has a correctly signed lower canonical motion visiting t=pi/4. Let its corner at that angle be c=(c_x,k). In body coordinates, the outer hallway inequalities are

\[
c_x+y-k-\sqrt2\leq x\leq c_x-y+k+\sqrt2.
\tag{25.1}
\]

The forbidden quadrant is

\[
y<k-|x-c_x|.
\tag{25.2}
\]

**Lemma 53 (high corner excludes competitive area).** If k>1 and S is connected, then |S|<=sqrt(2).

**Proof.** The whole vertical line x=c_x in the incoming strip is forbidden by (25.2). The horizontal projection of connected S is an interval, so S lies strictly on one side of that line. On the right side, avoidance of (25.2) is x>=c_x+k-y. Together with (25.1), this restricts each horizontal section to an interval of length at most sqrt(2). The left side is identical. Integration over a strip of height at most one gives the assertion. QED.

The case k=1 is deliberately not included in the strict separation argument: the two sides can meet at (c_x,1). It is harmless for the bounding box below.

**Proposition 54 (uniform competitive box).** Every ambidextrous S with |S|>sqrt(2) has a proper rigid representative contained in

\[
\mathcal B=[-(1+\sqrt2),1+\sqrt2]\times[0,1].
\tag{25.3}
\]

Its convex hull is contained in the same box.

**Proof.** Apply unit-span normalization, support tightening, and the correct-sign reduction from Notes 8, 10, and 15. The two-strip bound gives |S|<=sec(alpha) for a lower endpoint alpha<pi/2. Since |S|>sqrt(2), its endpoint exceeds pi/4; the full-endpoint case also visits pi/4. Thus the preceding diagonal placement exists. Lemma 53 gives k<=1. For y>=0 the two outer inequalities (25.1) imply
\(|x-c_x|\leq k+\sqrt2\leq1+\sqrt2\).
Translate horizontally by -c_x. Convexity of the box gives the hull assertion. QED.

This is a bound on the entire connected body, not merely its positive-area core. Long zero-area appendages are included. For bodies of area at most sqrt(2), no such normalization is needed for the maximizing-sequence argument.

## 25.2 Compactness with variable angle endpoints

Fix A_0 with sqrt(2)<A_0<M; for example A_0=8/5, using (10.3). For each body in a maximizing sequence, discard finitely many terms so that its area exceeds A_0. Put it in the representative of Proposition 54 and retain its canonical endpoint magnitudes alpha_n,gamma_n. The two-strip bound gives

\[
\alpha_n,\gamma_n\in[\arccos(1/A_0),\pi/2].
\tag{25.4}
\]

The nonempty compact subsets of a compact metric space form a compact space in Hausdorff distance. For completeness, finite epsilon-nets of the underlying space give finite epsilon-nets for its nonempty compact subsets by recording which net balls are met. A Cauchy sequence of compact subsets converges to the nonempty compact set of limits of convergent point subsequences. Total boundedness and completeness give the asserted sequential compactness.

Pass to a subsequence with

\[
S_n\to S,\qquad \alpha_n\to\alpha,\qquad\gamma_n\to\gamma.
\]

The Hausdorff limit S is compact and nonempty. It is connected: a separation into two nonempty disjoint compact pieces would have positive distance and disjoint neighborhoods, and eventually S_n would lie in their union while meeting both, contradicting connectedness.

Convex hulls converge as well. Indeed, if d_H(S_n,S)<=epsilon then every finite convex combination of points of S_n is within epsilon of the corresponding combination of points of S, and conversely. Hence d_H(conv(S_n),conv(S))<=epsilon. Their support functions converge uniformly since the difference in support values in each unit direction is bounded by this Hausdorff distance.

## 25.3 Feasibility is closed in these canonical variables

Write K=conv(S). Incoming span and the two outgoing width inequalities pass to the limit by uniform convergence of supports and convergence of the endpoint angles.

Fix t in [0,alpha]. Choose t_n in [0,alpha_n] with t_n->t, and for any p in S choose p_n in S_n with p_n->p. The canonical hallway inequalities at (K_n,t_n) consist of two non-strict outer inequalities and the closed disjunction

\[
p_n\cdot\mu_{t_n}\geq h_{K_n}(\mu_{t_n})-1
\quad\text{or}\quad
p_n\cdot\nu_{t_n}\geq h_{K_n}(\nu_{t_n})-1.
\tag{25.5}
\]

Their limit is the same closed condition for (p,K,t): a union of two closed half-planes is closed, or one may pass to a subsequence on which the chosen disjunct is constant. Thus S avoids every lower forbidden quadrant for t in [0,alpha]. The reflected upper interval is identical.

The continuous support-determined canonical paths therefore transport S through both hallways with the required endpoint arms. Note 14's common-pose argument supplies any initial translations. This proves feasibility of the limit without taking a limit of arbitrarily parametrized original motions.

## 25.4 Upper semicontinuity of area and a maximizer

For compact subsets of the fixed box, Hausdorff convergence gives

\[
\limsup_n|S_n|\leq|S|.
\tag{25.6}
\]

Indeed, for each epsilon>0 all sufficiently large S_n are contained in the closed epsilon-neighborhood S_epsilon. These neighborhoods have finite measure and decrease to S as epsilon decreases to zero. Continuity of Lebesgue measure from above gives |S_epsilon|->|S|, proving (25.6).

**Theorem 55 (unrestricted attainment).** The posed ambidextrous problem has a finite attained maximum among compact connected bodies. At least one maximizer has unit incoming span, lies in the box (25.3), and has the correctly signed canonical motions with variable endpoint magnitudes in (25.4).

**Proof.** The candidate established in Note 18 has area M>A_0. Every body of area above sqrt(2) obeys the finite box-area bound from Proposition 54, while all other bodies already have bounded area. The supremum is therefore finite and at least M. Take a maximizing sequence above A_0 and apply Sections 25.2–25.3. Its limit is compact, connected, and feasible; (25.6) shows its area is at least the supremum, hence equal to it. The normalizations and endpoint bounds pass to the limit. QED.

For every maximizer the same normalization and saturation can be carried out. Saturation can only preserve its area, since it remains feasible. This proves area equality with its envelope, but not set equality without a regular-closed recovery argument.

## 25.5 What remains

Existence is no longer a missing premise in a maximizer-based structural proof. The missing statements concern the geometry of every maximizer: full-quarter endpoint reduction and the curvature/contact properties (or a replacement certificate). None follows merely from compactness or from choosing a maximizing sequence.
