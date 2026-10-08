# Reflection-equivariant connectedification of complete two-turn envelopes

**Status (2026-10-08):** A universal, exact geometric reduction for *full conventional turns*. It removes a connectedness issue from the horizontal convex-hull symmetrization proposal [HS](hull-reflection-symmetrization-budget.md). It does **not** prove the missing hull-symmetrization area monotonicity, nor the sharp Romik bound for left-right symmetric sofas whose vertical span is less than one. No Lean, CI, or numerical optimization is used in the proof.

Write \(J(x,y)=(-x,y)\). Fix the common incoming horizontal strip \(0\le y\le1\), with no assumption that the occupied vertical span is exactly one. A **full-turn feasible** compact set satisfies the complete canonical lower and upper supporting-hallway inequalities, even if it is disconnected; these are setwise conditions.

## 1. The reflection-equivariant compression

**Lemma SEC1.** Suppose \(Q\subset\mathbb R\times[0,1]\) is nonempty, compact, and \(JQ=Q\). Suppose each vertical fiber \(Q_x\) is an interval or empty. Assume \(Q\) satisfies the two complete canonical handed hallway families. Then there exists a **compact connected** full-turn feasible \(J\)-symmetric body \(Q^\sharp\) with
\[
\boxed{|Q^\sharp|=|Q|,\qquad
\operatorname{span}_y Q^\sharp=\operatorname{span}_y Q.}\tag{SEC.1}
\]
Its horizontal extent may decrease. Neither the original convex hull nor its support function is asserted to be preserved.

**Proof.** Let \(D=\operatorname{proj}_x Q\), a compact symmetric subset of \([-r,r]\). Define
\[
T(x)=\int_0^x \mathbf1_D(s)\,ds,\qquad
F(x,y)=(T(x),y).
\]
The integral for negative \(x\) has its usual signed meaning. Because \(\mathbf1_D\) is even, \(T\) is **odd**. It is also nondecreasing and 1-Lipschitz. The image \(T(D)\) is the interval \([-|D|/2,|D|/2]\): every value in the image of \([-r,r]\) has a preimage in \(D\), because on each complementary open gap of \(D\) the function \(T\) is constant and the two gap endpoints lie in \(D\).

The safe-depth estimate is worth recording rather than appealing to a symmetry intuition. For a unit normal \(n=(n_x,n_y)\), a point \(p\in Q\), and \(H=\operatorname{span}_y Q\le1\),
\[
\begin{aligned}
h_{F(Q)}(n)-F(p)\cdot n
&=\max_{q\in Q}\left[n_x(T(q_x)-T(p_x))+n_y(q_y-p_y)\right]\\
&\le\max\{h_Q(n)-p\cdot n,\ H|n_y|\}.\tag{SEC.2}
\end{aligned}
\]
Indeed, when \(n_x(q_x-p_x)\ge0\), monotonicity and the 1-Lipschitz property bound the transformed horizontal term by the old one; otherwise the transformed horizontal term is nonpositive and the vertical term is at most \(H|n_y|\). Thus any supporting-wall depth at most one remains at most one. The same is true for a width-one terminal or incoming strip, so **both complete angular families** survive the map.

The map \(F\) is reflection-equivariant: \(F\circ J=J\circ F\). The exact area equality
\[
|F(Q)|=|Q|
\]
follows by collapsing the complementary gaps one by one (each finite-gap map acts as a horizontal translation on the occupied slabs), taking their uniform limit, and combining upper semicontinuity of compact-set area under Hausdorff convergence with nonexpansion of each horizontal section under a 1-Lipschitz map. This is the argument of [GC2](horizontal-gap-compression.md), now with the centered odd normalization.

Finally, fill every nonempty vertical fiber of \(F(Q)\) by its interval hull. Since \(T(D)\) is an interval, the resulting \(Q^\sharp\) is compact and connected: a separation into disjoint nonempty compact pieces would partition its interval horizontal projection into two disjoint compact sets, because every vertical interval fiber lies wholly in one piece. The filling preserves symmetry and vertical extrema. It adds planar area only on the countably many abscissae where \(T\) has nontrivial constant intervals; all other fibers were already intervals. It therefore preserves area.

The vertical slice of every conventional lower supporting L-hallway is an interval, because its two outer conditions are upper bounds on \(y\) and the two inner alternatives are upward rays. The upper handed hallway similarly has interval sections. Consequently the vertical filling preserves every already available hallway placement. The support function is unchanged by filling, because
\[
F(Q)\subseteq Q^\sharp\subseteq\operatorname{conv}F(Q).
\]
Thus the filled body retains **canonical** supporting-hallway feasibility; support continuity makes both angle paths continuous, and the terminal straight-arm motions append at the endpoints. This proves SEC.1. \(\square\)

The preceding proof has no regularity, contact-order, positive-face, or unit-span requirement.

## 2. Exact variational equivalence, including disconnected envelopes

For a compact convex \(K\subset\mathbb R\times[0,1]\), define \(E(K)\) by removing *both* complete canonical open forbidden sweeps from \(K\). Its fibers are intervals or empty, and it is compact. Let
\[
\mathcal K_J=\{K:\ K\text{ nonempty compact convex, }JK=K,\ K\subset\mathbb R\times[0,1]\},
\]
and let \(\mathcal S_J\) be all compact connected \(J\)-symmetric bodies in the incoming unit strip that complete **both** conventional turns (their actual vertical span can be \(<1\)).

**Theorem SEC2 (symmetric envelope equality).**
\[
\boxed{\sup_{S\in\mathcal S_J}|S|
=\sup_{K\in\mathcal K_J}|E(K)|.}\tag{SEC.3}
\]

**Proof.** If \(S\in\mathcal S_J\), its convex hull \(K=\operatorname{conv}S\) belongs to \(\mathcal K_J\), and canonical support tightening gives \(S\subseteq E(K)\). This proves the first supremum is no larger than the second.

Conversely let \(K\in\mathcal K_J\). Reflection across \(x=0\) sends a lower canonical frame at \(t\) to the same (unordered) lower frame at \(\pi/2-t\), with the two walls exchanged; it similarly sends upper frames to upper frames. Since the **complete** quarter is present for each handedness and \(JK=K\), the total forbidden sweeps and \(E(K)\) are \(J\)-invariant. If \(E(K)\) is empty its area is zero and nothing is needed. Otherwise SEC1 applied to \(Q=E(K)\) constructs \(S=Q^\sharp\in\mathcal S_J\) with \(|S|=|E(K)|\). Hence the second supremum is no larger than the first. \(\square\)

This equality uses **the total ordinary area** of a potentially disconnected canonical envelope, and it never calls such a disconnected union itself a connected sofa. Nor does it replace positive clipping by a signed surrogate.

## 3. The corrected conditional hull-symmetrization route

Let \(A_F\) denote the unrestricted *complete-two-turn* area supremum (without \(J\)-symmetry), with vertical span at most one. For an actual full-turn hull \(K\), center its horizontal projection and let \(K_s=(K+JK)/2\). The exact convex hull-area identity [HS.1](hull-reflection-symmetrization-budget.md) does not establish the sign of the **full envelope** difference. Consider the still-open assertion
\[
\boxed{|E(K_s)|\ge|E(K)|\quad
\text{for every actual full-turn hull }K.}\tag{SEC.4, unproved}
\]
If SEC.4 were established, then SEC2 would imply
\[
\boxed{A_F=\sup_{S\in\mathcal S_J}|S|.}\tag{SEC.5, conditional}
\]
Indeed any full-turn \(S\) has \(|S|\le|E(K)|\le|E(K_s)|\le\sup_{\mathcal S_J}|\cdot|\), and the reverse inequality is immediate.

**Thus no separate connectedness or symmetric-component theorem remains necessary for this particular conditional route.** The earlier disconnected-envelope counterexamples are respected: SEC1 transforms the union into a *different* connected feasible shape and preserves its total area and reflection symmetry.

However, SEC1 preserves the **actual vertical span**. It need not equal one. The branch's [RS2](reflection-symmetric-optimality.md) establishes the sharp value only for \(J\)-symmetric bodies in the specified **unit-span** normalization. It cannot be applied to all of \(\mathcal S_J\), as the explicit [HS.5–HS.12](hull-reflection-symmetrization-budget.md) subunit-span constructions warn. Nor is SEC.4 proved by this connectedification argument. Therefore full-turn optimality would still require **both**
\[
\text{(i) the universal ordinary-area monotonicity SEC.4},\qquad
\text{(ii) }\sup_{\mathcal S_J}|S|\le M
\text{ allowing subunit spans}.
\]
Unrestricted partial turns additionally require control.

These are genuine global targets, not silently discharged conclusions. The only unconditional mathematical progress here is SEC1–SEC3: a symmetry-preserving, area-exact admissible connectedification and an exact supremum identity over **all** symmetric full-turn convex hulls.
