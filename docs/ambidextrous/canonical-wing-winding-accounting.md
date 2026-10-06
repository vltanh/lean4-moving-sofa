# Canonical-wing area accounting: negative winding is not the only correction

This is a review and limited extension of the user-supplied [canonical-admission proposal](two-wing-canonical-admission.md). It gives an exact ordinary-area identity, simplifies its pointwise winding admission, and supplies a precise version of its local cubic loop estimate. None of these statements proves unrestricted optimality. Labels WA are local; the original proposal is preserved unchanged.

## 1. The complete ordinary-area discrepancy

Let R,D be compact convex sets and Gamma the closed Lipschitz core curve used in CS.3, with the actual inward intersections. Let w be its clockwise winding number off its trace; set w=0 on the trace, which has planar measure zero. Put w_+=max(w,0), w_-=max(-w,0).

The winding-area formula gives

$$
\widehat{\mathcal W}(R,D)=|R|+|D|+\int_{\mathbb R^2}w.
\tag{WA.1}
$$

This is the generalized Green formula for a closed rectifiable curve, not the area of its geometric union. A primary reference is Cufi and Verdera, *A general form of Green Formula and Cauchy Integral Theorem*, [arXiv:1306.6832](https://arxiv.org/abs/1306.6832). The winding number is integrable here. For a polygon, subdividing the curve into its faces and summing their integer winding numbers proves the same identity directly.

For a compact measurable body S put A=R union D and C=S minus A. Define

$$
N=\int w_-,\qquad U=|C\cap\{w\le0\}|,
$$

$$
B=|A\setminus S|+|R\cap D|
+\int_{\mathbb R^2\setminus C}w_+
+\int_C(w_+-1)_+\ge0.
\tag{WA.2}
$$

U is surviving material outside both wings that the positively wound core fails to cover. N counts negative winding with multiplicity; the area of {w<0} equals N only when all negative winding is -1.

**Proposition WA1 (exact discrepancy).**

$$
\boxed{|S|-\widehat{\mathcal W}(R,D)=N+U-B.}
\tag{WA.3}
$$

In particular,

$$
|S|\le\widehat{\mathcal W}(R,D)+N+U.
\tag{WA.4}
$$

**Proof.** The union identity gives

$$
|R|+|D|=|S|-|C|+|A\setminus S|+|R\cap D|.
$$

Since w is integer-valued almost everywhere,

$$
|C|-\int_Cw_+=|C\cap\{w\le0\}|-\int_C(w_+-1)_+.
$$

Substitute these identities and w=w_+-w_- into WA.1. QED.

Adding only the negative-loop area is not generally justified: one must prove U=0 or pay for U too. Empirical agreement of |S|-widehat W with N does not establish U=0, since U and B can cancel. This elementary accounting carries no novelty claim.

A bound N+U<=M-widehat W would prove the area inequality. It would not automatically give the old functional equality kernel: equality could involve positive corrections. Exact uniqueness would need the correction budget's equality case.

## 2. Zero cut slack already forces cut-support agreement

For the canonical right wing, at theta in J_R its defining inequalities give

$$
r(\theta)\le h_K(\theta),\qquad r(\theta+\pi)\le1-h_K(\theta).
$$

Subtracting yields the quantitative bound

$$
\boxed{0\le h_K(\theta)-r(\theta)\le1-w_R(\theta).}
\tag{WA.5}
$$

Thus w_R(theta)=1 forces r(theta)=h_K(theta) and r(theta+pi)=1-h_K(theta). The same applies to D on J_D. Under the proposal's zero-cut-slack condition (Z), its four required cut-support agreements are automatic. This does not imply agreement on the whole core intervals.

Also, without any support agreement,

$$
Q_w(t)\subseteq Q_K(t),\qquad Q_w^\rho(t)\subseteq Q_K^\rho(t),
\tag{WA.6}
$$

because r<=h_K and d<=h_K. Surviving points therefore avoid every wing quadrant whose corresponding hull placement is known feasible. All angles used must still be covered by the actual motions.

## 3. Pointwise admission needs less than the full Theorem CA

**Proposition WA2.** Suppose S has both canonical full turns, K=conv(S), and R,D are its canonical wings. Assume the imported hull contact condition (M), zero cut slack (Z), and outward arms (V). Then

$$
S\setminus(R\cup D\cup\Gamma)\subseteq\{w=1\}.
\tag{WA.7}
$$

Consequently U=0 and

$$
\boxed{|S|\le\widehat{\mathcal W}(R,D)+\int w_-.}
\tag{WA.8}
$$

Whole-core support agreement and apex order are not needed for this particular conclusion. They serve a different purpose in the imported Theorem CA: showing that the negative-winding term vanishes.

**Proof.** CW2--CW3 of the proposal show that a surviving point outside R fails a right cut-wall test, and a point outside D fails a left cut-wall test. WA.5 and (Z) replace those hull cut supports by the corresponding wing supports. WA.6 supplies avoidance of the wing quadrants. The three point hypotheses of the proposal's winding lemma CW4 therefore hold, and its continuous-argument calculation gives clockwise winding one. Remove the null curve trace for area and apply WA1. QED.

In the absence of (M), backward transitions can leave U positive. Even with (M), the displayed conclusion retains N unless another argument excludes negative winding. This is not unrestricted admission.

## 4. A precise local cubic-loop lemma

The first-return statement in JX2 needs a simple local excursion before its loop area is interpreted. The following elementary version supplies that hypothesis rather than assuming it from C1 proximity.

In positively oriented normal/tangent coordinates at a cut wall, let a curve family be (X_e(t),Y_e(t)), with X_e(0)=Y_e(0)=0 and X_e'(0)=e>0. Assume X_e is C2 and Y_e is C1 on a fixed one-sided neighborhood. Suppose, jointly as e tends to zero and t tends to zero through nonnegative values,

$$
X_e''(t)\longrightarrow-a<0,\qquad Y_e'(t)\longrightarrow q>0.
\tag{WA.9}
$$

**Lemma WA3 (transverse small loop).** For sufficiently small e there is a unique first positive return t_e to X_e=0, with t_e/e tending to 2/a. The arc up to t_e, closed by its segment on X=0, is a simple counterclockwise loop, and

$$
\boxed{\lim_{e\downarrow0}\frac{|\mathrm{loop}_e|}{e^3}=\frac{2q}{3a^2}.}
\tag{WA.10}
$$

**Proof.** On a sufficiently small fixed neighborhood X_e'' is strictly negative and Y_e' strictly positive. Taylor's formula gives, uniformly for bounded s>=0,

$$
e^{-2}X_e(es)\to s-a s^2/2,\qquad Y_e'(es)\to q.
$$

The polynomial is positive before 2/a and negative afterwards. Strict concavity gives a unique return, with the asserted limit. Strict tangential monotonicity makes the arc a graph and excludes self-intersection. Its interior lies on X>0, so closing down the wall gives counterclockwise orientation. Its area is integral_0^{t_e} X_e(t)Y_e'(t)dt. Rescale t=es and integrate to obtain 2q/(3a^2). QED.

For a corner curve z'=p n_t+q n_(t+L), the normal acceleration at the cut angle beta is p'(beta)-q(beta). A family satisfying WA.9 with p(beta)=e and p'(beta) tending to -kappa therefore has a=kappa+q, reproducing the proposal's formal coefficient 2q/[3(kappa+q)^2].

This is a theorem about the subloop. To infer winding -1 for the complete Gamma inside it, the remainder of Gamma must contribute zero winding there. Identifying the loop area with |S|-widehat W additionally requires controlling the other terms of WA.3. Neither inference is made here.

WA.9 is stronger than C1 support closeness, which controls velocities but not necessarily their derivatives or a unique transverse excursion. Faceted junction shavings need a separate argument and are not automatically covered by this lemma.

## 5. Proof boundary

GH1 bounds widehat W on its stated height domain. The imported CA gives a sufficient situation where N and U both vanish. WA1 records the complete correction outside that situation; WA2 simplifies only the pointwise admission step. WA3 turns a local heuristic into a precise calculus statement under explicit regularity.

No result here places every maximizing sofa in the GH height domain, proves its full turns or contact signs, proves zero cut slack, or pays N+U globally. Exact equality recovery must be retained in any future correction budget.

No CI or Lean/Lake compilation was used. These are self-reviewed written arguments, not independent refereeing or kernel verification.
