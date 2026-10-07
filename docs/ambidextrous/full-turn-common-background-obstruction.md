# A genuine full-turn obstruction to universal common-face background admission

**Scope.** This is a hand-proof negative control for the proposed global CB/CT background construction. An explicit compact convex ambidextrous body has both *full* conventional turns, strictly positive horizontal faces in opposite end strips, and a horizontal face separation that no pair of containing height-one caps can bridge with **one common top-face interval** while each has full niche height at most one half. It has small area and **does not** exclude common-face admission for all *competitive* bodies. It is not a counterexample to Romik optimality.

The argument is independent of the weighted cap theorem and of curvature regularization. Labels CGA are local. No numerical search or computation is a premise.

## 1. The exact full-turn parallelogram

Put
\[
W=\frac{12}{5},\qquad \varepsilon=\frac1{20},\qquad
S=\operatorname{conv}\{(0,1),(\varepsilon,1),(W,0),(W+\varepsilon,0)\}.
\tag{CGA.1}
\]
This is the Minkowski sum of the diagonal segment
\[
S_0=[(0,1),(W,0)]
\]
and the horizontal segment \([0,\varepsilon]e_x\). Its fibers are
\[
S_y=[W(1-y),\,W(1-y)+\varepsilon]\quad(0\le y\le1).
\]
Hence it is compact, convex and connected, has incoming vertical span exactly one, and
\[
|S|=\varepsilon=\frac1{20}.
\tag{CGA.2}
\]
Its top face is \([0,\varepsilon]\times\{1\}\), its bottom face is \([W,W+\varepsilon]\times\{0\}\), and its horizontal projection is \([0,W+\varepsilon]\) of width \(49/20\). The two faces are strictly separated and lie in the opposite unit end intervals.

**Theorem CGA1.** The *same* body \(S\) admits both complete canonical conventional quarter turns. It need not be reoriented, shrunk, rounded or disconnected.

**Proof.** Write \(L=\pi/2\), \(c=\cos t\), \(s=\sin t\), \(u=(c,s)\), \(v=(-s,c)\), with \(0\le t\le L\). For a convex hull with support \(h\), a point lies in the canonical hallway if at least one of its inner-wall support depths
\[
D_u(z)=h(u)-z\cdot u,\qquad D_v(z)=h(v)-z\cdot v
\]
is at most one. Both outer supporting inequalities are automatic. The canonical corner path is continuous by support continuity, and the incoming and outgoing axes have width one in the required normal. Thus it is enough to verify the depth disjunction for every \(t\).

First use the lower turn, on \(S_0\). Parameterize a point by its fraction \(\lambda\in[0,1]\) from the top endpoint to the bottom endpoint. The two signed projection differences are
\[
A=Wc-s,\qquad B=Ws+c>0,\qquad A^2+B^2=W^2+1=(13/5)^2.
\]
If \(A\ge0\), its depths are \(A(1-\lambda)\) and \(B\lambda\). For all positive \(A,B\),
\[
\min(A(1-\lambda),B\lambda)
\le\frac{AB}{A+B}
\le\frac{A+B}{4}
\le\frac{\sqrt{A^2+B^2}}{2\sqrt2}
=\frac{13}{10\sqrt2}.
\tag{CGA.3}
\]
For the horizontal summand, each depth increases by at most \(\varepsilon\), so the smaller new depth is at most \(13/(10\sqrt2)+\varepsilon<1\). The last strict inequality is exact: \(13/(10\sqrt2)<19/20\) is equivalent, after squaring positive quantities, to \(676<722\).

If \(A<0\), the first wall alone protects the whole thickened segment. Its maximum depth is at most
\[
s-Wc+\varepsilon c=s-(W-\varepsilon)c\le s\le1,
\]
because \(W>\varepsilon\). This also covers the terminal angle, where equality is allowed.

For the upper turn, reflect the body vertically. Reflection does not alter its horizontal summand. The diagonal segment now runs from \((0,0)\) to \((W,1)\), with projection differences
\[
A'=Wc+s>0,\qquad B'=c-Ws,\qquad (A')^2+(B')^2=(13/5)^2.
\]
If \(B'\le0\), the two support maxima occur at opposite endpoints; their depths are again bounded by (CGA.3) plus \(\varepsilon\). If \(B'>0\), the second wall alone protects every point, with maximum depth
\[
c-Ws+\varepsilon s=c-(W-\varepsilon)s\le c\le1.
\]
Thus the reflected body makes a full lower turn, which is exactly a full upper turn of \(S\). The canonical placement lemma supplies continuous actual motions throughout both closed quarters. QED.

## 2. A universal half-height niche ceiling on the top face

**Lemma CGA2 (face-length obstruction).** Let \(B\) be *any* compact downward convex cap of height one, and suppose its horizontal top face is \([a,b]\times\{1\}\), length \(T=b-a\). Let \(N(B)\) denote its **full** positive-height one-turn niche. Then
\[
\boxed{H_N(B)\ge\max\{0,\,T/2+1-\sqrt2\}.}
\tag{CGA.4}
\]
Consequently
\[
H_N(B)\le\frac12\quad\Longrightarrow\quad T\le2\sqrt2-1.
\tag{CGA.5}
\]

**Proof.** At the turn angle \(t=\pi/4\), the two upper supporting values \(f=h_B(t)\), \(g=h_B(t+\pi/2)\) obey
\[
f\ge(b+1)/\sqrt2,\qquad g\ge(1-a)/\sqrt2
\]
by the retained top-face endpoints. The two inner-wall lines meet at a corner of height
\[
c_y=(f-1)\sin t+(g-1)\cos t
=\frac{f+g}{\sqrt2}-\sqrt2
\ge\frac{T}{2}+1-\sqrt2.
\]
When the corner height is positive, points of its open forbidden quadrant approach that corner from below while retaining positive height. Hence the full niche height is at least that corner height. If it is not positive, the stated lower bound is zero. Rearranging a bound by one half gives (CGA.5). QED.

This estimate requires neither a curvature bound nor smoothness, an aligned face, or a cap actually optimal for any functional. It is a direct necessary condition for the half-height niche hypothesis used in TC/CT/CB.

## 3. A common-face background is impossible for this feasible pair

Form the two downward caps \(U,V\) of the *actual* common hull of \(S\): \(U\) has top roof from \(S\), while \(V\) has the vertically reflected bottom roof. They have the same projection and height one. The first contains \((0,1)\) and \((\varepsilon,1)\); the second contains \((W,1)\) and \((W+\varepsilon,1)\).

Suppose there were containing height-one caps \(B_1\supseteq U\), \(B_2\supseteq V\) whose horizontal top-face intervals **coincide**, and both had full niche height at most one half. A containing cap of height one necessarily contains each original height-one point in its own top face. The common interval must therefore contain \([0,W+\varepsilon]\) and have length at least \(49/20>2\).

But CGA.5 gives length at most \(2\sqrt2-1<2\), since \(\sqrt2<3/2\). Contradiction.

**Theorem CGA3 (exact admission obstruction).** No such pair of containing half-height-niche backgrounds with one common top-face interval exists for the genuine full-turn body (CGA.1). In particular the common-background-face requirement in CB/CT cannot be established by a universal inclusion construction for **all** full-turn bodies. Adding upper-curvature restrictions only makes that input class smaller.

The obstruction is specifically to this *background-admission architecture*. It does not disprove the true full-turn area inequality, another area-aware repair that does not require common faces, or admission after an explicitly paid replacement rather than simple containment.

## 4. Competitive scope and next gate

This body's area is only \(1/20\), far below the candidate's \(M>8/5\). Thus CGA3 does **not** rule out a theorem saying that every *competitive* saturated opposite-face body has compatible backgrounds. Such a theorem would need to use competitive area quantitatively; neither full-turn feasibility nor smooth convexity alone is enough.

It does make a broad strategy choice precise: either prove a **competitive-only** shared-background theorem, retaining its area threshold, or pursue a direct actual-area inequality (for instance the proved SPB geometric enclosure) that does not demand a common top-face background.

No computational result, CI, Lean/Lake compilation, dependency installation, manuscript build or long search is used. The complete example and inequalities above are pen-and-paper. Unrestricted full-turn optimality remains open.

## 5. The example is already canonically saturated

Here \(K=\operatorname{conv}(S)=S\), since the example is convex. Theorem CGA1 establishes that **every point of \(K\)** survives every canonical hallway of both complete turns. Therefore the full same-hull canonical envelope satisfies
\[
E(K)=K=S.
\]
The example is not an artifact of leaving admissible material unfilled, or a body whose actual hull shrinks after canonical tightening. It belongs to the **saturated, positive opposite-end-face** class singled out by PD/PS, although its area is far below the competitive range.

Accordingly no theorem claiming universal **inclusion-based** common-face half-height-niche background admission over that entire saturated class can be true. A competitive-only admission theorem, or a replacement comparison that is not required to contain both original caps, is not refuted. These qualifications are essential to any attempt to use CB to finish full-turn optimality.

## 6. A continuum of exact obstructions, and the sharp diagonal-rod threshold

The fixed values in CGA.1 are illustrative; the same argument supplies a whole family. Let \(W\in(2,\sqrt7)\), let \(\ell=\sqrt{W^2+1}<2\sqrt2\), and choose
\[
0<\varepsilon<\min\left\{W,\ 1-\frac{\ell}{2\sqrt2}\right\}.
\]
Then the parallelogram with top face \([0,\varepsilon]\times\{1\}\) and bottom face \([W,W+\varepsilon]\times\{0\}\) has both complete turns: in the opposite-extrema angular regimes the maximum smaller depth is at most \(\ell/(2\sqrt2)+\varepsilon<1\); in the same-extremum regimes a single wall protects all points, with maximal depth at most \(s-(W-\varepsilon)c\) or \(c-(W-\varepsilon)s\), each at most one. All conclusions of CGA3 still hold because the common top-face span would exceed \(W>2>2\sqrt2-1\). These bodies are convex, canonically saturated, and have arbitrarily small positive areas \(\varepsilon\).

For clarity, the diagonal segment *before* horizontal thickening has a **sharp** full-quarter threshold within this coordinate family. The sufficiency of \(W^2+1\le8\) is CGA.3 with \(\varepsilon=0\). If \(W^2+1>8\), choose the lower-turn angle
\[
\tan t=\frac{W-1}{W+1}\quad(0<t<\pi/4).
\]
Then \(A=W\cos t-\sin t=B=W\sin t+\cos t=\ell/\sqrt2>2\). The midpoint of the diagonal segment has both inner-wall depths \(A/2=B/2>1\), so it lies strictly in the canonical forbidden quadrant at that angle. By the canonical support-tightening lemma, no alternative translation of that frame can make the segment feasible. Thus, for \(W>1\), a diagonal segment from \((0,1)\) to \((W,0)\) can make both complete canonical turns **if and only if** \(W\le\sqrt7\). The same condition holds for the reflected turn.

This sharp rod computation is only an exact feasibility fact, not an area bound for general sofas. In particular it does not promote the small-area background obstruction into a counterexample to competitive-only admission.

## 7. The half-height face threshold is sharp, not just a 45-degree estimate

The lower bound CGA.4 is the **best universal bound depending only on the top-face length**. Let \(Q_T=[a,b]\times[0,1]\) be the rectangle beneath a top face of length \(T=b-a>0\). Every height-one downward cap having that face contains \(Q_T\), so support monotonicity implies \(N(Q_T)\subseteq N(B)\).

For \(Q_T\), both inner-wall supports are attained at the two appropriate top vertices, and its inner corner at angle \(t\) has exact height
\[
c_y(t)=T\sin t\cos t+1-\sin t-\cos t.
\]
Put \(z=\sin t+\cos t\in[1,\sqrt2]\), so \(\sin t\cos t=(z^2-1)/2\). Then
\[
c_y(t)=\frac T2(z^2-1)+1-z.
\]
This is a strictly convex quadratic in \(z\), so its maximum over \([1,\sqrt2]\) is attained at an endpoint. The endpoint values are zero and \(T/2+1-\sqrt2\), respectively. The supremum of heights in each positive forbidden quadrant equals the height of its corner, since its downward-left interior approaches that corner. Therefore
\[
\boxed{H_N(Q_T)=\max\{0,T/2+1-\sqrt2\}.}\tag{CGA.6}
\]
Here \(H_N\) is the supremum of positive heights, with value zero for an empty positive niche.

Together with support monotonicity, (CGA.6) proves that the infimum of full-niche heights over **all** height-one downward caps with a prescribed positive top-face length \(T\) is exactly \(\max\{0,T/2+1-\sqrt2\}\), attained by the rectangle. Thus the bound \(T\le2\sqrt2-1\) under \(H_N\le1/2\) is sharp for that premise. Neither an angular refinement nor a sharper test based only on the common top-face length can evade CGA3. A global admission theorem must use additional competitive-body geometry or replace that premise.
