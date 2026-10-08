# Width-gate supplement: curvature and contact already force full turns

This supplement removes the **separate full-quarter-turn assumption** from the application of Theorem 65 to competitive bodies. It does not prove the remaining curvature or contact inequalities for an unrestricted maximizer.

**Label convention.** Results here use WG1–WG3, and the sharp application in Note 31 uses WG4. This avoids collisions with concurrently added numbered Notes 64–67. The existing filename is retained so previously committed links remain valid. This supplement is distinct from `64-positive-corners-are-interior.md`.

The key intermediate body is a Minkowski central symmetral used only to compare widths. It is **not asserted to be a feasible sofa**. No feasibility-preserving symmetrization, symmetry of an optimizer, or new maximizer-selection theorem is assumed.

## W.1 Two moment inequalities on a quarter circle

Put L=pi/2. Let r:[0,L] -> [0,1] be measurable and write

\[
a=\int_0^L r(t)\cos t\,dt,
\qquad b=\int_0^L r(t)\sin t\,dt.
\]

**Lemma WG1 (quarter moments).**

\[
0\leq a,b\leq1,\qquad
b\leq\sqrt{2a-a^2},\qquad a\leq\sqrt{2b-b^2}.
\tag{W.1}
\]

**Proof.** The first bounds follow by integration. For the first curved bound put y=1-a. When 0<=y<1, choose theta=arcsin(y) and lambda=y/sqrt(1-y^2). The function sin(t)-lambda cos(t) is nonpositive before theta and nonnegative after theta. Since 0<=r<=1,

\[
b-\lambda a
\leq\int_\theta^L(\sin t-\lambda\cos t)\,dt
=\sqrt{1-y^2}-\lambda(1-y).
\]

As 1-y=a, the lambda terms cancel. If y=1, then a=0 and nonnegativity forces r=0 almost everywhere, hence b=0. Reflecting t to L-t exchanges a and b and proves the other inequality. QED.

Bounding the two moments separately by one would be too weak for the argument below.

## W.2 Support hypotheses and the central symmetral

Let K be a compact convex body normalized by

\[
h_K(L)=1,\qquad h_K(3L)=0.
\tag{W.2}
\]

Its vertical span is one and K lies in 0<=y<=1. Assume

\[
0\leq\sigma_K=h_K+h_K''\leq dt
\tag{W.3}
\]

on each **open** coordinate quarter. Axis atoms are allowed. As in Note 31, the quarter restrictions are W^{2,infinity}, with endpoint derivative traces.

Define on an upper half

\[
d_h(t)=h(t)+h(t+L)+h'(t+L)-h'(t)-2,
\qquad0\leq t\leq L.
\tag{W.4}
\]

Endpoint derivatives are the traces from the two indicated quarters. The contact hypothesis is d_h>=0 for h=h_K and for its horizontal reflection h^rho(t)=h(-t)+sin(t). These are the two inequalities p<=q in Theorem 65. An almost-everywhere version extends to the trace endpoints by continuity.

Set

\[
C=\tfrac12\bigl(K+((0,1)-K)\bigr),
\qquad H(t)=h_C(t)=\tfrac12\bigl(h_K(t)+h_K(t+\pi)+\sin t\bigr).
\tag{W.5}
\]

Then C is centrally symmetric about (0,1/2), has vertical span one, and

\[
w_C(t)=H(t)+H(t+\pi)=h_K(t)+h_K(t+\pi)=w_K(t).
\tag{W.6}
\]

Its curvature density is the average of the two opposite densities, still between zero and one. Direct substitution also gives

\[
d_{h^\rho}(s)=d_h(3L-s),\qquad
d_H(t)=\tfrac12\bigl(d_h(t)+d_h(t+\pi)\bigr).
\tag{W.7}
\]

In the first identity the arguments of d_h range over the shifted lower quarter. The affine sine mode contributes zero to the linear part of d. Taking s=L-t shows that both terms in the second identity are nonnegative. Thus d_H>=0 on [0,L].

These are support identities. C is not assumed to follow either motion.

## W.3 A rectangle inside the auxiliary body

Let a_0=h_C(0)=h_C(pi). The rightmost face has vertical endpoints y_-<=y_+ in [0,1]. Central symmetry makes the top of the leftmost face have height 1-y_-. Write the top face as [ell,r] times {1}; the bottom face is [-r,-ell] times {0}.

Put f(t)=H(t), g(t)=H(t+L), with densities rho_f,rho_g. The support-contact coordinates give

\[
\begin{aligned}
a_0-r&=\int_0^L\rho_f\sin t\,dt,&
1-y_+&=\int_0^L\rho_f\cos t\,dt,\\
\ell+a_0&=\int_0^L\rho_g\cos t\,dt,&
y_-&=\int_0^L\rho_g\sin t\,dt.
\end{aligned}
\tag{W.8}
\]

Indeed A=f mu+f' nu has derivative rho_f nu and endpoints (a_0,y_+),(r,1). The second arc G=g nu-g' mu has derivative -rho_g mu and endpoints (ell,1),(-a_0,1-y_-). Integrating proves (W.8). The two rightmost traces remain distinct; this does not discard permitted axis faces.

Lemma WG1 implies

\[
r\geq a_0-\sqrt{1-y_+^2},\qquad
-\ell\geq a_0-\sqrt{2y_--y_-^2}.
\tag{W.9}
\]

The endpoint contact inequalities give

\[
-\ell\geq1+y_+-a_0,\qquad r\geq2-a_0-y_-.
\tag{W.10}
\]

To check the signs, p(0)=y_+, q(0)=a_0-ell-1, p(L)=1-r-a_0, and q(L)=y_--1. Applying p<=q at both endpoints gives (W.10).

Average the two lower bounds for r. Since y_-<=y_+,

\[
r\geq\frac{2-y_--\sqrt{1-y_+^2}}2
\geq1-\frac{y_++\sqrt{1-y_+^2}}2
\geq1-\frac1{\sqrt2}.
\tag{W.11}
\]

Similarly,

\[
-\ell\geq\frac{1+y_+-\sqrt{2y_--y_-^2}}2
\geq1-\frac{(1-y_-)+\sqrt{1-(1-y_-)^2}}2
\geq1-\frac1{\sqrt2}.
\tag{W.12}
\]

The final inequalities use z+sqrt(1-z^2)<=sqrt(2) for z in [0,1]. Put d=1-1/sqrt(2)>0. Both horizontal faces of C contain [-d,d] at their respective heights. Convexity gives

\[
[-d,d]\times[0,1]\subseteq C.
\tag{W.13}
\]

**Theorem WG2 (width gate from the two support hypotheses).**

\[
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|\quad(t\in\mathbb R).}
\tag{W.14}
\]

In particular w_K(t)>1 for pi/4<=|t|<pi/2.

**Proof.** The rectangle inclusion bounds the width of C; (W.6) transfers it to K. On [pi/4,pi/2], the displayed trigonometric lower bound is concave, has value 3/sqrt(2)-1>1 at the left endpoint and one at the right. It is strictly greater than one before that right endpoint. Absolute values handle negative angles. QED.

The rectangle is in C, not necessarily in K. Also, only the endpoint values of d_H are used after (W.7); the full contact inequalities remain necessary in the existing sharp-functional theorem, not in this width calculation itself.

## W.4 Full turns for competitive sofas

**Corollary WG3 (no independent full-turn hypothesis).** Let S be a compact connected ambidextrous body in the posed problem, with |S|>sqrt(2). Suppose its hull K in a unit-span normalization satisfies (W.3) and the two contact conditions (W.4). Then its correctly signed canonical motions have full quarter-turn endpoints.

**Proof.** Theorem 30 gives canonical endpoint magnitudes alpha,gamma in (0,L]. The two-strip bound (8.9) forces each to exceed pi/4; otherwise |S|<=sqrt(2). Their outgoing strips require w_K(alpha)<=1 and w_K(-gamma)<=1. Theorem WG2 rules out every magnitude in (pi/4,L), leaving alpha=gamma=L. Canonicalization retained the original body. QED.

[Corollary WG4 in Note 31](31-closed-curvature-class-theorem.md) therefore gives the sharp area and exact uniqueness theorem from just the curvature and contact conditions, without an extra full-turn premise. Bodies of area at most sqrt(2) are strictly below M by Note 10.

## W.5 Exact scope

The sufficient route has two support obligations in **one common normalization**: curvature domination and both contact inequalities. Full turns follow once they hold.

Neither condition is proved here for unrestricted maximizers. In particular, a bound only at floating normals does not give domination on all open quarters: an unknown partial terminal direction can be pinned yet lie inside one of those quarters. The implication does not eliminate that variational difficulty.

No feasible symmetrization or interpolation is presumed, and satisfaction of the two conditions in different coordinate normalizations is not enough. The proof removes a separate premise rather than declaring the unrestricted structural theorem complete.

All calculations are pen-and-paper. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. The result is a written argument subject to independent review.
