# 64. The curvature and contact hypotheses already force full turns

This note removes the **separate full-quarter-turn assumption** from the application of Theorem 65 to competitive bodies. It does not prove the remaining curvature or contact inequalities for an unrestricted maximizer.

The key intermediate body is a Minkowski central symmetral used only to compare widths. It is **not asserted to be a feasible sofa**. No feasibility-preserving symmetrization, symmetry of an optimizer, or new maximizer-selection theorem is assumed.

All calculations are pen-and-paper. No CI, Lean compilation, numerical experiment, or computer algebra is used.

## 64.1 Two moment inequalities on a quarter circle

Put L=pi/2. Let r:[0,L] -> [0,1] be measurable and write

\[
a=\int_0^L r(t)\cos t\,dt,
\qquad b=\int_0^L r(t)\sin t\,dt.
\]

**Lemma 118 (quarter moments).**

\[
0\leq a,b\leq1,\qquad
b\leq\sqrt{2a-a^2},\qquad
 a\leq\sqrt{2b-b^2}.
\tag{64.1}
\]

**Proof.** The first bounds follow by integration. For the first curved bound put y=1-a. When 0<=y<1, choose theta=arcsin(y) and lambda=y/sqrt(1-y^2). The function sin(t)-lambda cos(t) is nonpositive before theta and nonnegative after theta. Since 0<=r<=1,

\[
b-\lambda a
\leq\int_\theta^L(\sin t-\lambda\cos t)\,dt
=\sqrt{1-y^2}-\lambda(1-y).
\]

As 1-y=a, the lambda terms cancel, giving the assertion. If y=1, then a=0 and nonnegativity forces r=0 almost everywhere, so b=0. Reflecting the parameter t to L-t exchanges a and b and proves the other inequality. QED.

This elementary rearrangement bound will control the horizontal displacement of an arc from its vertical displacement. Bounding both displacements separately by one would be too weak for the conclusion below.

## 64.2 The precise support hypotheses

Let K be a compact convex body normalized by

\[
h_K(L)=1,\qquad h_K(3L)=0.
\tag{64.2}
\]

Thus its vertical span is one and K lies in 0<=y<=1. Assume its curvature measure satisfies

\[
0\leq\sigma_K=h_K+h_K''\leq dt
\tag{64.3}
\]

on each **open** coordinate quarter. Axis atoms are allowed. As explained in Note 31, the restrictions are W^{2,infinity}, so their endpoint derivative traces exist.

On an upper half define

\[
d_h(t)=h(t)+h(t+L)+h'(t+L)-h'(t)-2,
\qquad 0\leq t\leq L.
\tag{64.4}
\]

Endpoint derivatives in this expression are the traces from the two indicated quarters. The contact hypothesis is d_h>=0 for h=h_K and for the horizontal reflection

\[
h^\rho(t)=h(-t)+\sin t.
\tag{64.5}
\]

Equivalently these are the two inequalities p<=q used in Theorem 65. An almost-everywhere version holds at all trace endpoints by continuity on each closed quarter.

## 64.3 Central symmetrization preserves these hypotheses and every width

Define

\[
C=\tfrac12\bigl(K+((0,1)-K)\bigr),
\qquad
H(t)=h_C(t)=\tfrac12\bigl(h_K(t)+h_K(t+\pi)+\sin t\bigr).
\tag{64.6}
\]

The body C is centrally symmetric about (0,1/2), has vertical span one, and has exactly the same width as K in every direction:

\[
w_C(t)=H(t)+H(t+\pi)=h_K(t)+h_K(t+\pi)=w_K(t).
\tag{64.7}
\]

Its curvature density on each open quarter is the average of the two opposite densities of K, and hence is still between zero and one.

For the contact condition, direct substitution gives

\[
d_{h^\rho}(s)=d_h(3L-s),
\qquad
d_H(t)=\tfrac12\bigl(d_h(t)+d_h(t+\pi)\bigr).
\tag{64.8}
\]

Here d_h on a shifted quarter means the same expression (64.4) with shifted arguments. The added sine mode contributes zero to that expression's linear part. As s=L-t covers [0,L], the original two contact conditions make both terms on the right nonnegative. Thus d_H>=0 on [0,L].

These are identities of support functions. No claim that C follows either motion is used or needed.

## 64.4 A rectangle inside the symmetral

Let a_0=h_C(0)=h_C(pi)>0. The rightmost exposed face has vertical endpoints y_-<=y_+ in [0,1]. Central symmetry makes the top of the leftmost face have height 1-y_-. Let the top horizontal face be [ell,r] times {1}; its centrally reflected bottom face is [-r,-ell] times {0}.

Write f(t)=H(t), g(t)=H(t+L), and let rho_f,rho_g be their densities. The support-contact coordinates give

\[
a_0-r=\int_0^L\rho_f\sin t\,dt,
\qquad 1-y_+=\int_0^L\rho_f\cos t\,dt,
\]

\[
\ell+a_0=\int_0^L\rho_g\cos t\,dt,
\qquad y_-=\int_0^L\rho_g\sin t\,dt.
\tag{64.9}
\]

For completeness, the first arc is A=f mu+f' nu, whose a.e. derivative is rho_f nu. Its endpoints are (a_0,y_+) and (r,1). The second arc is G=g nu-g' mu, whose derivative is -rho_g mu; its endpoints are (ell,1) and (-a_0,1-y_-). Integrating their coordinates proves (64.9), including any permitted axis faces through the one-sided traces.

Lemma 118 therefore gives

\[
r\geq a_0-\sqrt{1-y_+^2},
\qquad
-\ell\geq a_0-\sqrt{2y_--y_-^2}.
\tag{64.10}
\]

The endpoint contact inequalities d_H(0)>=0 and d_H(L)>=0 give, respectively,

\[
-\ell\geq1+y_+-a_0,
\qquad r\geq2-a_0-y_-.
\tag{64.11}
\]

Indeed p(0)=y_+, q(0)=a_0-ell-1, p(L)=1-r-a_0, and q(L)=y_--1.

Average the two lower bounds for r in (64.10)-(64.11). Since y_-<=y_+,

\[
r\geq\frac{2-y_--\sqrt{1-y_+^2}}2
\geq1-\frac{y_++\sqrt{1-y_+^2}}2
\geq1-\frac1{\sqrt2}.
\tag{64.12}
\]

Similarly,

\[
-\ell\geq\frac{1+y_+-\sqrt{2y_--y_-^2}}2
\geq1-\frac{(1-y_-)+\sqrt{1-(1-y_-)^2}}2
\geq1-\frac1{\sqrt2}.
\tag{64.13}
\]

The last inequalities are Cauchy-Schwarz applied to z+sqrt(1-z^2), for z in [0,1]. Put d=1-1/sqrt(2)>0. Both horizontal faces of C contain [-d,d] at their respective heights. Convexity therefore yields

\[
[-d,d]\times[0,1]\subseteq C.
\tag{64.14}
\]

**Theorem 119 (width gate from the two support hypotheses).** Every K satisfying (64.2)-(64.5) obeys

\[
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|\quad(t\in\mathbb R).}
\tag{64.15}
\]

In particular w_K(t)>1 for pi/4<=|t|<pi/2.

**Proof.** The rectangle inclusion gives the displayed width bound for C; (64.7) transfers it to K. On [pi/4,pi/2] the function (2-sqrt(2))cos(t)+sin(t) is concave. Its value at the left endpoint is 3/sqrt(2)-1>1, and its value at the right is one. It is therefore strictly greater than one before the right endpoint. Absolute values give the reflected assertion. QED.

The rectangle in (64.14) is in C, not necessarily in K. The proof deliberately uses equality of widths rather than assuming a rectangle or a feasible symmetrization of the original body.

## 64.5 Full turns follow for competitive sofas

**Corollary 120 (no independent full-turn hypothesis).** Let S be a compact connected ambidextrous body in the posed problem, with |S|>sqrt(2). Suppose its hull K in a unit-span normalization satisfies the curvature and two contact hypotheses above. Then both of its correctly signed canonical motions can be taken to be full quarter turns.

**Proof.** Theorem 30 gives the canonical endpoint magnitudes alpha,gamma in (0,L]. The two-strip bound (8.9) forces each to exceed pi/4: an endpoint of magnitude at most pi/4 would give |S|<=sqrt(2). Its outgoing strip requires w_K(alpha)<=1 or w_K(-gamma)<=1. Theorem 119 rules out every magnitude in (pi/4,L), so alpha=gamma=L. The original canonicalization contains the same body; no new feasibility-preserving deformation is required. QED.

Combining with Theorem 65 gives area at most M and exact uniqueness for every body satisfying just the two support hypotheses, even when its original motions were arbitrary or partial. Bodies of area at most sqrt(2) are strictly below M by Note 10.

## 64.6 What this closes, and what remains

The earlier sufficient route listed three independent structural outputs. For this route they reduce to **two**: curvature-measure domination and both contact inequalities, in one common unit-span normalization. Once those are obtained for a relevant maximizer, full endpoints follow from this note.

The argument does not give either of those two hypotheses for every maximizer, does not treat their satisfaction in different normalizations as sufficient, and does not supply a feasibility-preserving symmetrization. Thus it removes one genuine obligation without claiming an unrestricted solution.
