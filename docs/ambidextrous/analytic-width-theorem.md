# A pen-and-paper replacement for the computer-assisted width exclusion

**Result.** The width-at-most-two gate has the stronger analytic bound

\[
\boxed{|S|<41/25=1.64<M.}
\]

It has the same geometric scope as the previous computer-assisted theorem CA-W. The proof uses elementary integrals, convexity, and the classical planar mixed-area inequality. It does **not** depend on the certificate tree, its replay, a numerical optimizer, a rational matrix calculation, or any sharp auxiliary-functional or curvature theorem in this branch.

The unrestricted ambidextrous optimum is not identified by this width theorem alone. The remaining global curvature/ordinary-area comparison is unchanged. The earlier certificate is retained as a historical independent approach.

## 1. An analytic minimum for the two-hallway loss

Use the constants and notation of [LP1–LP2](analytic-width-loss-partition.md) and [AL1](analytic-width-localization.md):

\[
c=\sqrt{3/5},\quad s=\sqrt{2/5},\quad
q=s/c,\quad r=c/s,\quad a=8/15,
\quad \kappa=2-\frac{c+s-1}{cs}.
\]

The lower-turn positions use (cos t,sin t)=(c,s) and (s,c). Denote their left and right outer deficits by d_1,e_1 and d_2,e_2, respectively. They are nonnegative for canonical placements of any body in [0,2] times [0,1]. No relation between these two positions, or between the lower and upper turns, is assumed.

**Theorem AW1 (one-turn pair loss).** For every choice of these four nonnegative deficit parameters,

\[
\boxed{\Lambda>9/50.}
\tag{AW.1}
\]

**Proof.** Suppose Lambda<=9/50. Each single hallway's partition loss is at most Lambda. Lemma AL1 and its complementary-angle version give

\[
3/20<d_1<3/7,\quad1/10<e_1<1/2,
\qquad1/10<d_2<1/2,\quad3/20<e_2<3/7.
\tag{AW.2}
\]

All positive inner triangles lie in the middle band and below height 1/2. All outer-deficit triangles lie in the outside bands with heights below 1/2. Thus the partition truncates none of these areas.

Define the convex function

\[
J(u,v)=\int_0^\infty\max\{0,u-qx,v-rx\}\,dx.
\]

Convexity follows pointwise from the maximum of affine functions. The outside-band loss is exactly J(d_1,d_2)+J(e_2,e_1). The two positive inner triangles have areas

\[
A_1=\frac{cs}{2}(\kappa-rd_1-qe_1)^2,
\qquad A_2=\frac{cs}{2}(\kappa-qd_2-re_2)^2.
\]

Lemma LP2 yields Lambda>=Psi, where the following surrogate is defined on all real parameter values:

\[
\begin{aligned}
\Psi={}&J(d_1,d_2)+J(e_2,e_1)\\
&+\frac{3cs}{11}\left[(\kappa-rd_1-qe_1)_+^2+
(\kappa-qd_2-re_2)_+^2\right].
\end{aligned}
\tag{AW.3}
\]

It is convex and invariant under (d_1,d_2,e_1,e_2) mapping to (e_2,e_1,d_2,d_1). Average a vector with this image and put u=(d_1+e_2)/2, v=(d_2+e_1)/2. Then

\[
\Psi\geq F(u,v):=2J(u,v)+\frac{6cs}{11}(\kappa-ru-qv)_+^2.
\tag{AW.4}
\]

This is averaging in an auxiliary convex scalar function, **not** a claimed feasibility-preserving symmetrization of sofas or motions.

For u>0 and u<v<(r/q)u=(3/2)u, the two positive roof lines cross before their relevant zeros. Direct integration gives

\[
J(u,v)=\frac{u^2}{2q}+\frac{(v-u)^2}{2(r-q)}.
\tag{AW.5}
\]

Set

\[
u_* =\frac{10\sqrt6\,\kappa}{109},\qquad
v_* =\frac{12\sqrt6\,\kappa}{109},\qquad
G_* =\kappa-ru_*-qv_* =\frac{55\kappa}{109}>0.
\tag{AW.6}
\]

Their ratio is 6/5, strictly inside the regime of AW.5. There 1/(r-q)=2r and, with gamma=6cs/11,

\[
F(u,v)=ru^2+2r(v-u)^2+\gamma(\kappa-ru-qv)^2.
\]

Its first derivatives vanish exactly when

\[
3u-2v=\gamma G,\qquad v-u=\gamma G/3.
\]

AW.6 satisfies both equations. Since F is convex everywhere, this is a global minimum, including parameters outside that local line-ordering regime. Its value is

\[
\boxed{F(u,v)\geq F(u_*,v_*)=\frac{6\sqrt6}{109}\kappa^2.}
\tag{AW.7}
\]

For instance, substitution of u_*=5gamma G_*/3 and v_*=2gamma G_* makes the value gamma*kappa*G_*.

The elementary bounds sqrt(6)>22/9 and kappa>7/6 give

\[
\frac{6\sqrt6}{109}\kappa^2>
\frac{539}{2943}>\frac{9}{50};
\]

the last positive difference is 463/147150. This contradicts Lambda<=9/50 and proves AW1. QED.

All placements are covered: outside AL1's region a single hallway already supplies enough loss; inside it LP2 and the convex minimum apply. There are no unlisted computer-enumerated cases.

## 2. The stronger finite-position bound

**Corollary AW2.** If a measurable S is contained in [0,2] times [0,1] and in the four canonical hallway positions above, then

\[
\boxed{|S|<41/25.}
\tag{AW.8}
\]

**Proof.** Apply AW1 separately to the independent lower and upper pairs. LP1 counts their losses on disjoint subsets of the rectangle, so

\[
|S|\leq2-\Lambda_- -\Lambda_+<2-2(9/50)=41/25.
\]

The nonnegative deficit bounds follow from containment in the rectangle. The finite envelope can be disconnected: its total area satisfies the same bound whenever the placements have those support bounds. QED.

## 3. Every competitive width-two sofa visits these positions

Here is the relevant motion reduction, repeated to make independence from the certificate explicit.

For nonempty compact S let K=conv(S). At a hallway frame (u,v), replace its outer offsets A,B by h_K(u),h_K(v). The new outer bounds hold by definition, and the inner thresholds h_K(u)-1,h_K(v)-1 are no larger than the old thresholds. Thus S still fits. The canonical placements vary continuously with their angle.

Lift the frame angle continuously from zero. If it first reaches either signed quarter turn, stop there: the outgoing normal is then the incoming strip normal up to sign, so its width is at most one. Otherwise retain the original terminal angle, between the signed quarter turns, with its existing outgoing width at most one. Every intermediate angle was visited by continuity. Traversing its canonical placements in monotone angular order preserves S and the endpoint arms. This is the support-tightening/angle-erasure argument of Notes 8–10, not an application of any area theorem.

A wrong-sign endpoint of magnitude at most pi/4 gives a two-strip bound |S|<=sqrt(2). A larger wrong-sign magnitude visits the wrong diagonal; every horizontal hallway section there has length sqrt(2), so intersecting the incoming unit-height strip gives the same bound. Thus area greater than 8/5 forces the conventional signs.

Let t_1=arctan(s/c) and t_2=arctan(c/s)=pi/2-t_1. The larger angle satisfies

\[
\cos t_2=\sqrt{2/5}>5/8,
\]

because 2/5-25/64=3/320>0. A reduced endpoint of magnitude at most t_2 would give

\[
|S|\leq\sec t_2=\sqrt{5/2}<8/5
\]

from its two endpoint strips. The strip-intersection area is at most 1/cos(omega), by the determinant of the two strip normals. Therefore every body of area above 8/5 visits both required angles for each turn. No extension from a partial endpoint to a full quarter turn is asserted.

## 4. The analytic replacement theorem

**Theorem AW-W (width-at-most-two exclusion without computer assistance).** Let S be a compact connected ambidextrous body in the common incoming-orientation convention. If its horizontal width in an incoming unit-height strip is at most two, then

\[
\boxed{|S|<41/25<411/250<M.}
\tag{AW.9}
\]

**Proof.** Translate S into [0,2] times [0,1]. Area at most 8/5 is already strictly below 41/25. Otherwise Section 3 supplies all four positions, and AW2 applies.

To compare with the candidate, put z=149/500. Since

\[
4z^3+3z-1=-4551/31250000<0,
\]

the positive root Y of the increasing cubic exceeds z. Integrating 1/(1+x^2)>1-x^2 gives arctan z>z-z^3/3. Hence

\[
M=1+4Y^2+\arctan Y
>1+4z^2+z-z^3/3
=\frac{616648051}{375000000}
>\frac{411}{250}>\frac{41}{25}.
\]

The final comparisons are rational arithmetic. QED.

The proof allows incoming vertical span smaller than one: only containment in the unit-height strip is used. No stretching of the body is performed.

## 5. Dependency boundary

Every global maximizer has area at least the feasible candidate value M, so every common incoming unit-span representative has horizontal width greater than two. This is the consequence previously supplied by CA-W, with a stronger constant and an analytic proof.

The dependencies are exactly support tightening and the two-strip estimate; the disjoint partition LP1; the mixed-area triangle inequality LP2; the localization AL1 with four rational boundary checks; and the convex minimum AW.7. Classical Brunn--Minkowski is used only to derive the mixed-area estimate in LP2.

No certificate binary, source hash, arithmetic implementation, numerical search, or generated case list is needed to check these arguments. The old computational certificate is preserved for provenance. Combining AW-W with the earlier CW4 theorem still leaves the global curvature or equivalent ordinary-area comparison for unrestricted maximizers. This closes removal of computer assistance from the **width gate**, not that distinct remaining problem.

All proofs are written and self-reviewed, not independently refereed or Lean-verified. No CI or Lean/Lake compilation was used.
