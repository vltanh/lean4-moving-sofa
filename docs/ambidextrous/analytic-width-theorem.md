# A pen-and-paper replacement for the computer-assisted width exclusion

**Result.** The width-at-most-two gate has the stronger analytic bound

\[
\boxed{|S|<41/25=1.64<M,}
\]

under the same geometric scope as the previous computer-assisted theorem CA-W. The proof below depends on elementary integrals, convexity, and the classical planar mixed-area inequality. It does **not** depend on the certificate tree, its replay, a numerical optimizer, a rational matrix calculation, or any of the sharp auxiliary-functional or curvature theorems in this branch.

The unrestricted ambidextrous optimum is not identified by this width theorem alone. The remaining global curvature/ordinary-area comparison is unchanged. The earlier certificate is retained as a historical, independent approach rather than silently deleted.

## 1. An analytic minimum for the two-hallway loss

Use the constants and notation of [LP1–LP2](analytic-width-loss-partition.md) and [AL1](analytic-width-localization.md):

\[
c=\sqrt{3/5},\quad s=\sqrt{2/5},\quad
q=s/c,\quad r=c/s,\quad a=8/15,
\quad \kappa=2-\frac{c+s-1}{cs}.
\]

The lower-turn positions use (cos t,sin t)=(c,s) and (s,c). Denote their left and right outer deficits by d_1,e_1 and d_2,e_2, respectively. They are nonnegative for canonical placements of any body contained in [0,2] times [0,1]. No relation between these two positions, or between the lower and upper turns, is assumed.

**Theorem AW1 (one-turn pair loss).** For every choice of these four nonnegative deficit parameters,

\[
\boxed{\Lambda>9/50.}
\tag{AW.1}
\]

**Proof.** Suppose Lambda<=9/50. Each single hallway's partition loss is at most Lambda. Lemma AL1 and its complementary-angle version therefore give

\[
3/20<d_1<3/7,\quad1/10<e_1<1/2,
\]

\[
1/10<d_2<1/2,\quad3/20<e_2<3/7.
\tag{AW.2}
\]

All the positive inner triangles lie inside the middle band and below height 1/2; all the outer-deficit triangles lie in their respective outside bands with heights below 1/2. Thus the partition loses none of these areas by truncation.

Define the convex function

\[
J(u,v)=\int_0^\infty\max\{0,u-qx,v-rx\}\,dx.
\]

Convexity follows pointwise from the maximum of affine functions. The outside-band loss is exactly J(d_1,d_2)+J(e_2,e_1). The positive inner triangles have areas

\[
A_1=\frac{cs}{2}(\kappa-rd_1-qe_1)^2,
\quad
A_2=\frac{cs}{2}(\kappa-qd_2-re_2)^2.
\]

Lemma LP2 therefore yields

\[
\Lambda\geq\Psi(d_1,d_2,e_1,e_2),
\]

where, defining the surrogate on all real parameter values,

\[
\begin{aligned}
\Psi={}&J(d_1,d_2)+J(e_2,e_1)\\
&+\frac{3cs}{11}\left[
(\kappa-rd_1-qe_1)_+^2+
(\kappa-qd_2-re_2)_+^2\right].
\end{aligned}
\tag{AW.3}
\]

This function is convex. It is invariant under

\[
(d_1,d_2,e_1,e_2)\longmapsto(e_2,e_1,d_2,d_1).
\]

Averaging a parameter vector with this image, put u=(d_1+e_2)/2 and v=(d_2+e_1)/2. Convexity gives

\[
\Psi\geq F(u,v):=2J(u,v)+\frac{6cs}{11}(\kappa-ru-qv)_+^2.
\tag{AW.4}
\]

This averaging concerns an **auxiliary convex scalar function**, not a purported feasibility-preserving symmetrization of bodies or motions.

For u>0 and u<v<(r/q)u=(3/2)u, the two positive roof lines in J cross before either relevant zero. Direct integration gives

\[
J(u,v)=\frac{u^2}{2q}+\frac{(v-u)^2}{2(r-q)}.
\tag{AW.5}
\]

Consider

\[
u_* =\frac{10\sqrt6\,\kappa}{109},\qquad
v_* =\frac{12\sqrt6\,\kappa}{109},\qquad
G_* =\kappa-ru_*-qv_* =\frac{55\kappa}{109}>0.
\tag{AW.6}
\]

Their ratio v_*/u_*=6/5 puts them strictly inside the regime of AW.5. There 1/(r-q)=2r and, with gamma=6cs/11,

\[
F(u,v)=ru^2+2r(v-u)^2+\gamma(\kappa-ru-qv)^2.
\]

Its two first derivatives vanish exactly when

\[
3u-2v=\gamma G,\qquad v-u=\gamma G/3.
\]

Substitution of AW.6 verifies both equations. Since F is convex everywhere, this stationary point is a **global** minimum, including parameters outside that local line-ordering regime. Its value is

\[
\boxed{F(u,v)\geq F(u_*,v_*)=
\frac{6\sqrt6}{109}\,\kappa^2.}
\tag{AW.7}
\]

For example the value follows by inserting u_*=5gamma G_*/3 and v_*=2gamma G_*; the resulting expression is gamma*kappa*G_*.

The elementary bounds sqrt(6)>22/9 and kappa>7/6 from AL.4 give

\[
\frac{6\sqrt6}{109}\kappa^2
>\frac{539}{2943}>rac9{50},
\]

where the last positive difference is 463/147150. Thus Lambda>9/50, contradicting the initial assumption. QED.

Every possible placement is covered: a loss outside the localized region is already too large by AL1; inside it LP2 and the global convex minimum apply. No unlisted contact cases or computer-enumerated boxes are used.

## 2. The stronger finite-position bound

**Corollary AW2 (four-position ordinary-area bound).** Suppose a measurable set S is contained in [0,2] times [0,1] and in two lower and two upper canonical hallway positions at the paired angles above. Then

\[
\boxed{|S|<41/25.}
\tag{AW.8}
\]

**Proof.** Apply AW1 separately to the independent lower and upper pairs. Lemma LP1 counts their losses on disjoint subsets of the rectangle, so

\[
|S|\leq2-\Lambda_- -\Lambda_+
<2-2(9/50)=41/25.
\]

The support bounds ensuring nonnegative deficits follow simply from containment in the rectangle. The finite envelope may be disconnected; the loss bound applies to its total area as well. QED.

## 3. Why every competitive width-two sofa visits these positions

This step repeats the relevant motion reduction to make its independence from the certificate explicit.

For a nonempty compact body S let K=conv(S). At a hallway frame (u,v), with outer offsets A,B, replace those offsets by h_K(u),h_K(v). The new outer bounds hold by definition, while the inner thresholds h_K(u)-1,h_K(v)-1 are no larger than the old ones. Thus the tightened hallway still contains S. These canonical placements vary continuously with the angle.

Lift the frame angle of each original motion continuously, starting at zero. If it first reaches either signed quarter turn, stop there: the outgoing normal then equals the incoming strip normal up to sign, so its width is at most one. Otherwise retain the original terminal angle, which lies between the two signed quarter turns and already supplies an outgoing strip of width at most one. Every intermediate angle was visited by continuity. Traversing its canonical placements in monotone angular order preserves the whole body and the endpoint arm conditions. This is the support-tightening and angle-erasure argument of Notes 8–10; it does not assume any area theorem.

A wrong-sign endpoint of magnitude at most pi/4 puts K in two unit strips with intersection area at most sqrt(2). A larger wrong-sign magnitude visits the wrong diagonal orientation; every horizontal section of that hallway has length sqrt(2), so intersection with the incoming unit-height strip again has area at most sqrt(2). Therefore a body of area greater than 8/5 has the conventional turning signs.

Let t_1=arctan(s/c) and t_2=arctan(c/s)=pi/2-t_1. Their larger angle satisfies

\[
\cos t_2=s=\sqrt{2/5}>5/8,
\]

since 2/5-25/64=3/320>0. If a correctly signed reduced endpoint had magnitude at most t_2, the two endpoint strips would give

\[
|S|\leq\sec(t_2)=\sqrt{5/2}<8/5,
\]

a contradiction. Hence a body with area above 8/5 visits both required angles for each turn. The two-strip estimate follows from the determinant of the map taking a point to its coordinates in the two unit-strip normals; its absolute determinant is cos(omega).

## 4. The analytic replacement theorem

**Theorem AW-W (width-at-most-two exclusion, without computer assistance).** Let S be a compact connected ambidextrous body in the common incoming-orientation convention. In an incoming unit-height strip, suppose its horizontal width is at most two. Then

\[
\boxed{|S|<41/25<411/250<M.}
\tag{AW.9}
\]

**Proof.** Translate S into [0,2] times [0,1]. If |S|<=8/5 there is already a strict bound below 41/25. Otherwise Section 3 supplies all four canonical positions, and AW2 applies.

For the comparison with the candidate, let z=149/500. The polynomial 4z^3+3z-1=-4551/31250000 is negative, so its increasing cubic's positive root Y exceeds z. Integrating 1/(1+x^2)>1-x^2 gives arctan z>z-z^3/3. Thus

\[
M=1+4Y^2+\arctan Y
>1+4z^2+z-z^3/3
=\frac{616648051}{375000000}
>\frac{411}{250}>\frac{41}{25}.
\]

The two final comparisons are rational arithmetic. QED.

The proof even allows incoming vertical span smaller than one; it uses only containment in a unit-height strip, not equality of the span. No stretching of S is performed.

## 5. Consequence and exact dependency boundary

Every global maximizer has area at least the feasible candidate value M. In any common incoming unit-span representative its horizontal width is therefore greater than two. This is the width consequence previously supplied by CA-W, now with a stronger constant and a pen-and-paper proof.

The analytic dependencies are exactly:

1. support tightening, continuity of angles, and the endpoint two-strip estimate;
2. the fixed disjoint loss partition LP1;
3. the planar mixed-area triangle inequality LP2;
4. the convex/tail localization AL1 and its four rational boundary checks;
5. the two-variable convex minimum AW.7.

No certificate binary, source hash, arithmetic implementation, numerical search, or computer-generated list is needed to check the theorem. The classical Brunn--Minkowski inequality enters only through the explicitly derived mixed-area estimate in LP2. The earlier computational proof and its reproduction files remain available for provenance and comparison.

Combining AW-W with the existing CW4 theorem still leaves the global curvature or equivalent ordinary-area comparison for unrestricted maximizers. This note closes the requested removal of computer assistance from the **width gate**, not that distinct remaining problem.

All new proofs are written and self-reviewed, not independently refereed or Lean-verified. No CI or Lean/Lake compilation was used.
