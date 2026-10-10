# A global curvature majorant, with the ordinary-area question kept separate

This note constructs a single global repair of **every** planar convex hull. It does not need proximity to the candidate, a smooth input, protected windows, or contact order. It supplies the smallest support majorant whose curvature is at most one inside each coordinate quarter, and an exact positive formula for its hull-area gain.

It does **not** assert monotonicity of the area surviving the two moving corridors. That missing comparison is stated explicitly in Section 5. The labels GM are local to this note. This is a written argument, not a Lean-checked result.

## 1. A projective coordinate with no singular endpoints

Let J=[a,a+pi/2] be one coordinate quarter. Put m=a+pi/4 and

\[
k(t)=\cos(t-m),\qquad z=\tan(t-m),\qquad -1\leq z\leq1.
\]

Thus k is between 1/sqrt(2) and one, and dz/dt=1/k^2. For a convex-body support function h define

\[
\phi(z)=\frac{1-h(t)}{k(t)}.
\tag{GM.1}
\]

Write sigma=h+h'' for its nonnegative distributional curvature measure. Direct differentiation, first for a smooth h and then distributionally by testing and integration by parts, gives

\[
\phi''=k^3\,dz-z_*(k\,\sigma|_{\operatorname{int}J}).
\tag{GM.2}
\]

The notation z_* is pushforward of a measure. In the smooth case the density is (1-h-h'')k^3. The change of variables k^3 dz=k dt explains the weight on the measure term. In particular phi is Lipschitz and semiconcave with distributional second derivative at most the continuous positive density k^3.

Let Cphi be the greatest convex function below phi on [-1,1], including the endpoint inequalities. It is the lower convex envelope, not a convex approximation chosen by a numerical optimizer.

## 2. The envelope regularity required here

**Lemma GM1.** If a Lipschitz function phi on a compact interval satisfies phi''<=b(z)dz, where b is continuous and nonnegative, its lower convex envelope C has the same endpoint values as phi and

\[
0\leq C''\leq b(z)\,dz
\quad\text{on the open interval}.
\tag{GM.3}
\]

It is affine on each component of {C<phi}, is continuously differentiable in the interior, and has Lipschitz derivative there, with finite endpoint traces.

**Proof.** The envelope is the supremum of affine minorants. Endpoint equality follows by using a line through the endpoint with sufficiently large inward negative slope; Lipschitz continuity of phi bounds the necessary slope. In one dimension, an open interval where the envelope is strictly below the obstacle must be a straight chord: otherwise a short chord replacing a nonaffine portion of C raises it, remains convex, and remains below phi by the positive local gap. Exhausting a component gives affinity on the whole component.

At an interior contact x, semiconcavity supplies one-sided slopes phi'_-(x)>=phi'_+(x). Since phi-C has a minimum zero there,

\[
C'_-(x)\geq\phi'_-(x)\geq\phi'_+(x)\geq C'_+(x).
\]

Convexity gives the opposite ordering of the two C slopes. All four slopes are therefore equal. C is differentiable at contacts and is differentiable on the affine noncontact intervals; its derivative has no jumps.

For x<y, if both belong to the same affine component, the slope increment is zero. Otherwise move x to the first contact to its right when needed, and move y to the last contact to its left when needed. Call these u<=v. The affine parts have constant slope. At the contact points semiconcavity gives

\[
0\leq C'(y)-C'(x)=\phi'(v)-\phi'(u)
\leq\int_u^v b(z)dz\leq\int_x^y b(z)dz.
\]

The same argument applies by one-sided limits when an endpoint occurs. This proves the Lipschitz bound and the measure inequality (GM.3). In particular there is no unrecorded singular curvature of C. QED.

## 3. A canonical global operator on convex bodies

For each quarter define

\[
\bar h(t)=1-k(t)C\phi(z(t)),
\tag{GM.4}
\]

and glue the four functions at the coordinate-axis normals. Let u=bar h-h.

**Theorem GM2 (least global quarter-curvature majorant).** The glued function is the support function of a compact convex body R(K). It has the following properties:

\[
K\subseteq R(K),\qquad
\bar h=h\text{ at all four axis normals},
\qquad
0\leq\bar h+\bar h''\leq1\text{ on every open quarter}.
\tag{GM.5}
\]

The curvature bound is a measure statement. The body R(K) is the smallest support majorant with this upper bound and the same axis supports: every support function g>=h satisfying g+g''<=1 inside the quarters has g>=bar h. The operator is idempotent, order preserving, and commutes with translations of bodies.

**Proof.** Since Cphi<=phi, bar h>=h. Lemma GM1 gives equal endpoint values. Applying (GM.2) in reverse to (GM.4), the inequalities 0<=C''<=k^3 dz give 0<=bar h+bar h''<=dt on the quarter. In particular bar h is W^{2,infinity} there, with finite derivative traces.

At a left endpoint u=0 and u>=0 imply u'_+>=0; at a right endpoint they imply u'_-<=0. When two quarters are glued, the jump of the derivative increases by a nonnegative amount relative to the original nonnegative axis atom. Hence the whole periodic curvature measure is nonnegative. The supporting-half-plane construction for a periodic function with nonnegative h+h'' (as in Lemma 43) gives a compact convex body with support bar h. It contains K. Its four axis supports agree, so it is bounded by the same coordinate rectangle and has the same horizontal and vertical spans.

For minimality, if g>=h and g+g''<=dt, then (1-g)/k is convex and below phi. It is therefore below Cphi, so g>=bar h. Applying this to bar h proves idempotence. Monotonicity follows because convex envelopes preserve pointwise order; the two order reversals in (GM.1) and (GM.4) cancel. A translation adds a linear combination of cos(t) and sin(t) to h. Dividing it by k makes it affine in z. Convex envelopes commute with addition of affine functions, proving translation covariance. QED.

This is an all-quarter construction, not the unsupported instruction to smooth a support function until it has the desired curvature. It may change the hull by a definite amount, consistent with the closedness obstruction of Note 50.

The coordinate-rectangle support is a useful barrier: on each quarter it is the solution r''+r=0 with the same endpoint values. Convexity of K gives r>=h. The function (1-r)/k is convex, so it is below Cphi and bar h<=r. Thus the construction cannot escape the original containing rectangle.

Also, for two input supports,

\[
\|R(h_1)-R(h_2)\|_\infty\leq\sqrt2\|h_1-h_2\|_\infty.
\tag{GM.6}
\]

Indeed transformation (GM.1) amplifies the uniform norm by at most sqrt(2), convex envelopes are nonexpansive in that norm, and multiplication by k amplifies it by at most one.

## 4. The hull-area gain is exact and strictly positive

On {u>0}, Cphi is affine. Hence the repaired curvature is exactly dt there. Since u vanishes on the contact set and at the axis normals,

\[
\int_J u\,d\sigma_{\bar h}=\int_Ju\,dt.
\]

Distributional integration by parts, using u=0 at the endpoints, gives

\[
\int_Ju\,d\sigma_h
=\int_Ju+\int_Ju'^2-\int_Ju^2.
\tag{GM.7}
\]

The support-area formula and its exact quadratic expansion now imply

\[
\boxed{|R(K)|-|K|
=\sum_J\left[\int_Ju+
\frac12\int_J(u'^2-u^2)\right].}
\tag{GM.8}
\]

Axis atoms contribute zero because u is zero there. The measure pairing in (GM.7) includes all input edge and singular-continuous curvature; it is not replaced by a density integral.

The Dirichlet inequality on a quarter gives integral u'^2>=4 integral u^2. Therefore

\[
|R(K)|-|K|\geq
\sum_J\left[\int_Ju+\frac38\int_Ju'^2\right],
\tag{GM.9}
\]

which is positive unless the repair is identically zero. This is a **hull-area** statement. Niche changes have not been subtracted from it.

## 5. A precise testable route to closure, not a claimed comparison

For a normalized hull of width W>2, R(K) has that same width and the curvature cap. Its widths consequently obey CW1, so all its nonvertical directions in the reduced angular range have width greater than one. An originally partial endpoint is therefore not preserved as an endpoint of a sofa whose actual hull is R(K). One cannot invoke the old motions unchanged for the whole repaired hull.

One potentially sufficient assertion, still **unproved**, is

\[
|S|\leq\widetilde{\mathcal Q}(h_{R(\operatorname{conv}S)})
\tag{GM.10}
\]

for every competitive normalized ambidextrous S of width W>2. It would allow AF3 to finish the upper bound without requiring R(K) itself to be the hull of a feasible connected sofa. For uniqueness the equality case would need to recover the original body; (GM.10) alone does not provide that recovery.

A different sufficient route is an actual feasible, area-nondecreasing repair with a strictly increasing area whenever R(K)!=K. Equations (GM.8)-(GM.9) do **not** prove either route: the increased inner thresholds can remove old surviving area, and their connectedness or partial-endpoint costs cannot be dropped.

The role of this note is to replace a collection of protected repairs by a canonical **global candidate operator** and its fully specified hull gain. Subsequent tests and geometric analysis must establish or refute the ordinary-area comparison separately. The unrestricted proof remains open.
