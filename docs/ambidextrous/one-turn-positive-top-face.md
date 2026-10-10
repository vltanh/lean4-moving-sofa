# Every signed weighted maximizing cap has a positive top face

**Scope.** This removes the T=0 exception from the finite shortening theorem TS1. The optimization problem is the signed one-turn objective Psi(U)=|U|-|N(U)|-W(U)/2 of PA2, not unrestricted ambidextrous area. It does not prove the sharp weighted value or remove the two-turn clipping term. Labels PT are local. Baseline: `4f9f92b94ef496c50ffb66ae4a38b233855768b1`.

The inputs are WP1--WP2 (polygon selection with summable one-sided facet defects), WR1 (the limiting end edges have height exactly 1/2), and the elementary geometry of finite niches. No equality of all facet derivatives, niche containment, contact pattern, or positive top face is assumed in the argument below.

## 1. The vertical projection identity for a finite niche

Let U_n be a downward-closed grid cap of positive width W_n. The upper allowed normals are theta_j=j*pi/(2n), 0<=j<=2n, and its floor is y=0. Let ell_j be its upper outer-facet lengths, including zero lengths at redundant normals, and T_n=ell_n its horizontal top-face length.

The finite niche N_n is the union of the strictly forbidden quadrants at j*pi/(2n), 1<=j<n, intersected with y>=0. The two source-wall normals are all theta_j with 0<j<2n and j different from n. Let tau_j be the total exposed length of its boundary on the corresponding inner wall, above the floor, as in WP2. Define J_n to be the projection of N_n intersected with y>0 onto the x-axis.

For a fixed x the niche roof is the positive part of the maximum of finitely many minima of two affine functions. It is continuous and piecewise affine. Each positive roof segment has outward normal theta_j; its horizontal projected length is its length times sin(theta_j). Distinct nonhorizontal wall normals prevent positive-length duplicate segments. Zero-height intervals contribute neither to J_n nor to these exposed lengths. Consequently

$$
\sum_{0<j<2n,\ j\ne n}\tau_j\sin\theta_j=|J_n|.
\tag{PT.1}
$$

This counts the measure of a possibly disconnected union, not the length of its convex hull. No cap clipping of the niche is used.

The upper boundary of the cap similarly projects once over its whole width. Its vertical end edges have zero horizontal projection. Thus

$$
W_n=T_n+\sum_{0<j<2n,\ j\ne n}\ell_j\sin\theta_j.
\tag{PT.2}
$$

**Lemma PT1 (projection balance with defects).** If ell_j<=tau_j+b_(n,j), with nonnegative errors and e_n=sum_j b_(n,j), then

$$
\boxed{T_n\ge W_n-|J_n|-e_n.}
\tag{PT.3}
$$

**Proof.** Multiply the inequalities by sin(theta_j), sum, and use PT.1--PT.2 and 0<=sin(theta_j)<=1. QED.

Only the one-sided inequalities of WP2 are needed. In particular, exact Euler balance and arbitrary inward facet variations have not been inserted as additional premises.

## 2. A robust gap between the niche and either vertical end

Let U be a cap in [l,r] times [0,1]. Suppose, for some d>0 and H<1, every point of U with x<=l+d has y<=H. Set delta=min(d,1-H)>0. Then every point of the full positive-height niche satisfies x>l+delta. The same conclusion holds for any finite list of interior turn angles.

To prove it, fix t in (0,pi/2), and put s=sin(t), c=cos(t), g=h_U(t+pi/2). Splitting the support test into x<=l+d and x>=l+d gives

$$
g+l s\le\max(Hc,c-ds).
$$

A forbidden point (x,y), with y>=0, obeys -x s+y c<g-1. Therefore

$$
x-l>\frac{1-g-ls}{s}
\ge\min\left\{\frac{1-Hc}{s},\ d+\frac{1-c}{s}\right\}
\ge\min(1-H,d)=\delta.
\tag{PT.4}
$$

Reflecting horizontally proves the right-end version: a right slab of width d and height at most H forces x<r-delta for every niche point.

**Lemma PT2 (end gaps persist under Hausdorff convergence).** Suppose caps U_n converge to a cap U whose upper roof at both horizontal endpoints is strictly less than one. Then there are delta_L,delta_R>0 such that, for all sufficiently large n, every finite niche of U_n lies horizontally between l_n+delta_L and r_n-delta_R, where [l_n,r_n] is its projection.

**Proof.** Compactness and the strict endpoint heights give small positive-width slabs at each end of U with maximum height below some H<1. Choose narrower slabs and a slightly larger H'<1. If a subsequence of U_n had a point violating one of those narrower bounds, compactness and l_n->l, r_n->r would give a violating limit point of U. Thus both slab bounds hold eventually. Apply PT.4 to them. The constants do not depend on the finite angular mesh. QED.

This is why niche-area convergence alone would not suffice: a very shallow positive roof could have a large projection while having tiny area. PT2 supplies uniform spatial gaps, not an unjustified continuity assertion for projection measure.

## 3. Excluding a point top face

**Theorem PT3 (positive top face for every weighted maximizer).** Every global maximizer U_* of the signed objective Psi has a top face of strictly positive length.

**Proof.** Select the prescribed U_* using WP1. Its polygon sequence U_n converges in Hausdorff distance, and WP2 gives PT.3 with e_n->0. WR1 says the upper endpoint heights of U_* are exactly 1/2. PT2 therefore supplies fixed positive delta_L,delta_R. It follows that

$$
|J_n|\le W_n-\delta_L-\delta_R,
\qquad
T_n\ge\delta_L+\delta_R-e_n.
$$

For large n the polygon top faces have a uniform positive length. Their heights tend to the height of U_*, namely one. Take convergent subsequences of their two endpoints. The limits belong to U_*, lie at height one, and remain separated horizontally by at least delta_L+delta_R. Convexity puts the segment between them in the top face of U_*. Thus its length is positive. QED.

The proof also works using weak convergence of curvature measures and the closed singleton {pi/2}; the endpoint argument above makes the inequality direction explicit. A jump at the top normal is obtained, not ruled out by open-quarter regularity.

## 4. Consequences: the point-top qualification in TS1 is removed

By PT3 every weighted maximizer qualifies for the finite horizontal shortening operation of TS1. Hence, for **every** weighted global maximizer,

$$
\boxed{H_N(U_*)\le1/2.}
\tag{PT.5}
$$

ST1 gives upper roof a(x)>=1/2 over the entire cap projection. Thus the full niche is contained in the cap. Its complement has nonempty interval fibers all containing y=1/2, is compact, and is connected. TS2's rational two-point test now gives, without a top-face exception,

$$
\boxed{x_R-x_{tl}\le9/4,\qquad x_{tr}-x_L\le9/4.}
\tag{PT.6}
$$

The required EA2 threshold is still two. PT.6 must not be substituted for it. The remaining excessive-arm range is (2,9/4] for all weighted maximizers, not merely those with positive top faces.

The symmetric two-turn construction TS.13 also applies to every weighted maximizer:

$$
|S_{U_*}|=2\Psi(U_*)+2\int\min(n,1-a)\,dx\ge2\Psi(U_*).
$$

The correction has its original nonnegative sign. This constructs an actual ambidextrous body from the auxiliary maximizer; it does not give an upper bound on arbitrary ambidextrous bodies or compute max Psi.

## 5. Dependency and validation boundary

The geometric projection and slab arguments are proved above. Their application to weighted maximizers depends on the branch's written WP and WR results. This is not independent verification of those historical proofs or kernel verification. The new theorem is not a consequence merely of W^(2,infinity) regularity: the summable facet inequalities are essential.

A regression checker for rational polygon roofs and the projection formula is a separate artifact. Such finite tests cannot replace the uniform slab argument or the mathematical passage to the limit. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used.
