# 05. A specified right-angle maximizer: penalized polygon proof

Date: 2026-10-02. Status: proposed pen-and-paper extension of Baek's argument, not Lean-checked or independently reviewed. The new ingredients are the selection, perturbation-error and limiting arguments below; the scalar arm-length bootstrap is the existing one in Chapter 6.

Put L=pi/2. Let K_* be a standard cap attaining the global maximum of A_L(K). By the existing optimality and balanced-cap existence theorems, this value is |G|. This note argues that K_* satisfies the injectivity condition, without assuming that K_* is a limit of exact maximum polygon caps.

## 1. Compact approximation of the specified cap

Choose R with K_* strictly inside the horizontal bounds of [-R,R] x [0,1]. Let X be the compact family of standard right-angle caps contained in this box, and let X_n be its polygon caps with the dyadic normal mesh of spacing delta_n=L/2^n. The artificial horizontal bounds are constraints on the family, not additional allowed polygon normals.

Write A_n for the polygon upper approximation on this mesh. On X,

    A_n decreases uniformly to A.

Here are details of the continuity issue for the niche. A wedge at angle 0<t<L has vertical height above the x-axis

    F(K,x,t) = max(0, min(
      (h_K(t)-1-x cos t)/sin t,
      (h_K(t+L)-1+x sin t)/cos t)).

Its horizontal support is between the two horizontal extremes of K: use h_K(t)<=x_max cos t+sin t and its reflected inequality. Consequently x may be confined to [-R,R]. Set F(K,x,0)=F(K,x,L)=0. Uniform Lipschitz bounds for the support functions, together with h_K(L)=1, give F<=C_R t near 0 and F<=C_R(L-t) near L. Thus F is jointly continuous even at the two endpoints. The full niche height is max_t F, and the polygon height is the maximum over the mesh. These maxima converge uniformly on the compact parameter space; their integrals in x are the niche areas.

The circumscribed polygon caps decrease to K. For each fixed mesh their areas depend continuously on the sampled heights. One way to see the required nondegeneracy is to take a top contact point of K: the finite nonhorizontal constraints and the bottom constraint enclose a triangle below that point with positive area, even when K itself degenerates to a vertical segment. The finite intersections are uniformly bounded for a fixed mesh. Continuity of convex-body area and Dini's theorem give uniform convergence of their areas on X. Subtracting the two area limits proves the claim for A_n.

Let e_n=sup_X |A_n-A|. The recovery caps r_n=C_n(K_*) converge to K_*, eventually lie strictly inside the box, and satisfy A_n(r_n)=A_n(K_*)>=A(K_*): their sampled supports are exactly those of K_*.

Take the selector

    P(K)=integral_0^pi (h_K-h_{K_*})^2,

and lambda_n>0 such that lambda_n->0 and e_n/lambda_n->0, for example sqrt(e_n)+1/n. Choose K_n to maximize A_n-lambda_n P on X_n. The selection lemma of note 04 proves K_n->K_*. In particular the artificial box constraints are inactive for all sufficiently large n.

## 2. Actual facet perturbations and the mesh-scale error

Fix a sampled normal t other than L. If its facet has positive length, increase its defining height by epsilon>0, sufficiently small for this polygon and facet. The resulting polygon contains K_n and keeps every other sampled support unchanged. Its support at t increases by epsilon: a point in the relative interior of the positive facet has strictly positive slack at the other, nonparallel constraints. Thus the changed assigned heights are actual sampled supports in this case.

Between consecutive mesh normals the support is the sine interpolation of the two endpoint heights, including when a facet is redundant. The support change divided by epsilon is therefore a sine hat on the two cells adjacent to t. Its absolute value is at most 1 there. At the first mesh facet, the missing normal 0 is the bottom-right corner, and the formula on [0,delta_n] is cos(s)/cos(delta_n), at most 2. The reflected last cell is analogous. On [0,pi] the support change is supported on length at most 2 delta_n and is bounded by 2 epsilon.

The penalty derivative therefore has absolute value at most C_R delta_n, by note 04. The unpenalized one-sided area derivative is

    d A_n / d epsilon = sigma_n(t)-tau_n(t),

where tau is the corresponding inner-polyline length. This is the Nef-polygon variation calculation of Lemma 3.4.7, before any assumption of maximality. Penalized maximality gives

    sigma_n(t) <= tau_n(t)+C_R lambda_n delta_n.         (1)

If the facet length is zero, (1) is automatic because tau_n(t)>=0. No inward perturbation, positive length at a neighboring facet, or exact balancedness is assumed. The pinned top normal L is not needed for the following density estimates.

## 3. The geometric estimate survives approximate balance

For an arbitrary polygon cap in the fixed box, the geometric part of the proof of Theorem 6.3.3 gives, at each t in the first-quadrant mesh,

    tau_n(t) <= |g_n^+(t)-1| delta_n
                 + max(0,delta_n-sigma_n(t)) + C_R delta_n^2.     (2)

To separate geometry from the original maximality hypothesis: intersect the relevant inner-wall boundary with the union of the half-planes d(t-delta), d(t), d(t+delta). Its length is bounded by the larger of the two tangent-ray lengths computed in Lemma 6.3.2. Since g^-<=g^+, this contribution is at most |g^+-1| delta+O_R(delta^2). The remaining portion is on a segment of length max(0,2 tan(delta/2)-sigma(t)). The endpoint angles 0 and L contribute empty open quadrants above the x-axis, so the same inclusion works for the first and last mesh cells. This proves (2).

The paper obtains a fixed diameter bound for its maximum polygons. Here the chosen box supplies a possibly larger uniform bound; this changes only C_R. The vertex and tangent-ray computations in the repository (`inj_polygon_vertices_at`, `inj_polygon_g_eq`, and `inj_param_minus_length`) already have the hypothesis `IsPolygonCap`, not exact maximality.

Combine (1) and (2). Splitting into sigma_n(t)<=delta_n and sigma_n(t)>delta_n yields

    sigma_n(t) <= k_0(g_n^+(t)) delta_n
                   + C_R (delta_n^2+lambda_n delta_n),           (3)

where k_0(s)=max(|s-1|,(|s-1|+1)/2). The same bound holds after reflection. The cumulative error over O(1/delta_n) facets is O_R(delta_n+lambda_n), and tends to zero.

## 4. Pass to surface-area measures

Hausdorff convergence K_n->K_* gives uniform convergence of support functions and weak convergence of their surface-area measures. At almost every normal s, K_* has a unique support point. If mesh angles s_n converge to such an s, the corresponding support points of K_n converge to that point: every subsequential limit lies in the support face of K_* at s, which is a singleton. Consequently the piecewise-constant samples g_n^+ used in (3) converge almost everywhere to g_{K_*}, and they are uniformly bounded by the box diameter.

Testing (3) against continuous nonnegative functions compactly supported away from L and using dominated convergence gives

    sigma_{K_*}|[0,L) <= k_0(g_{K_*}(t)) dt.                      (4)

This includes absence of an atom at 0: there are no polygon facets just below 0, and the masses in the first mesh cells obey (3). The reflected argument gives the corresponding inequality on (L,pi], including absence of an atom at pi. An atom at the top normal L is allowed.

## 5. The analytic bootstrap uses (4), not the definition of balancedness

The two measure inequalities supply absolutely continuous curvature measures on the open upper quadrants and no vertical end faces. The existing arm identities then give continuous, absolutely continuous arm functions with f(0)=g(L)=1 and

    f(t) >= 1+integral_0^t m_0(g(u)) du,
    g(t) >= 1+integral_t^L m_0(f(u)) du,                         (5)

where m_0(s)=s-k_0(s). The reflection swaps the two inequalities. These are the ingredients of the scalar bootstrap in Section 6.5; a balanced-cap label is not an additional analytic input.

For completeness its universal iteration starts from F_0=0 and sets

    F_{j+1}(t)=max(F_j(t), 1+integral_0^t m_0(F_j(L-u)) du).

Monotonicity of m_0 and (5) prove f(t)>=F_j(t) and g(t)>=F_j(L-t) by induction. The existing scalar Lemma 6.5.5 proves F_11(t)>1 for 0<t<=L (the repository corrects the paper's endpoint typo). It follows that f(t)>1 and g(t)>1 for 0<t<L.

The curvature absolute continuity also gives a continuously differentiable inner-corner curve, with

    x_K'(t)=-(f(t)-1)u_t+(g(t)-1)v_t.

Thus its two scalar components along u_t,v_t have the strict signs required by `InjCond3`; the curvature densities give `InjCond1`, and the preceding regularity gives `InjCond2`. This is the final analytic step of Theorem 6.1.1 with (4) in place of its original balanced-cap source.

Therefore the specified maximizing cap K_* is in K^i (its cap area is at least its sofa area |G|>2.2). Note 02 now identifies K_* as a horizontal translate of C(G), and its cap-minus-niche sofa as the same translate of G.

## Scope and review points

This is an extension to EVERY maximizing right-angle cap, not a claim that every such cap satisfies the repository's stronger definition `IsBalancedMaxCap`. The selection and perturbation arguments are deliberately separate from that definition.

The points most worth independent checking are the mesh-local support perturbation at the end cells, the limiting measure argument at normals 0 and pi, and the fact that the scalar Chapter 6 bootstrap consumes exactly (4)-(5). No new numerical result, Lean declaration, or axiom is introduced. Arbitrary moving sofas still require a shape-preserving right-angle reduction and exact set recovery.
