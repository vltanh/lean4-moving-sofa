# 13. Every maximizing right-angle cap satisfies injectivity

Date: 2026-10-02. Paper proof. This replaces the proposed extension in note 05 with a proof using notes 10–12. Balancedness of the chosen cap, or of its approximating polygons, is not assumed.

## Theorem

Let K_* be any standard right-angle cap globally maximizing

    A(K)=|K|-|N(K)|.

Then its inner-corner curve is continuously differentiable on [0,pi/2], its curvature measures are absolutely continuous on the two upper quadrants away from the top normal, and its arm functions satisfy

    f(t)>=1+t/2,   g(t)>=1+(pi/2-t)/2.

In particular K_* satisfies the injectivity condition. Since the already proved maximal cap value is |G|>2.2, it lies in K^i. Consequently note 02 identifies K_* as a horizontal translate of the cap of G.

## 1. Select the specified cap

Set L=pi/2. Use note 12 with a box whose horizontal bounds strictly contain K_*. It supplies polygon caps K_n converging to K_* and maximizing A_n-lambda_n P, where lambda_n->0. For sufficiently large n the box constraint is inactive. All K_n have diameter at most a fixed D.

Write delta=delta_n, sigma(t)=sigma_{K_n}({t}), and tau(t) for the lengths in the completed inner polyline. Note 10 gives, at every floating normal t,

    sigma(t)<=tau(t)+C lambda_n delta.                           (1)

This holds also when sigma(t)=0. C is independent of n,t. The step size is at most pi/4 after discarding finitely many terms.

## 2. An exact geometric inequality BEFORE imposing maximality

Fix t in Theta_n and abbreviate

    s=sigma(t),  q=tan(delta/2),  T=tan(delta),
    a=|g^+(t)-1|.

We prove

    tau(t)<=T(a+q)+(2q-s)_+.                                    (2)

This is a statement about arbitrary bounded polygon caps, not maximum polygons.

Let X be the part of the niche boundary on the inner half-ray b_vec(t). Its length is tau(t), by the general boundary decomposition in Lemma 3.4.5. Set

    R=H^d(t-delta) union H^d(t) union H^d(t+delta).

The intersections of the half-ray with the first and third half-planes are segments ending at the corner x_K(t), with lengths

    T(g^-(t)-1+q)_+,   T(1-g^+(t)+q)_+.

These follow by solving the two line intersections, or by Lemma 6.3.2's geometric computation; no maximality enters. Their union has length equal to the larger length. Since g^-<=g^+,

    length(X intersect R)<=T(a+q).                              (3)

Except for its single possible intersection with y=0, a point of X is above the floor and outside each of the three open inner quadrants. If it is also outside R, it must therefore lie in all three H^b(t-delta),H^b(t),H^b(t+delta). On b(t), this intersection is a segment of length

    (2 tan(delta/2)-s)_+.

To check the coefficient, the original consecutive supporting intersections bound the outer facet with length s. Moving the two adjacent supporting lines inward by unit distance shifts their intersections with b(t) toward each other by the two cotangent/intersection contributions, leaving signed length 2 tan(delta/2)-s. Solving their scalar line equations gives the same expression. Thus

    length(X minus R)<=(2q-s)_+.                                (4)

Equations (3)–(4) prove (2).

### End cells are included

At t=delta or L-delta one of t-delta,t+delta is 0 or L. Its open inner quadrant has empty intersection with y>=0, because h(L)=1. It can therefore be added to the exclusion argument above even though it is not sampled.

The supporting lines at virtual normals 0 and pi meet the first/last sampled facet at its actual bottom endpoint. For example the right endpoint is (h(delta)/cos(delta),0), and h(0)=h(delta)/cos(delta). Thus the consecutive-intersection formulas used above remain exact in the end cells. An endpoint atom is not discarded in the limiting argument.

## 3. The error budget

Combining (1) and (2), with e=C lambda_n delta and B=T(a+q), gives

    s<=B+(2q-s)_++e.

If s>=2q, then s<=B+e. Otherwise 2s<=B+2q+e. Therefore

    s<=max(B,(B+2q)/2)+e.

The arm bound 0<=g^+<=D gives a<=D+1. Elementary estimates on 0<=delta<=pi/4 give

    tan(delta)<=2delta,
    0<=tan(delta)-delta<=4delta^3/3,
    0<=2tan(delta/2)-delta<=delta^3/3.

It follows, with a constant C_D independent of n,t, that

    sigma(t)<=delta k(g^+(t))+C_D delta^2+C lambda_n delta,        (5)
    k(x)=max(|x-1|,(|x-1|+1)/2).

Reflection gives the counterpart on the second upper quadrant. There are O(1/delta) facets, so the total error in (5) is O(delta+lambda_n), tending to zero.

## 4. Weak convergence without losing normal 0

Let mu_n be the sum of the first-quadrant floating atoms sigma(j delta) at j delta, 1<=j<2^n. Spread each atom uniformly over [(j-1)delta,j delta), obtaining the measure bar_mu_n. For every continuous test function eta on a fixed compact interval,

    |integral eta dmu_n-integral eta dbar_mu_n|
      <= modulus_eta(delta) mu_n(R).

The masses are uniformly bounded, either by (5) or the perimeter bound from the box. Thus this difference tends to zero.

On each such cell (5) bounds the density of bar_mu_n by

    k(g^+_{K_n}(j delta))+C_D delta+C lambda_n.                   (6)

Extend it by zero on the final cell next to L. For almost every s in (0,L), the support face of K_* at s+L is a singleton. This uses only the elementary fact that a planar compact convex body has at most countably many positive-length faces, not any conclusion about curvature absolute continuity. For mesh normals s_n->s, the chosen support points of K_n at s_n+L converge to that singleton: each cluster point is in its support face by uniform support convergence. Hence the step functions in (6) converge almost everywhere to k(g_{K_*}(s)). They are uniformly bounded by the diameter bound, so dominated convergence applies.

Now regard surface measures on the circle and take nonnegative continuous test functions supported in an arc (-epsilon,L), where 0<epsilon<pi/4. The polygon surface measure on this arc consists precisely of mu_n; in particular there is no facet at 0 or just below it. Weak convergence of the full surface measures, the preceding spreading estimate, and (6) yield

    sigma_{K_*}|[0,L) <= k(g(t)) dt.                            (7)

The test functions may be NONZERO AT 0. Thus (7) includes sigma_{K_*}({0})=0; it is stronger than a test restricted to compact subsets of (0,L). Reflecting the argument proves

    sigma_{K_*}|(L,pi] <= k(f(t-L)) dt,                         (8)

including no atom at pi. No bound or vanishing is asserted for the top atom at L.

## 5. Regularity, arm identities, and the analytic bootstrap

The two bounds give bounded curvature densities r(t),s(t) on the two upper quadrants. For interior parameters define

    f(t)=h(t+L)-h'(t),   g(t)=h(t)+h'(t+L).

Use the right derivative of h at 0,L and the left derivative at L,pi as appropriate to the two separate restrictions. In particular f uses h'_-(L) at its right endpoint, while g uses h'_+(L) at its left endpoint. A horizontal top edge is allowed; no equality of these two derivatives is assumed.

The general support/Stieltjes identities give

    df=(g-r)dt,    dg=(s-f)dt.

Thus f,g have absolutely continuous representatives on [0,L]. They are nonnegative: they are projections of the difference between the two supporting contact points of K_* onto the corresponding unit vectors. The absence of atoms at 0 and pi makes the extreme support points bottom endpoints. Therefore

    f(0)=1,   g(L)=1.

Since r<=k(g) and s<=k(f), integration gives

    f(t)>=1+integral_0^t m(g(u))du,
    g(t)>=1+integral_t^L m(f(u))du,   m(x)=x-k(x).                (9)

Note 11 now proves f(t)>=1+t/2 and g(t)>=1+(L-t)/2. This replaces the finite bootstrap in the earlier note 05.

On each of the restrictions [0,L] and [L,pi], the support function has a continuous one-sided endpoint derivative: h''+h has a bounded density there away from the permitted top atom. The inner corner

    x_K(t)=(h(t)-1)u_t+(h(t+L)-1)v_t

is therefore C^1 on [0,L], with

    x_K'(t)=(1-f(t))u_t+(g(t)-1)v_t.

Both required component signs are strict on (0,L). The curvature densities give InjCond1, the C^1 statement gives InjCond2, and the signs give InjCond3. Also |K_*|>=A(K_*)=|G|>2.2, so K_* belongs to K^i.

Finally the already proved bounds A(K)<=Q(K,B_K,D_K)<=Q(G's triple)=|G| are equalities at K_*. Note 02's cap-rigidity theorem applies and gives

    K_*=C(G)+(a,0).

Horizontal translation commutes with the niche construction, so K_* minus N(K_*) is G+(a,0). QED.

## Source and dependency audit

The old ingredients are general polygon boundary/variation geometry (Baek Lemmas 3.4.5 and 3.4.7), support-vertex geometry (§6.3), weak convergence of surface measures, and the general arm Stieltjes identities (§6.2). Their repository locations are `Balanced/MaximumPolygonCap.lean`, `Injectivity/DiscreteIneq.lean`, `Angle/HorizontalSide.lean`, and `Injectivity/ArmLengths.lean`.

The only use of maximality in the new sequence is the penalized first variation (1). Neither exact balancedness nor polygon niche containment is used in (2)–(9). The original maximum-polygon diameter theorem is not used: the selected compact box supplies D. The scalar result is proved in note 11 rather than imported from a numerical calculation.
