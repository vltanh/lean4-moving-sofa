# A local area bound for every normalized right-angle cap near Gerver

**Status:** written analytic proof, not Lean-checked or independently reviewed. Combined with 05-nonsmooth-certificate.md this removes the Ki hypothesis locally. It does not claim that nearby caps themselves become injective.

Let v=pi/2, phi=phi_G, b0=v-phi, T=pi-phi. Denote Gerver's cap by K0, its niche by N0, and its sofa by G. Use a<b for the endpoints of the niche roof and top edge, x_-<a<b<1 for the two floor endpoints and these top endpoints, and H<1 for the maximum roof height, as in 03-nonconvex-recovery.md.

## Theorem

There is delta0>0 such that every normalized right-angle cap K with d_H(K,K0)<delta0 has

1. N(K) subset K;
2. its canonical triple xi_K=(K,B_K,D_K) in the enlarged domain Tbar;
3. A(K)=|K minus N(K)| <= Q(xi_K) <= M;
4. d_H(K,K0+(s,0)) <= 2sec(phi) sqrt(M-A(K)), where s=-(h_K(pi)-h_K0(pi)).

Atoms in the curvature measure, including vertical edges and atoms at the cut normals, are allowed. Items 3--4 use the extended certificate of the previous note, not the source's theorem restricted to Ki.

## 1. Robust support and corner facts

If compact convex K_n converge to K0 and t_n tends to t, every limit of points p_n in the exposed face e_Kn(t_n) lies in e_K0(t). This follows by taking limits in p_n.u_tn=h_Kn(t_n). Consequently, on a compact normal interval where K0's exposed point is unique and continuous, *all* exposed points of K are uniformly close to those of K0 as d_H(K,K0) tends to zero. The proof is a contradiction/subsequence argument; it does not assert convergence of derivatives at an atom of K0.

Apply this to compact neighborhoods of [phi,b0] and [v+phi,T], which avoid the top normal v. Gerver's f,g are strictly greater than 1 on [phi,b0]. Thus, for all nearby K, both one-sided versions of its arms exceed 1+c there, for a fixed c>0. The corner path x_K is Lipschitz and satisfies almost everywhere

    x_K'=-(f_K-1)u_t+(g_K-1)v_t.

It follows that X_K'=d(x_K)_x/dt <= -c on the core, after reducing c if necessary. The core is therefore a Lipschitz graph with a Lipschitz inverse horizontal coordinate. Its height remains positive and below 1, since this is true for Gerver on the compact core interval.

We also need, for nearby K,

    x_K(t).u_phi < h_K(phi)-1                    (phi<t<=v),
    x_K(t).u_T   < h_K(T)-1                      (0<=t<b0). (1)

For the first inequality on a small interval to the right of phi, the derivative of x_K.u_phi is uniformly negative by the same exposed-point argument. On the remaining compact interval Gerver's inequality has a strictly positive gap, and uniform convergence of x_K and h_K preserves it. The second inequality is the reflected argument at b0. Thus (1) requires regularity of *Gerver at the cuts*, not full injectivity of the competitor.

## 2. Localization of every nearby niche

For every sufficiently small eta>0, a sufficiently small cap neighborhood has

    N(K) subset [a-eta,b+eta] x [0,H+eta].                   (2)

Here and below the floor is included and the other boundary conventions do not affect area.

For 0<t<v a positive-height forbidden wedge has feet

    Z_K(t)=(1-h_K(t+v))/sin(t),
    W_K(t)=(h_K(t)-1)/cos(t),

and its points have x-coordinates between Z_K(t) and W_K(t), and height at most x_K(t)_y. Gerver's feet lie in [a,b], since its niche has exactly that horizontal projection and its inner corner has positive height for 0<t<v. Uniform convergence of h gives the desired foot bounds away from the denominators' endpoint zeros.

Near v, every point supporting a nearby cap at a normal near v has abscissa at most b+eta. Otherwise a subsequential limit would lie beyond the right endpoint of K0's top face. Since all ordinates are at most 1,

    h_K(t)<= (b+eta)cos(t)+sin(t),
    W_K(t)<=b+eta+(sin(t)-1)/cos(t)<=b+eta.

Near 0, use the analogous lower bound a-eta for abscissae supporting K at normals v+t. It gives

    h_K(v+t)<=-(a-eta)sin(t)+cos(t),
    Z_K(t)>=a-eta+(1-cos(t))/sin(t)>=a-eta.

Finally x_K converges uniformly to x_K0. The height of each reference corner is at most H because it lies in the closure of its positive-height wedge. This proves (2).

For completeness, the positive-height assertion outside the exposed core is also a consequence of the stated Gerver formulas, not an extra numerical assumption. On 0<t<=phi, its first phase has

    x_K0(t)_y/sin(t)=2a1 cos(t)-1-(1/2)cos(t)tan(t/2).

Here a1>0 (indeed 2a1-1=g_G(0)-1>0 by the endpoint width fact). The displayed function decreases on [0,phi]: cos(t)tan(t/2)=sin(t)-tan(t/2) has positive derivative there, since cos(t)-1/(1+cos(t))>0 for t<=0.04. Its value at phi is positive by the core-height fact. The last phase is its reflected counterpart, with the same ordinate. This establishes positivity on the entire open interval.

The reference rectangle [a,b] x [0,H] has strictly positive distance from every upper supporting line of K0. To see this, use the trapezoid with vertices (x_-,0),(1,0),(a,1),(b,1) contained in K0, the strict endpoint inequalities, and H<1. By compactness the upper-support gap has a positive minimum. Thus, for small eta and then small d_H(K,K0), the rectangle on the right side of (2) is contained in K. This proves N(K) subset K.

Two consequences will be useful later:

- any fixed floor rectangle I x [0,h] with I a compact interval in (x_-,a), and h sufficiently small, belongs to K minus N(K) for all nearby K;
- for every fixed small eta>0 there are h_eta>0 and t_eta<v such that

      [a+eta,b-eta] x [0,h_eta]
        subset union_{0<t<=t_eta} Q_K^-(t)                 (3)

  for all nearby K. Indeed gamma(x)>0 on (a,b). Cover the compact floor segment by finitely many strictly forbidden reference quadrants, then preserve their strict slacks on a thin rectangle under support perturbations.

## 3. Canonical body contacts

Let B_K=K intersect the half-planes p.u_t>=h_K(t)-1 for phi<=t<=v; define D_K in the reflected way. Both are nonempty convex compact subsets of K: the right floor corner (h_K(0),0) belongs to every defining half-plane for B_K, by h_K(t)<=h_K(0)cos(t)+sin(t); the left corner treats D_K. The wall inequalities hold by definition and the floor equalities follow from these floor corners.

The cut equality for B_K also holds locally. Its cut line b_K(phi) meets K, since its foot W_K lies strictly between the floor endpoints for Gerver and hence for nearby K. Let p be the highest point of K on that line. A supporting normal at p may be chosen as theta_p in [phi,phi+pi]. Put d(t)=h_K(t)-p.u_t. Then d(phi)=1 and d(theta_p)=0.

A normal theta_p>phi+v is impossible: comparing p with any exposed point C of K at phi+v, in the frame (u_phi,v_phi), gives

    h_K(phi)-C.u_phi <= h_K(phi)-p.u_phi=1.

But the exposed-point convergence of Section 1 makes the left side greater than 1, since the corresponding Gerver arm g_G(phi)>1. Therefore phi<theta_p<=phi+v. Sublinearity of the support function, interpolated between phi and theta_p and (when needed) between theta_p and v, yields d(t)<=1 for phi<=t<=v. Thus p belongs to B_K and lies on its cut line. The cut support equality follows. The reflected proof gives D_K's other cut equality.

This proves xi_K in Tbar without assuming Ki.

## 4. Local geometric area bound

The source's three-region argument now applies with the following explicitly verified replacements for injectivity.

**Tail regions.** For phi<t<=v, (1) implies

    H_K^R intersect Q_K^-(t)=H_K^R minus H_K^b(t).           (4)

In fact, in the (u_t,v_t) frame, a point of H_K^R with negative first inner-wall slack cannot have a nonnegative second slack, since u_phi=cos(t-phi)u_t-sin(t-phi)v_t and the corner lies strictly below the cut line. Intersecting with y>=0 gives the wedge version. The reflected identity holds on the left.

The region between B_K's right tail and its endpoint tangents lies in K, in H_K^R, and outside B_K. The first two assertions follow from the triangle whose vertices are the cut foot and the two tail endpoints; all lie in K. A point outside B_K violates one of its wall inequalities, necessarily at t strictly between phi and v. Equation (4) puts it in N(K). The convex-arc area identity therefore gives

    |N(K) intersect H_K^R| >= J(X_B,W_K)-J(right tail),
    |N(K) intersect H_K^L| >= J(Z_K,Y_D)-J(left tail).        (5)

This argument is valid for arbitrary convex B_K,D_K, including polygonal boundaries.

**Core region.** The core's horizontal coordinate is strictly decreasing, its height is positive, and (1) keeps it strictly between the two cut half-planes except at its endpoints. Hence the core, the two cut-line segments to the floor, and the floor segment form a simple graph region. Vertically below the core, points are in its corresponding forbidden quadrant; the two side triangles lie in the cut-end forbidden quadrants. All of this region lies outside H_K^R and H_K^L. Integration of its Lipschitz graph (equivalently, integration by parts for its signed curve area) gives

    |N(K) minus H_K^R minus H_K^L|
      >= J(W_K,x_K(phi))+J(core)+J(x_K(b0),Z_K).             (6)

The a.e. derivative bound from Section 1 is sufficient for this change of variables; C^1 regularity is not used.

The two cut half-planes are disjoint inside K: for nearby K, |K|>2.2 and the elementary strip argument of source Lemma 8.1.4 applies. Since N(K) subset K, its three parts in (5)--(6) are disjoint. Add these estimates, subtract from |K|, and join collinear segment terms at the two cuts. This yields A(K)<=Q(xi_K).

Apply the enlarged-domain certificate (05-nonsmooth-certificate.md, (6)--(8)) to obtain Q(xi_K)<=M and the asserted square-root cap estimate. This completes the theorem.

## Logical boundary

This is a *local* extension of the area bound, not a global assertion that all caps satisfy it. No nearby cap is asserted to have an absolutely continuous curvature measure. The next remaining issue is that a general sofa may stop at omega<v and need not lie in K minus N(K); the terminal-strip loss must pay for the omitted hallway constraints.
