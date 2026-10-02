# 14. A right-angle motion of the specified maximizing sofa

Date: 2026-10-02. Paper proof. This closes the fixed-angle extension proposed in note 06. Constants depend on the fixed omega<pi/2; no uniform limit in omega is taken.

## Theorem

Put L=pi/2. Every global maximizer K_* of A_omega among standard caps, for 0<omega<L, satisfies

    w_{K_*}^circ<=sigma_{K_*}({L}),
    z_{K_*}^circ<=sigma_{K_*}({omega}).                         (1)

Consequently, if omega>=arcsec(2.2), A_omega(K_*)>=2.2, and M=K_* minus N_omega(K_*) is a monotone sofa, a rotated copy of that SAME M admits a right-angle motion.

## 1. Selected polygons and floating defects

Note 12 supplies K_n->K_* maximizing A_n-lambda_n P, with lambda_n->0, in the compact family of standard omega-caps. Put

    d_n(t)=sigma_{K_n}({t})-tau_{K_n}(t).

For every floating upper normal, note 10 proves

    d_n(t)<=C lambda_n delta_n.                                 (2)

This is valid even for zero-length facets, since then d_n(t)=-tau_n(t)<=0. The normal interval (omega,L) adds no floating hats; its two endpoint heights are fixed.

## 2. Feasibility of a pinned-strip variation

Here are details for t=L; the case t=omega is obtained by reflecting the cap, which swaps its two strips. Assume the top facet at L has positive length.

In its finite defining half-plane intersection, replace

    y<=1, y>=0

by

    y<=1+epsilon, y>=epsilon,

and leave all other ASSIGNED heights fixed. Denote the intersection by K^epsilon.

For sufficiently small positive epsilon its actual top height is 1+epsilon. Choose a point in the relative interior of the positive top facet away from the finitely many intersections with other defining lines. All other inequalities are strict there. Moving it up by epsilon gives a witness for the new top height.

Its actual bottom height is epsilon. The origin satisfies every upper defining inequality strictly: all upper heights are at least o.u_s>0, where o=(c,1), c=sec omega-tan omega. Thus the original bottom contains a point (x,0), x>0 small, with all other inequalities strict. The point (x,epsilon) is a witness for the new bottom.

The other strip still has both supports attained. Its top contact o remains in K^epsilon for epsilon<1. For its bottom, take a sufficiently short nonzero point r v_omega in the original cap. Such points exist because all upper constraints have strict slack at O, and they lie on p.u_omega=0 with positive height. Fix one first, then take epsilon smaller than its height. It remains in K^epsilon.

Thus K^epsilon has width exactly one in both pinned directions. Translating it by

    v_epsilon=(epsilon tan omega,-epsilon)

puts it back in standard position. It is a polygon cap with the same allowed normals. This proves the needed feasibility without assuming that all the other assigned heights are actual supports. The permitted epsilon may depend on K_n and n.

## 3. Assigned versus actual supports: the direction of comparison

Write h^epsilon for the assigned data before normalization. Both pinned upper supports of K^epsilon equal their assigned values by section 2, so the fan defined by those strip data is the ACTUAL fan. At every floating normal, its actual support is no larger than the assigned height.

Consequently the niche formed from actual supports is contained in the niche formed from assigned heights. The cap intersection is unchanged: replacing assigned heights by actual supports does not change a convex polygon defined by those normals. Therefore

    A_n(actual K^epsilon)>=A_n(assigned h^epsilon).               (3)

Translation of a cap and its fan/niche does not change this area difference. Thus the normalized cap is a valid competitor with an objective at least the assigned-height objective. The inequality in (3) is essential: the opposite inequality would not suffice.

## 4. A uniform O(epsilon) penalty bound at a pinned strip

All standard omega-caps contain the fixed ball B(q,rho) of note 12. Let K be defined by unit-normal inequalities p.u_i<=h_i and contain this ball. Suppose K' is the intersection with assigned heights h_i' satisfying |h_i'-h_i|<=a epsilon. Put eta=a epsilon/rho<1. Direct substitution into every inequality gives

    (1-eta)K+eta q subset K' subset (1+eta)K-eta q.               (4)

For the right inclusion, if x' is in K', then (x'+eta q)/(1+eta) satisfies the old inequalities because h_i-q.u_i>=rho. For the left inclusion, use the same margin and h_i'>=h_i-a epsilon.

The normalized pinned perturbation changes each assigned height by at most (1+sec omega)epsilon. The bounded parallelogram and (4) therefore give

    d_H(K_n,normalized K_n^epsilon)<=C_omega epsilon.

Since the support differences in P are uniformly bounded and its integration interval is fixed,

    |P(normalized K_n^epsilon)-P(K_n)|<=C_omega epsilon.          (5)

These constants are independent of n. The common interior ball is indispensable to this argument; note 09 records why bounded diameter alone does not imply (4) with a uniform constant.

## 5. Pinned first variations

The cap area derivative for t=L is sigma_n(L)-sigma_n(3L): the top moves outward and the floor moves inward. The union of sampled inner quadrants does not change, because L is not a floating sample. Only the fan floor moves. Its niche area derivative is

    -length(N_n intersect {y=0})=tau_n(L)-sigma_n(3L).

The boundary-length equality here is the general polygon identity of Lemma 3.4.5, valid without niche containment. Subtracting gives

    A_n(h^epsilon)-A_n(h)=epsilon d_n(L)+O_n(epsilon^2).

The same calculation applies to the other pinned strip. It agrees with the corrected sign in the repository's Lemma 3.4.7; the printed niche sign in the original paper must not be used uncorrected.

Combine penalized maximality, (3), and (5). Divide by epsilon and take epsilon down to zero at FIXED n. This yields

    d_n(L)<=C_omega lambda_n,
    d_n(omega)<=C_omega lambda_n.                              (6)

If the relevant top facet has zero length, the bound is automatic. No uniform control of the quadratic remainder is needed, since the epsilon limit precedes the mesh limit.

## 6. Turn the one-sided bounds into two-sided pinned bounds

The upper cap boundary and the completed inner polyline have the same two endpoints. Traversing both from right to left gives

    sum_t d_n(t) v_t=0,
    sum_t d_n(t) sin t=0.                                     (7)

This endpoint identity holds for every polygon cap; the niche need not lie inside it. All upper normals are in (0,L+omega), hence have positive sine.

From (2) and (6),

    E_n:=sum_t (d_n(t))_+ sin t <= C_omega lambda_n,             (8)

because there are O(1/delta_n) floating normals and only two pinned ones. Equation (7) shows that the same bound holds for the sum of the weighted negative parts. In particular, for k=omega,L,

    -d_n(k)<=E_n/sin k<=C_omega' lambda_n.

Thus

    tau_n(k)<=sigma_n(k)+C_omega' lambda_n.                    (9)

There is no division by the small sine of an extreme mesh angle. Only the two FIXED pinned sines are divided out.

## 7. Pass the horizontal-gap inequalities to K_*

For an arbitrary polygon cap,

    w_K^circ<=tau_K(L),   z_K^circ<=tau_K(omega).                (10)

For the first inequality, the bottom segment from the largest wedge right intercept to the right cap endpoint is outside every wedge. Intersect it with the original bottom edge. Its length is at least w_K^circ: each sampled wedge gap has that lower bound, and the whole bottom edge has it too because W_K(t)->O as t increases to omega. This remaining segment belongs to the completed inner polyline in direction L. The second assertion follows by reflection. This is precisely the geometric part of Theorem 4.1.2 before balancedness is invoked.

The infimum gaps are Lipschitz in Hausdorff distance with constant 1+sec omega, by their support formulas. Hence w_{K_n}^circ->w_{K_*}^circ, and likewise for z. Weak convergence of curvature measures gives, at each fixed k,

    limsup_n sigma_{K_n}({k})<=sigma_{K_*}({k}).

Combine (9)–(10) and lambda_n->0 to obtain (1). This establishes (1) for the SPECIFIED maximizer, not just for a selected balanced limit.

## 8. A direct width argument retaining the same sofa

Assume now omega>=arcsec(2.2), A(K_*)>=2.2, and M=K_* minus N(K_*) is a monotone sofa. Write K=K_*, c=sec omega-tan omega, o=(c,1). We use the established scalar/area estimates of Baek Lemmas 4.2.2 and 4.2.4, with their intended ranges as corrected in the repository:

- For d_min=1.25 when omega<arctan(2.2), and 1.1 otherwise, the portion of P_omega with both outer extents at most c+d_min has area less than 2.2.
- If d_min<=d<=tan omega, r_y=1-d cot omega and g=sqrt(1-r_y^2), then d sin omega>1 and g>2 cos omega.

These are pre-existing scalar estimates, not an extension of a balancedness theorem.

Since |K|>=A(K)>=2.2, at least one outer extent exceeds c+d_min. Reflecting if necessary, take h_K(0)=c+d with d>=d_min. The bottom endpoint q_0=(c+d,0) belongs to K; P_omega gives d<=tan omega. The supporting lines at 0,omega meet at r=(c+d,r_y), and 0<=r_y<=1.

Set g=sqrt(1-r_y^2) and s=q_0-g u_0. Then |r-s|=1. For every 0<t<omega, the two supporting constraints imply h_K(t)<=r.u_t. Therefore

    h_K(t)-1<=r.u_t-1<=s.u_t,

so every right wedge gap is at least g. By (1), the horizontal top edge has length at least g. Its right endpoint is o, so q_1=o-g u_0 also belongs to K.

Let a=L-omega, which lies in (0,omega). The two scalar inequalities above give

    (q_0-c u_0).u_a=d sin omega>1,
    (q_1-c v_omega).v_a=-cos(2omega)+g cos omega>1.

Among O,c u_0,c v_omega, the first scalar product with u_a is largest at c u_0; the scalar product with v_a is largest at c v_omega. Since q_0,q_1 are in K, all THREE points satisfy both strict inequalities defining Q_K^-(a). Thus the triangle

    Delta=conv{O,c u_0,c v_omega}

is contained in that open inner quadrant and in the fan, hence in N(K).

It follows that M is contained in the closed polygon obtained by cutting Delta off the origin corner of P_omega. For any t in [omega,L], its upper support is o.u_t and its lower support is attained at one of c u_0,c v_omega. Its width in direction u_t is therefore

    max((o-c u_0).u_t,(o-c v_omega).u_t)
      =max(sin t,cos(t-omega))<=1.                            (11)

This is a width bound for M itself. No new maximizing shape has been substituted for it.

## 9. Construct the additional motion

Put beta=L-omega. For 0<=alpha<=beta, the vertical width of R_alpha M is the width of M in normal direction L-alpha, hence at most one by (11). Translating it vertically by minus its lowest height, and sufficiently far left, puts it in the horizontal side of the hallway. The required translations vary continuously with alpha because support functions do.

Start with R_beta M and rotate clockwise through beta to a horizontal-strip copy of M. Translate inside the horizontal side to the starting placement of M's original motion; interpolation between two allowed translations stays inside that convex side. Then follow M's original omega-angle motion. The total clockwise rotation is beta+omega=L.

This constructs a right-angle motion of a rotated copy of the SAME M. Every subset of M remains a subset throughout these isometries. QED.

## Noncircularity and source audit

Selection comes from note 12; floating variations from note 10; pinned feasibility, penalty control, and error cancellation are proved above. The old inputs are the general Nef-polygon first variation and endpoint identities (Chapter 3), weak curvature convergence, and the scalar estimates of §4.2. The proof never invokes Theorem 4.1.4 or 4.2.5 with a missing balancedness hypothesis.

The old repository locations are `MovingSofa/Balanced/MaximumPolygonCap.lean`, `MovingSofa/Angle/HorizontalSide.lean`, and `MovingSofa/Angle/RightAngle.lean`. The construction of the extra motion is written explicitly here rather than inferred from equality of areas.
