# Quantitative recovery of the nonconvex sofa

**Status:** written analytic proof from the paper's Gerver boundary facts, not Lean-checked or independently reviewed. This extends the cap result, but does not remove the injective-envelope hypothesis from the quantitative theorem. The separate qualitative theorem has no such hypothesis.

Write K0=K_G, G=K0 minus N(K0), M=|G|, v=pi/2. For any normalized right-angle cap K, put U(K)=K minus N(K). The following local geometric statement does not itself require K in Ki.

## Proposition: local Lipschitz continuity of the shape map at Gerver

There are constants C0,delta0>0, depending only on G, such that

    d_H(U(K),G) <= C0 d_H(K,K0)

whenever K is a normalized right-angle cap and d_H(K,K0)<delta0. In particular U(K) is nonempty in this range. No general continuity theorem for arbitrary cap/niche maps is assumed.

### Gerver boundary facts used

Use the notation of the paper's Section 9 and Appendix A.1. Let x_- be the left bottom endpoint, let a=D(0)_x, b=B(v)_x be the top-edge endpoints, and let

    Gamma = D([0,theta]) union x([phi,v-phi]) union B([v-theta,v]).

The cited boundary facts imply the following; we also spell out the consequences needed here.

1. Gamma is the graph of a continuous function gamma on [a,b]. Its three pieces have disjoint successive x-intervals and match at their endpoints. Let H=max gamma<1. The niche is exactly the region 0<=y<gamma(x); outside (a,b) it is empty. Also [a,b] x [0,1] lies in K0.
2. x_-<a<b<1. For the additional strict endpoint inequalities, the cap has no vertical edges: its surface-area measure has no atom at normal 0 or pi, by the injectivity regularity. If a=x_-, the points (a,1) and (x_-,0) would give a vertical edge; similarly if b=1. The weak inequalities follow from cap containment. Thus the inequalities are strict.
3. gamma is Lipschitz, with some finite constant L. On the left tail its slope has absolute value at most tan(theta), since D' is a nonnegative multiple of u_t. On the right tail the same bound follows from B' being a nonpositive multiple of v_t. On the middle piece, x'_x<0 on the compact interval [phi,v-phi], by injectivity and positivity of both sine and cosine. Its absolute value therefore has a positive minimum, while x'_y is bounded. The inverse graph has bounded slope. Gluing the three graphs retains a finite Lipschitz constant.
4. On the left tail, the wall-frame slacks of D(t) are (-(g_G(t)-1),0); on the right tail those of B(t) are (0,-(f_G(t)-1)). There is a uniform number gamma_tail>0 bounding those inactive-slack magnitudes below. In the interiors this follows from f_G,g_G>1. At t=0, g_G(0)=1-a>1, since a<0. At t=v, f_G(v)=b-x_->1. These endpoint strict inequalities are the paper's Lemma `lem:gerver-width`. Continuity supplies the uniform bound on the two compact tail intervals.

These statements use only the already established Gerver geometry, not a new numerical reconstruction.

### 1. An outer-boundary margin

The convex hull of (x_-,0),(1,0),(a,1),(b,1) lies in K0. By the strict inequalities above and H<1, the rectangle

    R=[a,b] x [0,H]

lies strictly inside all of its upper supporting half-planes. It may meet the floor, which is not one of these upper half-planes. Compactness gives

    gamma_outer = min_{q in R, 0<=t<=pi} [h_K0(t)-q.u_t] > 0.   (1)

One way to see strictness directly: at height y<1 the left side of that trapezoid is strictly left of a, and the right side strictly right of b. At the floor only the downward normal can have zero gap, and it is not in [0,pi].

Put delta=d_H(K,K0), so all support differences have magnitude at most delta. Let p be in U(K). If p is outside K0, choose a nearest q in K0, with |p-q|<=delta. If q belonged to N(K0), it would lie in R. For delta<gamma_outer, (1) would imply p.u_t<h_K0(t) for every upper normal t. Since p_y>=0, the cap half-plane representation would then put p in K0, a contradiction. Hence q is in G, and

    dist(p,G)<=delta whenever p is outside K0.                  (2)

### 2. Points inside the reference niche cannot protrude far

Suppose now p is in K0 minus G. Let q=(p_x,gamma(p_x)) be the roof point above it and d=q_y-p_y>0. The point q belongs to one of the three displayed boundary pieces.

On a middle piece q=x(t), t in [phi,v-phi], both reference inner-wall slacks of q are zero. Moving downward by d makes them -d sin(t) and -d cos(t). Both coefficients are at least c=sin(phi)>0.

On a left tail, one slack at q is at most -gamma_tail and the other is zero. The coefficient of d in the latter is cos(t)>=cos(theta)>c. On a right tail the same assertion holds with sin(t)>=cos(theta)>c.

Consequently, if delta<gamma_tail and d>delta/c, both reference slacks of p are strictly less than -delta. Changing the cap support by at most delta leaves both slacks for K strictly negative. This puts p in N(K), contradicting p in U(K). Therefore

    dist(p,G)<=d<=delta/c.                                     (3)

Together (2)-(3) show sup_{p in U(K)}dist(p,G)<=delta/c for delta below both geometric margins.

### 3. A reference erosion lies in U(K)

For r>0 write G_{-r}={p in G:dist(p,G complement)>=r}. Then

    G_{-sqrt(2)delta} subset U(K).                             (4)

For delta=0 this is read directly as U(K0)=G; for delta>0, take p in the left side. The open ball of radius r=sqrt(2)delta about p lies in G. Every reference outer-wall gap is therefore at least r, and p_y>=r, so the support perturbation leaves p in K. The entire open forbidden quadrant Q^-_K0(t) is disjoint from G. In its orthonormal wall frame the distance to that quadrant is

    sqrt(max(a,0)^2+max(b,0)^2).

It is at least r. Thus max(a,b)>=r/sqrt(2)=delta. The corresponding perturbed maximum is at least zero, so p is outside every forbidden quadrant of K. This proves (4), including the angles 0 and v if they are included.

### 4. A uniform interior-ball property for G

There exist kappa,r0>0 such that, for every p in G and 0<rho<=r0, some closed ball of radius kappa*rho lies in G intersect the closed ball of radius rho about p. Here is a direct proof, avoiding an unverified assertion that an arbitrary piecewise smooth boundary has no cusps.

Decompose G into the two convex wings

    K0 intersect {x<=a},   K0 intersect {x>=b},

and the middle epigraph strip E={a<=x<=b, gamma(x)<=y<=1}. Both wings have nonempty interiors, since they contain the triangles with vertices (x_-,0),(a,0),(a,1) and (b,0),(1,0),(b,1), respectively.

For a compact convex body C containing a ball of radius r_C centered at c, let D_C be its diameter. From any p in C, the homothetic ball with ratio lambda=rho/(D_C+r_C) has radius r_C*rho/(D_C+r_C), lies in C, and lies in the rho-ball about p. Restrict rho so lambda<=1. This treats both wings and the rectangle [a,b] x [H,1].

It remains to treat p=(x,y) in E with y<=(1+H)/2. Choose the horizontal direction sigma toward the farther endpoint of [a,b], and set

    w=rho/[4(L+2)],
    z=(x+2 sigma w, y+(3L+2)w).

For rho<=min(b-a,(1-H)/2), the ball of radius w about z lies in E. Indeed its x-coordinates are within 3w of x and stay in [a,b]; its lowest ordinate is y+(3L+1)w>=gamma(x)+3Lw, hence above gamma throughout the ball. Its highest ordinate is below 1. Finally |z-p|+w<=(3L+5)w<=rho. Taking the minimum of the finitely many constants proves the interior-ball property.

With r=sqrt(2)delta and rho=2r/kappa<=r0, this property supplies, near every p in G, a ball of radius 2r in G. Its center belongs to G_{-r}, hence to U(K) by (4), and lies within rho of p. Thus

    sup_{p in G}dist(p,U(K)) <= 2sqrt(2)delta/kappa.

The proposition follows with

    C0=max(csc(phi),2sqrt(2)/kappa)

and delta0 chosen below gamma_outer, gamma_tail, and kappa*r0/(2sqrt(2)). This is a local Lipschitz statement for the nonconvex shape map at G, not at all caps.

## Theorem: square-root stability with an injective right-angle envelope

There are C,epsilon0>0 depending only on G with the following property. Suppose a rigid image of a moving sofa S is contained in a monotone sofa U with rotation angle pi/2, whose cap K belongs to Ki. If epsilon=M-|S| is in [0,epsilon0), then

    d_rig(S,G) <= C sqrt(epsilon).

In particular the result applies to monotone right-angle sofas whose own cap belongs to Ki. It does not assert that every near-optimal moving sofa has such an envelope.

### Proof

Work in the frame where S subset U, and horizontally align K using the pinned translation from the cap theorem. Monotonicity of area, the cap/sofa identity, and optimality give

    |S|<=|U|=A(K)<=M,
    |U minus S|<=epsilon,
    delta=d_H(K,K0)<=2sec(phi) sqrt(M-A(K))
                         <=2sec(phi) sqrt(epsilon).          (5)

For epsilon0 small enough, all geometric margins above hold. Equations (2)-(3) bound the distance from S to G by delta/c.

For the other directed distance, put r=sqrt(2)delta. For p in G let d=dist(p,S) and rho=min(d/2,r0). If d<=4r/kappa there is already the desired O(sqrt(epsilon)) bound. Otherwise, and provided rho>=2r/kappa, the interior-ball property supplies a ball of radius kappa*rho in G intersect B(p,rho). Its concentric ball of radius kappa*rho/2 lies in G_{-r}, hence in U. It is disjoint from S because rho<d. Thus

    epsilon >= |U minus S| >= pi*kappa^2*rho^2/4.             (6)

Choose epsilon0 also below pi*kappa^2*r0^2/4 and require r<=kappa*r0/2. Then d>=2r0 is impossible by (6). Consequently rho=d/2; the case d>4r/kappa ensures rho>2r/kappa. Equation (6) now gives d<=4sqrt(epsilon)/(kappa sqrt(pi)).

Combining this with (5), one possible constant is

    C=max(2sec(phi)csc(phi),
          8sqrt(2)sec(phi)/kappa,
          4/(kappa sqrt(pi))).

If epsilon=0 the same interior-ball argument, or the paper's exact recovery lemma, gives equality. All arguments are area and distance estimates; no regularity of the smaller S is assumed beyond its being a closed moving sofa.

## Remaining gap for the fully quantitative moving-sofa theorem

The unrestricted qualitative theorem is proved in `02-global-qualitative.md`. The argument above still requires a right-angle monotone envelope with cap in Ki. Near-maximality alone has not been shown here to yield that hypothesis or an approximate substitute with controlled error. Therefore an unrestricted C sqrt(M-|S|) theorem is not claimed.
