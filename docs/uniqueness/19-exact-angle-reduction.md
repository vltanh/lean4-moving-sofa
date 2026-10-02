# 19. Exact angular estimates and an explicit shape-preserving motion

Date: 2026-10-02. Pen-and-paper proof. This replaces the two scalar estimates imported in note 14 by elementary rational/polynomial proofs. It also makes the final motion and the reflection step explicit.

## Theorem

Put L=pi/2. Suppose

    arcsec(11/5) <= omega < L,

and K is a standard omega-cap with |K|>=11/5. Suppose its two pinned edge lengths satisfy

    sigma_K({L}) >= w_K^circ,
    sigma_K({omega}) >= z_K^circ.                              (1)

If M=K minus N_omega(K) is a monotone sofa, a rotated copy of the SAME M admits a motion with total clockwise rotation L. The argument preserves every subset of M throughout. It does not replace K by another maximizing cap.

For the uniqueness application, (1) is the conclusion of the specified-maximizer argument in note 14, sections 1-7. The present proof does not assume balancedness and does not use the scalar estimates in the original Chapter 4.

## 1. Coordinates and the two extent thresholds

Write

    C=cos(omega), S=sin(omega), T=tan(omega),
    c=sec(omega)-tan(omega)=1/(sec(omega)+tan(omega)),
    o=(c,1).

Every standard cap lies in P_omega={0<=p_y<=1, 0<=p.u_omega<=1}, contains o and O, and has upper-right top endpoint o. The membership of o and the common triangle were proved directly in note 15, section 1.

Let

    d_0=5/4     if T<11/5,
    d_0=11/10   if T>=11/5.

The initial angle bound implies

    sec(omega)>=11/5,
    T>=4 sqrt(6)/5>19/10.

In particular 0<d_0<T. Also sec(omega)+T>4, so c<1/4.

We first prove that at least one of the two extents h_K(0), h_K(L+omega) exceeds c+d_0.

If both were at most c+d_0, then K would lie in

    R={p in P_omega: p_x<=c+d_0, p.v_omega<=c+d_0}.

Each cutoff removes a corner triangle with base T-d_0 and height (T-d_0)/T. The triangles are disjoint. Indeed p_x>c+d_0 and p.v_omega>c+d_0 would imply

    C p_y > (1+S)(c+d_0) > (1+S)c = C,

contrary to p_y<=1. Since |P_omega|=sec(omega),

    |R|=sec(omega)-(T-d_0)^2/T
        =c+2d_0-d_0^2/T.                                     (2)

When T<11/5 and d_0=5/4,

    |R| < 1/4+5/2-125/176 = 359/176 < 11/5.

When T>=11/5 and d_0=11/10, use c<1/T to get

    |R|=11/5+c-121/(100T)<11/5.

Both contradict |K|>=11/5. This proves the extent assertion without numerical approximation.

Reflecting when necessary, suppose h_K(0)=c+d with d>d_0. The reflection will be transferred back to the original set in section 6. The parallelogram bound h_K(0)<=sec(omega) gives d<=T.

## 2. Two strict inequalities, certified by positive coefficients

Put

    r_y=1-d/T,   g=sqrt(1-r_y^2).

Because d_0<=d<=T, we have 0<=r_y<1 and g^2 increases as d increases. It suffices to prove

    d_0 S>1,
    1-(1-d_0/T)^2>4/(1+T^2).                                 (3)

### The first inequality

For d_0=5/4, S^2>=96/121 gives

    (d_0 S)^2 >= 150/121 > 1.

For d_0=11/10, T>=11/5 gives S^2>=121/146 and

    (d_0 S)^2 >= 14641/14600 > 1.

All quantities are positive, so d S>=d_0 S>1.

### The second inequality when d_0=5/4

Multiply by the positive number 16T^2(1+T^2). The assertion becomes

    p(T)=40T^3-89T^2+40T-25>0.

Set z=T-19/10>=0. Direct expansion is

    p(T)=40z^3+139z^2+135z+407/100>0.                          (4)

### The second inequality when d_0=11/10

Multiplication by 100T^2(1+T^2) gives

    q(T)=220T^3-521T^2+220T-121>0.

With z=T-11/5>=0, the exact expansion is

    q(T)=220z^3+931z^2+1122z+4598/25>0.                        (5)

Thus (3) holds in both cases. Taking nonnegative square roots proves the required inequalities

    d sin(omega)>1,    g>2 cos(omega).                         (6)

These are rational certificates with nonnegative variables; there is no unproved trigonometric convexity assertion or approximate endpoint calculation. Note 18 records why using d_0=11/10 in both cases would fail.

## 3. Force a sufficiently long top edge

The rightmost bottom point q_0=(c+d,0) belongs to K. To see this, take a rightmost point of K and project it vertically to height zero: all allowed upper scalar products decrease, and both lower fan inequalities still hold. Let

    r=(c+d,r_y),    s=(c+d-g,0).

The point r is the intersection of the support lines with normals 0 and omega, and |r-s|=1. For 0<=t<=omega, write u_t as a nonnegative sine combination of u_0 and u_omega. The support inequalities give h_K(t)<=r.u_t. Therefore

    h_K(t)-1 <= r.u_t-1 <= s.u_t.

The last inequality follows from (r-s).u_t<=|r-s|=1. Dividing by cos(t)>0, for 0<t<omega, shows that the right intercept W_K(t) has abscissa at most s_x. Hence

    w_K(t)>=g,   w_K^circ>=g.

By (1) the horizontal top edge has length at least g. Its right endpoint is o, so

    q_1=o-g u_0=(c-g,1)

belongs to K.

## 4. Put a fixed triangle inside one open inner quadrant

Let a=L-omega. Since T>19/10>1, we have omega>pi/4, and hence 0<a<omega. Consider

    Delta=conv{O,c u_0,c v_omega}.

The largest u_a scalar product of its three vertices occurs at c u_0: its value is c sin(omega)>0, whereas the value at c v_omega is c cos(2omega)<0. The largest v_a scalar product occurs at c v_omega: its value is c sin(2omega)>0, whereas the value at c u_0 is -c cos(omega)<0.

The witnesses from section 3 satisfy

    (q_0-c u_0).u_a = d sin(omega)>1,
    (q_1-c v_omega).v_a = -cos(2omega)+g cos(omega)>1.

The second strict inequality follows from g>2 cos(omega) and -cos(2omega)=1-2cos(omega)^2. Since q_0,q_1 belong to K, every vertex, and therefore every point of Delta, satisfies

    p.u_a < h_K(a)-1,
    p.v_a < h_K(a+L)-1.

Thus Delta is contained in the OPEN inner quadrant Q_K^-(a). It is also in the fan, so

    Delta subset N_omega(K).                                 (7)

The inequalities are strict even at the three vertices; replacing an open quadrant by its closure has not been used.

## 5. Width of the remaining polygon

Every point of the fan has unique coordinates p=A u_0+B v_omega with A,B>=0. In these coordinates P_omega is 0<=A,B<=sec(omega), its far corner is o, and Delta is A+B<=c. Thus M lies in the closed cut polygon

    P_omega intersect {A+B>=c}.

For omega<=t<=L, the coefficients of p.u_t in A,B are cos(t)>=0 and sin(t-omega)>=0. Its maximum is attained at o; its minimum over the cut polygon is attained at c u_0 or c v_omega. Its width is consequently

    max((o-c u_0).u_t,(o-c v_omega).u_t)
      =max(sin(t),cos(t-omega))<=1,                            (8)

using o-c u_0=(0,1) and o-c v_omega=u_omega. Hence M itself has width at most one in every normal direction of [omega,L].

## 6. Transfer the reflection back before constructing the motion

The reflection in the line with angle (L+omega)/2 exchanges u_0 and v_omega, preserves P_omega and Delta, and sends the inner quadrant at t to the inner quadrant at omega-t with its two inequalities exchanged. It also swaps the two inequalities (1).

Therefore when the left extent, rather than the right one, is large, apply sections 2-4 to the reflected cap and reflect (7) back. The result is still Delta subset N_omega(K) for the ORIGINAL cap. Equivalently, reflection preserves the normal interval [omega,L] and transfers (8) back. No reflection of the actual sofa is needed in the subsequent motion.

## 7. Continuous motion of the same set

Put beta=L-omega. For 0<=alpha<=beta, the vertical width of R_alpha M equals the width of M in normal direction L-alpha and is at most one by (8). Choose a constant B with |p|<=B for p in M and define

    b(alpha)=(1-B, h_M(L-alpha+pi)).

Then R_alpha M+b(alpha) lies in the horizontal side: its minimum height is zero, its maximum height is its vertical width, and its first coordinate is at most one. The function b is continuous because M is compact and its support function is continuous.

The starting shape is R_beta M. First let alpha decrease continuously from beta to zero, using the placement R_alpha M+b(alpha). Next interpolate between b(0) and the translation at the start of M's original monotone motion. Each point stays in the horizontal side during this interpolation because that side is convex. Finally follow M's original clockwise omega-angle motion.

In terms of the starting shape q=R_beta p, the rotation angle in the first phase is alpha-beta, in the translation phase it is -beta, and in the last phase it is theta_original-beta. It starts at zero and ends at -omega-beta=-L. The phase endpoints match and all translations are continuous.

Thus R_beta M admits a right-angle motion. At every phase the SAME isometry is applied to every point, so every subset of M retains its containment. This is the exact shape-preservation needed in the uniqueness theorem. QED.

## Dependency boundary

The only substantive hypothesis not proved within this note is the pair of pinned edge inequalities (1); notes 10, 12 and 14, sections 1-7, establish them for every specified maximizing cap. The cap/fan definitions and the existence of the original monotone motion are part of the existing development. This proof eliminates the scalar/numerical inputs previously listed as item 5 in note 16.
