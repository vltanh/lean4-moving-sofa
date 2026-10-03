# Uniqueness of Gerver's sofa: complete paper argument

> **Status.** This argument is formalized in Lean in [`MovingSofaUniqueness/`](../../MovingSofaUniqueness): the proof compiles with no
> `sorry` and only Lean's standard axioms. [`docs/UNIQUENESS.md`](../UNIQUENESS.md) lists the Lean form of each
> proposition and the places where the formal proof takes a different route. The "Verification
> boundary" paragraph below describes the state before the formalization.

Date: 2026-10-02.

## Theorem

Let G be Gerver's sofa, with the definition used in this repository, and let S be a nonempty closed connected moving sofa in the unit right-angled hallway. If |S|=|G|, then there is a Euclidean isometry U such that

    U(S)=G.

This is equality of sets. No regularity, symmetry, parameterization, or prescribed motion is assumed for S beyond the definition of a moving sofa.

**Verification boundary.** The argument below is a pen-and-paper proof relative to the previously established optimality and geometric facts explicitly listed next. The additional uniqueness lemmas are proved here and in the linked detailed notes, not posited as hypotheses. This manuscript has not been independently reviewed or formalized in Lean. Historical machine checks of other files do not certify it.

## Established inputs and notation

Put L=pi/2, u_t=(cos t,sin t), v_t=(-sin t,cos t), and M=|G|. Area is planar Lebesgue measure. For a nonempty compact convex set K, let h_K be its support function and sigma_K its curvature measure on normal angles, so in distributions h_K''+h_K=sigma_K. At a polygon normal, sigma_K({t}) is the length of the corresponding facet.

A standard omega-cap has upper strip supports h_K(omega)=h_K(L)=1 and lower strip supports h_K(omega+pi)=h_K(3L)=0. Its allowed upper defining normals are

    J_omega=[0,omega] union [L,L+omega].

Repeated conditions are identified when omega=L. Write N_omega(K) for the fan intersected with the union of the open inner quadrants, and

    A_omega(K)=|K|-|N_omega(K)|.

The fan, not the bounded parallelogram, is used in both the finite and infinite niche definitions.

We use the following results of the existing optimality development.

1. G is a moving sofa; M>11/5; every moving sofa has area at most M. For each fixed omega in (0,L], the global maximum of A_omega over caps is attained by a cap whose cap-minus-niche set is a moving sofa. In particular A_omega(K)<=M for EVERY cap. The last conclusion is numerical only and does not replace a specified K by that auxiliary maximizing cap.
2. A moving sofa of area at least 11/5 admits an angle omega in [arcsec(11/5),L]. After translation to standard position it is contained in its own monotonization. This monotonization is a moving sofa of the same angle; if K is its own cap, it equals K minus N_omega(K), with area A_omega(K).
3. For any finite-angle polygon cap, not necessarily a maximizing one, there are nonnegative completed-inner-boundary lengths tau_K(t). At floating normals they are the lengths of the corresponding exposed inner half-rays. At a pinned normal k in {omega,L}, sigma_K({k+pi})-tau_K(k) is the niche's length on the lower fan boundary. The completed inner and outer upper boundaries have the same endpoints. The outward ASSIGNED-height variation of the finite area functional has first derivative sigma_K({t})-tau_K(t), with the lower strip moved as well when t is pinned.
4. For K in the domain K^i (a right-angle cap satisfying the injectivity condition and |K|>=11/5), its canonical triple x=(K,B_K,D_K) belongs to the convex domain of Q and

       A_L(K)<=Q(x)<=Q(x_G)=M.

   The concavity gap of Q is the sum of six nonnegative Mamikon gaps, four belonging to the cap. A Mamikon term is one half the integral of its squared tangent displacement; that displacement is affine under Minkowski combinations.
5. Gerver's cap and envelope have the geometric properties used in Proposition 6 below: the stated contact curves, derivative signs, matching endpoints, monotonicity of -alpha/beta, and path height at most one.

Input 1 follows from Theorem 1.1.1 and Theorems 3.5.2-3.5.6; input 2 from Theorem 1.5.1, Proposition 2.3.1 and Theorems 2.3.2, 2.4.3, 2.5.10. Input 3 is the general geometry preceding balancedness in Lemmas 3.4.5-3.4.8, with the corrected pinned niche sign. Input 4 is Chapters 7-8; input 5 is the repository's Gerver structure/envelope development. Thus none of the inputs asserts uniqueness, or that every cap maximizer is balanced or satisfies injectivity.

## Proposition 1. Select polygon approximations of a specified maximizer

Let K_* be a specified global maximizer of A_omega. There are finite-angle polygon caps K_n converging to K_* such that K_n maximizes

    A_n(K)-lambda_n P(K),
    P(K)=integral_0^(L+omega) (h_K-h_{K_*})^2,

on a compact polygon-cap family, where lambda_n tends to zero. At omega=L any artificial horizontal box constraint is eventually inactive.

### Proof

Use the nested mesh Theta_n={j delta_n:1<=j<2^n}, with delta_n=omega/2^n. Define C_n(K) using the two fixed strips and the upper supports at Theta_n and Theta_n+L; let N_n(K) use those sampled inner quadrants. Set A_n(K)=|C_n(K)|-|N_n(K)|.

For omega<L the cap family lies in the fixed parallelogram P_omega and contains a common positive-area triangle. To check the latter without assuming a contact that has not been proved, put c=sec(omega)-tan(omega) and o=(c,1). A contact on the omega support line has form o-lambda v_omega, lambda>=0; a contact on the top support line has form o-mu u_0, mu>=0. The former shows h_K(t)>=o.u_t on [0,omega], and the latter shows it on [L,L+omega]. Thus o belongs to K. Moreover o.u_t>=c>0 on the entire upper interval, so O and (c,0) also satisfy all the cap inequalities. Therefore conv{O,(c,0),o} lies in every cap. Fix an interior ball of this triangle.

For omega=L, restrict instead to caps inside [-R,R] x [0,1], with the target strictly inside the horizontal bounds. The family includes possible vertical-segment limits. Each of these families is compact: convex bodies in a common bounded box are Hausdorff precompact; the strip supports persist in a limit; and the restriction on normals is closed. At a right angle the latter is also immediate from downward closure above the floor, which persists under limits.

We need uniform approximation, not merely pointwise convergence. Here are the details that make it available. At a right angle a wedge has vertical height

    F(K,x,t)=max(0,min((h_K(t)-1-x cos t)/sin t,
                      (h_K(t+L)-1+x sin t)/cos t)).

For x in a common bounded interval it extends continuously by zero at t=0,L. Near 0 the second threshold is bounded above by a constant times t, using h_K(L)=1 and the uniform Lipschitz bound on supports; near L use the first threshold. The outer maximum with zero supplies the lower bound. Each wedge has abscissa in the common horizontal box. Consequently maxima over the full angle interval and over the meshes converge uniformly in K and x. Integrating proves uniform convergence of niche areas.

For omega<L use fan coordinates p=s(u_0-v_omega)+r(u_0+v_omega), r>=|s|. The coefficients of r in the two quadrant inequalities are

    cos t-sin(omega-t),    cos(omega-t)-sin t,

both strictly positive on [0,omega], with a positive minimum for fixed omega. Thus the wedge height above r=|s| is the positive part of the minimum of two jointly continuous thresholds minus |s|. It is zero at both angle endpoints. The support bounds and cos(omega)>0 give a common bounded s-range. Uniform convergence of sampled maxima and integration, now with Jacobian 2 cos(omega), prove the same conclusion.

The circumscribed caps C_n(K) decrease to K. For fixed n their dependence on K is continuous. At omega<L this follows from the common interior ball. At omega=L choose a top point (x_0,1) of K: (x_0,1/2) has slack at least sin(t)/2 at each sampled upper normal t, and slack 1/2 at the floor. This gives an interior ball for the fixed mesh even for a degenerate limiting K. Finite half-plane intersections therefore depend continuously on their heights. Continuity of convex area and Dini's theorem give uniform convergence of |C_n(K)| to |K|. We have proved

    e_n=sup |A_n-A_omega| -> 0,    A_n>=A_omega.                (9)

The polygon subfamily is closed, hence compact. The recovery polygon r_n=C_n(K_*) belongs to it for large n, converges to K_*, and preserves every sampled actual support: containment of K_* and the defining inequalities give the two opposite inequalities. Hence A_n(r_n)=A_n(K_*)>=A_omega(K_*).

Choose lambda_n>0 tending to zero with e_n/lambda_n tending to zero. Compare an exact maximizer K_n of A_n-lambda_n P with r_n. Global maximality of K_* gives

    0<=P(K_n)<=P(r_n)+e_n/lambda_n ->0.                       (10)

The continuous upper supports, together with the fixed lower cap inequalities, determine a standard cap. Thus P vanishes only at K_*. Compactness and (10) force convergence of the whole sequence. In the right-angle case the target's strict horizontal margin makes the box constraint eventually inactive. QED.

The detailed compactness and endpoint arguments are in [note 12](12-compact-selection-proof.md). This proposition does not say that exact UNPENALIZED maximizers approximate every maximizer; that statement is false, as recorded in note 03.

## Proposition 2. The selected polygons have controlled variation defects

Write d_n(t)=sigma_{K_n}({t})-tau_{K_n}(t). For floating normals,

    d_n(t)<=C lambda_n delta_n.                               (11)

For fixed omega<L and each pinned k in {omega,L},

    |d_n(k)|<=C_omega lambda_n.                               (12)

### Proof

Consider a positive floating facet at t with adjacent allowed normals a<t<b. Increase its assigned height by epsilon. Its ACTUAL support variation is the sine hat

    H_t(s)=sin(s-a)/sin(t-a) on [a,t],
    H_t(s)=sin(b-s)/sin(b-t) on [t,b],
    H_t(s)=0 elsewhere, periodically.

Indeed the changes of derivative jumps at a,t,b are respectively

    epsilon/sin(t-a),
    -epsilon(cot(t-a)+cot(b-t)),
    epsilon/sin(b-t).

They preserve nonnegative facet lengths for sufficiently small positive epsilon: neighboring jumps increase, and the only possible decrease is at the assumed positive facet. This also covers zero-length neighboring facets. All other sampled supports remain fixed.

On the selector's upper integration interval the hat has support of length at most 2delta_n and height at most 2. In the extreme cell, for example, H_delta(s)=cos(s)/cos(delta) on [0,delta]; the long lower-normal part is OUTSIDE the selector. Its integral over the upper interval is at most 4delta_n. The bounded support difference consequently gives |D_+P|<=C delta_n.

Input 3 and penalized maximality, with epsilon tending to zero at fixed n, prove (11). If the facet length is zero, (11) follows directly from tau>=0. No uniform admissible epsilon and no uniform quadratic remainder are required.

For a positive pinned facet at L, move y<=1,y>=0 to y<=1+epsilon,y>=epsilon, keeping the other assigned data fixed. A point inside the top facet witnesses attainment of its new support. A point inside the old bottom segment witnesses the new floor support. The other strip's two supports remain attained, using o and a short nonzero point on its lower ray. Translating by (epsilon tan(omega),-epsilon) restores standard position.

The actual floating supports of the perturbed polygon can be less than the assigned values. This causes the actual niche to be SMALLER than the assigned niche, whereas the cap intersection is unchanged. Thus its actual area objective is at least the assigned objective, which is the direction needed for the maximality comparison.

For completeness, the uniform penalty bound is not inferred from diameter alone. If B(q,rho) lies in K and every assigned height changes by at most a epsilon, direct substitution into the defining inequalities gives, for eta=a epsilon/rho<1,

    (1-eta)K+eta q subset K' subset (1+eta)K-eta q.

The common interior ball from Proposition 1 therefore gives a mesh-independent Hausdorff bound O_omega(epsilon), also after normalization. The penalty changes by O_omega(epsilon).

The cap area derivative is sigma(L)-sigma(3L). Only the fan floor changes in the assigned niche; its area derivative is minus its floor-section length, namely tau(L)-sigma(3L). Subtraction gives d_n(L). Penalized maximality now gives d_n(L)<=C_omega lambda_n. Reflection proves the same for omega. Zero-length pinned facets need no perturbation.

Finally input 3 gives the endpoint identity

    sum_t d_n(t)v_t=0,    sum_t d_n(t)sin(t)=0.                (13)

All upper normals have positive sine. By (11) and the two pinned upper bounds, the weighted sum of positive defects is O_omega(lambda_n); by (13) the weighted sum of negative defects is the same. Divide only by sin(omega) and sin(L), not by an extreme mesh sine, to obtain (12). QED.

Exact hat and pinned-feasibility details are in [note 10](10-local-variation-audit.md) and [note 14, sections 1-6](14-fixed-angle-maximizer.md).

## Proposition 3. Every maximizing right-angle cap satisfies injectivity

Let K_* be any global maximizer of A_L. Then K_* belongs to K^i.

### Proof

Select K_n as above in an eventually inactive box, giving a uniform diameter bound D. Fix a first-quadrant floating normal t and abbreviate

    s=sigma_{K_n}({t}), q=tan(delta_n/2), T=tan(delta_n),
    a=|g_{K_n}^+(t)-1|.

Here f and g are the usual nonnegative tangent-arm lengths. The following inequality is purely geometric:

    tau_{K_n}(t)<=T(a+q)+(2q-s)_+.                            (14)

To check it, partition the exposed inner half-ray by the union of the three opposite inner half-planes at t-delta_n,t,t+delta_n. Its intersection with that union has length at most

    max(T(g^-(t)-1+q)_+, T(1-g^+(t)+q)_+)<=T(a+q),

since g^-<=g^+. The remaining part must satisfy the three same-side inner half-plane inequalities. On b(t), their signed interval length is

    [2h(t)cos(delta_n)-h(t-delta_n)-h(t+delta_n)
                         +2(1-cos(delta_n))]/sin(delta_n)
      =2q-s.

Its length is the positive part. At the two end cells, the virtual inner quadrants at 0,L do not meet y>=0 and can be included in this argument. Their virtual supporting lines meet the extreme facets at the actual bottom vertices, so the same intersection formulas hold there.

Combining (11) and (14), solving separately for s>=2q and s<2q, and using 0<=g^+<=D gives

    sigma_{K_n}({t})<=delta_n k(g_{K_n}^+(t))
                       +C_D delta_n^2+C lambda_n delta_n,
    k(x)=max(|x-1|,(|x-1|+1)/2).                              (15)

The sum of errors is O(delta_n+lambda_n), not O(lambda_n/delta_n).

We spell out the limiting issue at normal zero. Spread each first-quadrant atom at j delta_n uniformly over [(j-1)delta_n,j delta_n). For a continuous test function the discrepancy from the atomic measure is at most its modulus of continuity at delta_n times the bounded total mass. At almost every angle the limiting support face in the opposite quadrant is a singleton; supporting points at converging normals therefore converge to that point. The bounded step functions k(g_{K_n}^+) in (15) converge almost everywhere, so dominated convergence and weak curvature convergence yield

    sigma_{K_*}|[0,L) <= k(g(t))dt,
    sigma_{K_*}|(L,pi] <= k(f(t-L))dt.                        (16)

In the first passage use tests supported on a circular arc (-epsilon,L) that may be nonzero at 0. Reflection gives the second passage, including pi. Thus (16) proves absence of atoms at 0 and pi; it does not assume it. The atom at L is allowed.

The distribution identity h''+h=sigma now gives separate C^1 restrictions on [0,L] and [L,pi], with absolutely continuous derivatives. Their one-sided derivatives at the common top need not coincide. The nonnegative arm functions

    f(t)=h(t+L)-h'(t),    g(t)=h(t)+h'(t+L)

use the corresponding one-sided endpoint values, and are absolutely continuous on [0,L]. The absence of the end atoms and the bottom-segment geometry give f(0)=g(L)=1. If r,s are the two curvature densities, then

    f'=g-r,    g'=s-f.

Thus (16) implies

    f(t)>=1+integral_0^t m(g),
    g(t)>=1+integral_t^L m(f),    m(x)=x-k(x).                 (17)

Here is an analytic bootstrap, avoiding finite numerical iteration. For x>=0,

    m(x)=3x/2-1 on [0,1], x/2 on [1,2], and 1 on [2,infinity),
    m(x)>=1/2-(3/2)(1-x)_+.

Let p=(1-f)_+, q=(1-g)_+, and H=max(p,q) over the interval. If H>0 then H<=1 by nonnegativity, and (17) forces H>1/3. Put b=(3H-1)/2. The integral inequalities imply

    p(t)<=min(H,bt),    q(t)<=min(H,b(L-t)).

At a point attaining H, and reflecting the interval if necessary,

    H<=I:=integral_0^L [(3/2)min(H,br)-1/2]_+ dr.

The integrand rises from zero to b between r=1/(3b) and r=H/b, an interval of length 2/3, and then stays constant. If L<=H/b, I<=b/3<H. Otherwise I=b(L+1/3)-H. Since L=pi/2<5/3, this is less than 2b-H=2H-1<=H. Both are contradictions. Therefore f,g>=1. Substitute this in (17) to obtain

    f(t)>=1+t/2,    g(t)>=1+(L-t)/2.                          (18)

The inner corner x_K(t)=(h(t)-1)u_t+(h(t+L)-1)v_t is C^1 on its closed parameter interval and

    x_K'(t)=(1-f(t))u_t+(g(t)-1)v_t.

Its two components have the required strict signs for 0<t<L by (18). Together with (16), these are all three injectivity conditions. Finally |K_*|>=A_L(K_*)=M>11/5. Hence K_* belongs to K^i. QED.

The complete local and endpoint calculations appear in [note 13](13-every-right-angle-maximizer.md); the scalar lemma is independently proved in [note 11](11-analytic-arm-bootstrap.md).

## Proposition 4. The specified maximizing monotone sofa has a right-angle motion

Suppose omega is in [arcsec(11/5),L), K_* globally maximizes A_omega, A_omega(K_*)>=11/5, and K_* minus N_omega(K_*) is a monotone sofa M_*. A rotated copy of that same M_* has a right-angle motion.

### Proof

For arbitrary polygon caps, the portion of the bottom segment outside every wedge has length at least w_K^circ, and belongs to the completed inner boundary at L. Hence w_K^circ<=tau_K(L); similarly z_K^circ<=tau_K(omega). The bottom-segment bound includes all unsampled angles because W_K(t) tends to O as t tends to omega from below.

Apply these inequalities to the selected K_n and use (12). The gap infima are Lipschitz in Hausdorff distance with constant 1+sec(omega). Weak curvature convergence gives limsup sigma_{K_n}({k})<=sigma_{K_*}({k}) at the fixed pinned normals. Therefore

    w_{K_*}^circ<=sigma_{K_*}({L}),
    z_{K_*}^circ<=sigma_{K_*}({omega}).                        (19)

The exact geometric conclusion of (19) is proved in [note 19](19-exact-angle-reduction.md); its essential algebra is included here. Set T=tan(omega), c=sec(omega)-tan(omega), and take d_0=5/4 for T<11/5, or d_0=11/10 otherwise. If both outer extents were at most c+d_0, the cap would lie in a truncated parallelogram of area

    c+2d_0-d_0^2/T<11/5,

contradicting |K_*|>=A_omega(K_*)>=11/5. For the first case the bound is at most 359/176<11/5; for the second it follows from c<1/T. Reflect temporarily if needed to choose the right extent h_K(0)=c+d, with d>=d_0 and d<=T.

Put r_y=1-d/T and g=sqrt(1-r_y^2). We have

    d sin(omega)>1,    g>2 cos(omega).                        (20)

These inequalities have exact certificates, not decimal tests. For d_0=5/4 the first square is at least 150/121, and the second reduces, with z=T-19/10>=0, to

    40z^3+139z^2+135z+407/100>0.

For d_0=11/10 the first square is at least 14641/14600, and the second, with z=T-11/5>=0, to

    220z^3+931z^2+1122z+4598/25>0.

The supporting intersection r=(c+d,r_y) and point s=(c+d-g,0) satisfy |r-s|=1. Sine interpolation of the supports at 0,omega gives h_K(t)-1<=s.u_t for 0<t<omega; hence all right wedge gaps are at least g. By (19) the top edge has length at least g. Therefore both

    q_0=(c+d,0),    q_1=(c-g,1)

belong to K_*.

Let a=L-omega in (0,omega). By (20), the two support witnesses q_0,q_1 place all three vertices O,c u_0,c v_omega strictly inside Q_K^-(a). Explicitly the two required gaps are d sin(omega) and -cos(2omega)+g cos(omega), each greater than one. Consequently

    Delta=conv{O,c u_0,c v_omega} subset N_omega(K_*).

Reflection exchanges u_0 with v_omega and preserves Delta, the fan, and the normal interval [omega,L]. Thus this conclusion transfers back to the original cap when its left extent was chosen. No different maximizing sofa is substituted.

Cutting Delta off P_omega leaves a polygon whose width in normal direction t in [omega,L] is

    max(sin t,cos(t-omega))<=1.

Thus M_* itself has all these widths. Put beta=L-omega. Rotate R_beta M_* clockwise through beta inside the horizontal strip, positioning it continuously by its support function; interpolate translations inside the horizontal side to the start of its original motion; then follow its original omega-angle motion. Relative to the starting copy the total angle is -beta-omega=-L. The explicit translations and matching phase endpoints are given in note 19, section 7. This is a motion of the same set and retains every contained subset. QED.

## Proposition 5. A maximizing cap in K^i is the Gerver cap up to translation

### Proof

For its canonical triple x, input 4 gives A(K)=Q(x)=Q(x_G)=M. Concavity and maximality make Q constant on the segment between x_G and x. Each of the six nonnegative Mamikon gaps is therefore zero.

Write f=h_K-h_{C(G)}. Support functions are absolutely continuous and f(L)=0. The midpoint gap of a cap term is one eighth the integral of the squared difference eta of its tangent displacements. Its vanishing implies eta=0 almost everywhere. For a tangent target T this means

    sin(T-t)f'(t)+cos(T-t)f(t)=f(T),

whose solutions are f(t)=f(T)cos(T-t)+b sin(T-t). For the outer-corner term the equation is f'(t)=f(t+L).

The four cap intervals are (0,phi), (phi,L-phi), (L-phi,L), (L,pi), with tangent targets L, none, pi-phi, pi respectively. Solve them in reverse dependence order. On (L,pi), f(L)=0 gives f(t)=a cos t, a=-f(pi). On (L-phi,L), the known value at pi-phi and f(L)=0 give the same formula. The middle equation becomes f'(t)=-a sin t; matching its right endpoint removes the integration constant. On (0,phi), the target value f(L)=0 gives f(t)=b cos t and matching at phi gives b=a. Continuous endpoint limits are legitimate and require no smooth boundary.

Thus f(t)=a cos t on [0,pi]. The lower supports of a right-angle cap are those of its bottom segment, because vertical projection to that segment increases every lower-normal scalar product. The segment's endpoints also differ by (a,0). The full support functions therefore agree after that translation, proving

    K=C(G)+(a,0),    K minus N_L(K)=G+(a,0).                  (21)

The second equality follows from horizontal translation covariance of the fan and every inner quadrant. QED.

There is also an explicit stability version in [note 17](17-quantitative-cap-rigidity.md): for every K in K^i,

    d_H(K,C(G)+(a,0))^2 <= 6(M-A_L(K)).                       (22)

It controls the apparently singular target endpoint in the fourth tangent term by the exact factor sin(pi-t)cos(pi-t)<=1/2. No inference from almost-everywhere equality of planar sets is involved in (21).

## Proposition 6. Gerver's sofa is regular closed

    G=closure(interior G).

### Proof

Use its existing rotation path x'=alpha u+beta v, with alpha<0, beta>0 and -alpha/beta nondecreasing on (0,L), and its inner envelope curves B=x+alpha v and D=x-beta u. On their relevant intervals,

    D'=(1-rho_C)u,    B'=(rho_A-1)v,

with rho_C,rho_A<1. The derivative statements are valid off finitely many junctions; the curves are continuous. Thus D, followed by x in reverse and then B, has strictly increasing abscissa. Their known matching endpoints make this curve the graph of a continuous height H on I=[D(0)_x,B(L)_x], with zero endpoint heights. The niche is exactly the region 0<=y<H(x).

The cap's top endpoints are D(0)+(0,1) and B(L)+(0,1). Convexity and downward closure give the entire rectangle I x [0,1] inside the cap. Each B or D envelope point has height less than one, by x_y<=1 and the strict signs above. A height-one point on the x-piece must have zero vertical derivative, giving

    -alpha(t)/beta(t)=cot(t).

The left side is nondecreasing and the right side strictly decreasing; there is at most one such point. Hence H<1 on a dense subset of I.

For any (x,y) in G with x in I, choose interior abscissas x_n tending to x with H(x_n)<1 and heights H(x_n)<y_n<1 tending to y. These are interior points of G by continuity of H. This includes both endpoints and a possible single height-one contact. Outside I a neighborhood misses the niche; the convex full-dimensional cap has dense interior, so those points also have interior approximations. Closedness of G supplies the reverse inclusion. QED.

All geometric inputs and the approximation argument are detailed in [note 07](07-regular-closedness.md). No Jordan-curve assumption or new numerical height bound is required.

## Proof of the theorem

By M>11/5 and input 2, translate S to standard position S_0 at some angle omega in [arcsec(11/5),L], and let M_0 be its own monotonization. Then

    S_0 subset M_0,
    M=|S_0|<=|M_0|<=M.

Therefore |M_0|=M. Its OWN cap K has A_omega(K)=M and M_0=K minus N_omega(K). By input 1, K is a global cap maximizer.

If omega<L, Proposition 4 gives a rotation V such that V(M_0) has a right-angle motion; if omega=L, take V to be the identity. Translate V(M_0) to standard right-angle position by W and monotonize once more, obtaining T_0. The actual inclusions are

    W(V(S_0)) subset W(V(M_0)) subset T_0.

All three areas are M by optimality. The OWN cap J of T_0 globally maximizes A_L. Proposition 3 puts J in K^i, and Proposition 5 gives

    J=C(G)+(a,0),    T_0=G+(a,0).

Composing the actual translations and rotations used above with translation by (-a,0) produces an isometry U satisfying

    U(S) subset G,    |U(S)|=|G|.

The set U(S) is closed. If an interior point of G were missing from it, the intersection of interior G with its open complement would contain a positive-radius ball. That ball would be a positive-area subset of G minus U(S), contradicting equality of the finite areas. Therefore interior G is contained in U(S). Proposition 6 and closedness give G subset U(S), proving

    U(S)=G.

QED.

## Logical closure and scope

The global proof preserves the specified set through both monotonizations and the additional strip rotation. The new variational reductions apply to every specified cap maximizer, not just an auxiliary balanced one. The endpoint atoms, zero-length neighboring facets, assigned-versus-actual support comparison, and pinned-strip feasibility are handled before their conclusions are used. No extra geometric uniqueness assumption occurs in the hypotheses.

The original optimality proof and Gerver's established structure are inputs, as stated. No claim is made here about uniqueness of motions or of the auxiliary triple representation. The quantitative result (22) concerns caps in K^i; it is not a claimed quantitative theorem for arbitrary sofas. The argument constructs no noncongruent maximizing shape.

The completed mathematical argument remains subject to independent review and subsequent formalization. Neither has been represented as already performed.
