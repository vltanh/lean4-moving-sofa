# The deficit certificate does not require a smooth competing cap

**Status:** continuous analytic proof; not Lean-checked or independently reviewed. This is a new extension of the source statements, not an invocation of them with a deleted hypothesis. The geometric upper bound is a separate question, treated in 06-local-upper-bound.md.

Write v=pi/2, phi=phi_G, b=v-phi, T=pi-phi, ell=v-2phi, M=|G|. Let K0=K_G and xi0=(K0,B0,D0) be Gerver's canonical triple. A normalized right-angle cap is a compact convex body represented by its upper supporting half-planes and y>=0, with h_K(v)=1 and h_K(3v)=0. Vertical edges and atoms at the two cut normals are allowed.

## 1. Enlarged domain

Let Tbar consist of triples (K,B,D), with K any normalized right-angle cap and B,D nonempty compact convex subsets of K, subject to

    h_K(t)+h_B(t+pi) <= 1,             phi<=t<=v,
    h_K(t)+h_D(t+pi) <= 1,             v<=t<=T,

with equality at the two endpoints of each interval. In particular h_B(3v)=h_D(3v)=0. There is no curvature-density, injectivity, or area-threshold assumption on the competing cap.

Retain the source's curve-area definition of Q (UpperBound.lean, upperQ). Equivalently write Q=P_K-R_B-L_D, where

    P_K=|K|+J(Z_K,x_K(b))-J(x_K|[phi,b])+J(x_K(phi),W_K),
    W_K=((h_K(phi)-1)/cos(phi),0),
    Z_K=((1-h_K(T))/cos(phi),0),

and R_B,L_D are the source's two tangent-line Mamikon squares. This equivalence uses only the endpoint equalities and collinearity of the segment endpoints: the area of the arc and the two tangent segments is the Mamikon integral for an arbitrary convex body. It does not require differentiability of the competing body.

## 2. An explicit affine-minus-squares formula valid with atoms

For h=h_K define S_K as the sum of the four cap Mamikon integrals on

    (0,phi; target v), (phi,b; outer corner),
    (b,v; target T), (v,pi; target pi).

Derivatives of h are taken almost everywhere. All convex support functions are Lipschitz; the tangent-displacement integrands are bounded on these intervals, including at a tangent target endpoint. Indeed h is Lipschitz and the apparent divided difference in the tangent formula is bounded. Thus these integrals are well-defined without a curvature-density assumption.

The following explicit identity holds:

    P_K+S_K = Lambda(h),

    Lambda(h) = h(0)+h(pi)
      +(1+tan(phi)-sec(phi)) [h(phi)+h(T)]
      + integral_phi^b [h(t)+h(t+v)] dt - (1+ell).             (1)

In particular Lambda is affine, and

    Q(K,B,D)=Lambda(h_K)-S_K-R_B-L_D.                        (2)

### Proof of (1), including nonsmooth caps

The full-period support formula and integration by parts for the distribution h''+h give |K|=1/2 integral_0^pi (h^2-h'^2). The lower semicircle contributes zero: on its two quadrants the support is h(0)cos(t) or -h(pi)cos(t). This formula includes all curvature atoms; they must not simply be omitted from an open-arc decomposition.

For a fixed target A, put

    rho_A(t)=h(A)csc(A-t)-h(t)cot(A-t)-h'(t),
    F_A(t)=1/2 cot(A-t)[h(A)^2+h(t)^2]-h(A)h(t)csc(A-t).

On each interval away from A, direct differentiation almost everywhere gives

    1/2 [h^2-h'^2+rho_A^2] = F_A'.                          (3)

As t increases to A, F_A(t) tends to zero. To check this without differentiability at A, rewrite its numerator as

    cos(A-t)(h(A)-h(t))^2
      +2h(A)h(t)(cos(A-t)-1),

divided by 2sin(A-t), and use the Lipschitz bound. Thus the last interval in (1) contributes h(pi), even when K has a vertical edge at pi.

On the middle interval put k(t)=h(t+v) and

    F_c(t)=-h(t)k(t)/2+(k(t)-h(t))/2.

Using x_K=(h-1)u_t+(k-1)v_t, expansion gives

    1/2 [h^2-h'^2+(k-h')^2] - 1/2 x_K cross x_K'
      = F_c' + h+k-1.                                     (4)

These are identities of absolutely continuous functions on compact subintervals. Integrate (3) on the first, third and fourth intervals and (4) on the middle one. The two extra segment terms in P_K are

    J(x_K(phi),W_K)
      =-1/2 tan(phi)(h(phi)-1)^2
       -1/2(h(phi)-1)(h(phi+v)-1),
    J(Z_K,x_K(b))
      =-1/2 tan(phi)(h(T)-1)^2
       -1/2(h(b)-1)(h(T)-1).

The cut-end contributions reduce respectively to

    (1+tan(phi)-sec(phi))h(phi)-1/2,
    (1+tan(phi)-sec(phi))h(T)-1/2.

Together with h(0), h(pi), and the middle integral this is (1). No equality of one-sided vertices at a cut was used. This is the required repair to the source's presentation, whose corresponding proof was stated in Ki.

## 3. First variation at Gerver on the enlarged domain

For xi=(K,B,D) in Tbar let Delta h_C=h_C-h_C0. The derivative at xi0 along the Minkowski segment toward xi is

    DQ(xi0;xi-xi0)
      = integral_[v-theta,v) [h_K(t)+h_B(t+pi)-1] d mu_B(t)
       + integral_(v,v+theta] [h_K(t)+h_D(t+pi)-1] d mu_D(t), (5)

where mu_B(E)=sigma_B0(E+pi), mu_D(E)=sigma_D0(E+pi). Both measures are nonnegative. Therefore this derivative is nonpositive.

Here is why the source's derivative computation extends to Tbar. The mixed-area derivative is integral Delta h_K d sigma_K0 for any pair of convex bodies. The floor term vanishes since both floor supports are zero. The convex-arc derivative formula already applies to arbitrary convex bodies. The core derivative follows by integration by parts for the two Lipschitz corner paths; only the reference path x_K0 is differentiated in the resulting integral, so the competitor need not be C^1. The segment formulas are algebraic. Gerver's matching endpoints X_B0=x_K0(phi), Y_D0=x_K0(b) make all endpoint terms telescope; the two remaining floor cross products vanish. This gives the four-integral formula of source Theorem 8.5.6, with no regularity requirement on xi.

Now use the already established reference measure identity (Main.lean, gm_sigma_decomp): sigma_K0 is the core measure iota_K0, the two reflected tail measures, and the top atom. The core terms cancel. The top atom multiplies Delta h_K(v)=0. The reflected tail measures are supported on the intervals in (5), where the reference wall constraints are equalities. These observations give exactly (5), as in source Theorem 8.5.7. All smoothness in this step belongs to Gerver, not to the competing cap.

## 4. Exact deficit identity and cap estimate

Let E_all be one half of the sum of the six integrals of squared differences of tangent displacements between xi and xi0. Let L(xi) be minus the right-hand side of (5), a nonnegative quantity. Formula (2) is affine minus squares, so its exact quadratic expansion, not a Taylor remainder estimate, is

    M-Q(xi)=L(xi)+E_all.                                   (6)

Consequently every xi in Tbar satisfies Q(xi)<=M and

    E_cap <= E_all <= M-Q(xi),                             (7)

where E_cap retains only the four cap terms. Horizontal translation is their null direction. Pin it by

    s=-(h_K(pi)-h_K0(pi)),
    f=h_K-h_K0-s cos(t).

Then f(v)=f(pi)=0. The Green-kernel lemma in 01-cap-coercivity.md was proved for absolutely continuous f with finite residual energy, not only for smooth support functions. It therefore gives

    d_H(K,K0+(s,0)) <= 2sec(phi) sqrt(M-Q(xi)).              (8)

Equation (8) holds on the enlarged algebraic domain Tbar. To replace Q(xi) by A(K), one must still supply a feasible canonical triple and prove the geometric upper bound. The next note does this locally near Gerver.

## Source and diagnostic audit

Primary dependencies: the definitions in Optimality/UpperBound.lean; arbitrary-convex-body Mamikon and arc identities in Convex/Mamikon.lean and Convex/CurveArea.lean; Gerver's reference measure identity in Main.lean. The corresponding prose is docs/proof/09-optimality.md, Sections 9.2--9.4 (especially Theorems 9.29--9.31).

An independent local check of (1)--(2) on the existing nonsmooth polygonal normal fan, including its equality-eliminated affine coordinates, gave maximum coefficient discrepancy 2.44e-13 at mesh 4. The scalar values Q+S+R+L and Lambda were 5.146586254401971 and 5.146586254401988. This checks signs and constants only; the continuous proof is (3)--(4). A reproducible check will be committed separately. No CI or Lean build was run.
