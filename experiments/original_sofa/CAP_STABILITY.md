# A quantitative cap estimate from the uniqueness argument

**Status:** an analytic deduction from the source's continuous Q identities,
written out below. This is not a Lean theorem, is not based on numerical
positive definiteness, and has not received independent review. The numerical
experiments following the proof are diagnostics only.

## Proposition and scope

Let phi be Gerver's cut angle, and let K belong to Baek's injective cap class
Ki, with rotation angle pi/2 and the usual normalization of bottom and top
supports. Write A(K)=area(K)-area(N(K)), and M=area(G). Then the source's
upper-bound and concavity identities imply

    inf_s d_H(K, K_G + (s,0)) <= (12/5) sqrt(M - A(K)).

More precisely, the proof gives C(phi) in place of 12/5, where C(phi) is about
2.326 on the source's interval [0.039,0.04]. The explicit chosen translation is
s=-(h_K(pi)-h_G(pi)); no minimization over s is needed to obtain the estimate.

This is a stability estimate **for caps in Ki and the functional A**. It is
not a theorem for every near-optimal moving sofa, nor a Hausdorff estimate for
the nonconvex set K minus its niche. The exact-maximizer reduction in the
uniqueness proof does not by itself give regularity of arbitrary near-maximizers.
Recovering an arbitrary sofa from a nearly equal-area envelope also needs a
quantitative argument; equality/regular-closedness alone is insufficient.

## 1. The Q deficit controls difference squares

For x0=xi_G and any x1 in the continuous triple domain, write
E=1/2 sum_j integral (rho_j(x1)-rho_j(x0))^2, summed over the six Mamikon terms.
The affine-minus-squares decomposition gives, for 0<lambda<1,

    Q((1-lambda)x0+lambda x1)
      = (1-lambda)Q(x0)+lambda Q(x1)+lambda(1-lambda)E.

Since x0 maximizes Q and the domain is convex,
Q(x0)-Q(x1) >= (1-lambda)E. Letting lambda decrease to zero gives

    Q(x0)-Q(x1) >= E.

Only the four cap terms will be needed: E >= E_cap. The auxiliary-body terms
are nonnegative and may be dropped. This avoids any assumption of strict
concavity in all the K,B,D variables. In particular, no regularization of the
flat B,D directions is justified or necessary for this cap estimate.

For the canonical triple of K in Ki, A(K) <= Q(xi_K) <= Q(xi_G)=M, hence

    M - A(K) >= M - Q(xi_K) >= E_cap.

These are squares of **differences** of tangent displacements. The individual
Mamikon terms at Gerver need not be zero.

## 2. An elementary continuum coercivity lemma

Put v=pi/2, b=v-phi, T=pi-phi and ell=v-2phi. Let
Delta=h_K-h_G, s=-Delta(pi), and f(t)=Delta(t)-s cos(t). Then
f(v)=f(pi)=0. The same proof below works for any absolutely continuous f with
these endpoint values and finite residual energy.

Translation does not change any tangent-displacement difference. Thus the four
residuals, with the sign convention rho(line/outer corner)-h', are

    r1(t) = -tan(t) f(t) - f'(t),                       0<t<phi;
    r2(t) = f(t+v) - f'(t),                            phi<t<b;
    r3(t) = f(T)/sin(T-t) - cot(T-t) f(t) - f'(t),      b<t<v;
    r4(t) = cot(t) f(t) - f'(t),                       v<t<pi.

Let e_j=||r_j||_L2 on its interval. Then E_cap=(e1^2+e2^2+e3^2+e4^2)/2.
The source's injectivity hypotheses provide the requisite support regularity.
All equations and integrals below can also be read almost everywhere.

### Last interval: solve backwards from the fixed top support

The equation for r4 gives

    f(t) = -sin(t) integral_v^t r4(u)/sin(u) du.

Cauchy-Schwarz and integral_v^t csc(u)^2 du=-cot(t) imply

    |f(t)|^2 <= -sin(t) cos(t) e4^2 <= e4^2/2.

In particular, writing k=f(T),

    |k| <= sqrt(sin(phi) cos(phi)) e4.

The expression is used for t<pi and extends to pi by continuity. The apparent
singularity at pi therefore does not introduce an uncontrolled endpoint term.

### Third interval: propagate the last-interval endpoint value

Using f(v)=0, the equation for r3 integrates to

    f(t) = -k cos(t)/cos(phi)
           + sin(T-t) integral_t^v r3(u)/sin(T-u) du.

Here 0<=cos(t)<=sin(phi) and
integral_t^v csc(T-u)^2 du <= tan(phi). Therefore

    sup_[b,v] |f| <= tan(phi)|k| + sqrt(tan(phi)) e3.

### Middle interval: integrate the shifted last-interval values

The equation for r2 gives

    f(t)=f(b)-integral_t^b f(u+v) du + integral_t^b r2(u) du.

Since b-phi=ell,

    sup_[phi,b] |f|
      <= sqrt(ell) e2 + sqrt(tan(phi)) e3
         + [ell/sqrt(2)+tan(phi)sqrt(sin(phi)cos(phi))] e4.

### First interval: close the estimate

The integrating factor for r1 is sec(t), giving

    f(t)=cos(t)[f(phi)/cos(phi)+integral_t^phi r1(u)/cos(u) du].

It follows that sup_[0,phi]|f| is at most sec(phi) times the preceding
middle-interval bound, plus sqrt(tan(phi)) e1.

Define

    a1 = sqrt(tan(phi));
    a2 = sec(phi) sqrt(ell);
    a3 = sec(phi) sqrt(tan(phi));
    a4 = sec(phi)[ell/sqrt(2)+tan(phi)sqrt(sin(phi)cos(phi))].

The same sum sum_j a_j e_j bounds the other intervals as well: sec(phi)>=1
and ell>=1 on [0.039,0.04], so in particular a4>=1/sqrt(2).
Another application of Cauchy-Schwarz now gives

    ||f||_infinity <= sqrt(2 sum_j a_j^2) sqrt(E_cap).

This defines C(phi)=sqrt(2 sum_j a_j^2).

### A safe numerical constant, using elementary rational bounds

On [0.039,0.04], the elementary trigonometric bounds give

    tan(phi)<=0.041, sec(phi)<=1.001,
    sin(phi)cos(phi)<=0.04, 1<=ell<=1.494, 1/sqrt(2)<=0.708.

Consequently

    C(phi)^2
      <= 2[0.041+1.001^2*1.494+1.001^2*0.041
           + {1.001(1.494*0.708+0.041*0.2)}^2]
       < 5.436 < (12/5)^2.

The upper bound 1.494 uses pi<22/7 and phi>=0.039. The remaining bounds follow
for example from sin(phi)<=phi and cos(phi)>=1-phi^2/2. No floating-point
experiment is needed for these strict rational inequalities.

## 3. From support error to cap Hausdorff distance

On the lower semicircle, a normalized cap's support is determined by its two
bottom endpoints: h(0)cos(t) on the lower-right quadrant and -h(pi)cos(t) on
the lower-left. Thus the upper-semicircle bound also bounds the difference of
the full support functions. For compact convex bodies, Hausdorff distance is
the uniform distance between support functions. Combining this with Sections
1 and 2 proves the stated cap proposition.

## 4. Numerical cross-check, not a substitute for the proof

`stability.py` assembles only the four cap-square terms, fixes f(pi/2)=f(pi)=0,
and computes the norm of each continuous angular evaluation functional in the
inverse energy matrix. On each polygon-normal cell the evaluation norm is a
2-by-2 trigonometric quadratic form, whose maximum is checked at the cell ends
and its eigenvector directions, not just at sampled angles.

At phi=0.04, the best ambient polygonal constants observed were:

| Uniform intervals per quadrant | Cap constant | Smallest energy eigenvalue |
| --- | --- | --- |
| 4 | 1.983966901592 | 0.082537162420 |
| 8 | 1.997161577177 | 0.052976783518 |
| 16 | 2.000462468571 | 0.030854633471 |
| 32 | 2.001304945263 | 0.016789327131 |
| 64 | 2.001526954455 | 0.008777124838 |

The raw coordinate eigenvalue shrinks with dimension; that is not a loss of
coercivity in the geometrically relevant uniform norm. The numerical norm stays
near 2.002 and below the independently derived analytic bound 2.325194709846.
The extremizing linear evaluation was t=0 on each tested mesh. The program's
witness has energy 1 to about 4.2e-14 and attains the reported norm. These
calculations do not prove that the limiting best constant is 2.002, nor that
these unrestricted perturbations are all feasible cap perturbations.

## Sources and reproduction

The continuous identities are in `MovingSofaUniqueness/Rigidity.lean`
(`mamikonSegmentEquality_iff`, the tangent-displacement equality argument) and
`MovingSofaOptimality/Optimality/Concavity.lean` (`mamikonS`, `lemma8_3_7`,
`theorem8_3_8`), with the upper-bound theorem in `Optimality/UpperBound.lean`.
The same four intervals appear in Section 8 of the uniqueness paper.

    export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
    python experiments/original_sofa/stability.py --output /tmp/stability.json

No CI, Lean compilation, or formal proof validation was performed.
