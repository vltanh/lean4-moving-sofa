# Exact coercivity of the four cap residuals

This is a written analytic proof, not a Lean-checked theorem. It sharpens the earlier 12/5 estimate. The sharpness statement below concerns the ambient residual space with a pinned translation, not the best constant among feasible sofas or after optimizing over translations.

## Lemma

Let 0 < phi < pi/4, v=pi/2, b=v-phi, T=pi-phi, and A=sec(phi). Let f be absolutely continuous on [0,pi], with f(v)=f(pi)=0. Suppose its four residuals belong to L2 on their respective intervals:

    r1 = -tan(t) f(t) - f'(t),                      (0,phi);
    r2 = f(t+v) - f'(t),                           (phi,b);
    r3 = f(T)/sin(T-t) - cot(T-t) f(t) - f'(t),     (b,v);
    r4 = cot(t) f(t) - f'(t),                      (v,pi).

Put R^2=sum_j ||rj||_2^2 and E=R^2/2. Then

    ||f||_infinity <= sqrt(2) sec(phi) R = 2 sec(phi) sqrt(E).

The constant is optimal for this pinned residual-space inequality.

## 1. Reconstruct f exactly

All formulas below hold first away from endpoints and extend by continuity. On the last interval, the integrating factor gives

    f(t) = -sin(t) integral_v^t r4(u)/sin(u) du.               (1)

For t<pi the integral is finite. Cauchy-Schwarz bounds the square by
(-sin(t)cos(t)) ||r4||_2^2, which tends to zero at pi. This also explains why the apparent endpoint singularity is harmless.

On the third interval,

    f(t) = -f(T) cos(t)/cos(phi)
           + sin(T-t) integral_t^v r3(u)/sin(T-u) du.         (2)

Here all denominators are bounded away from zero. In particular

    f(b) = -tan(phi) f(T) + integral_b^v r3(u)/sin(T-u) du.

On the middle interval,

    f(t) = f(b) - integral_t^b f(u+v) du + integral_t^b r2(u) du.

Substitute (1) and the expression for f(b), and interchange the integrals on the bounded rectangle. The combined r4 coefficient simplifies, yielding

    f(t) = integral_t^b r2(u) du
         + integral_b^v r3(u)/sin(T-u) du
         + integral_v^T G_t(u) r4(u) du,                     (3)

where

    G_t(u) = [A - sin(t)]/sin(u),        v <= u <= v+t;
             [A + cos(u)]/sin(u),       v+t <= u <= T.

Finally, on the first interval,

    f(t) = cos(t) [A f(phi) + integral_t^phi r1(u)/cos(u) du]. (4)

These are linear evaluation functionals on the Hilbert direct sum of the four L2 spaces. No independence assumption about residuals of a particular cap is needed for an upper bound.

## 2. Compute the exact evaluation norms

Let D(t) be the squared L2 norm of the coefficient vector in (1)-(4), so |f(t)|^2 <= D(t) R^2. Direct integration gives

    D(t) = cos(t)^2 [2 A^2 - tan(t)],          0 <= t <= phi;
           cos(t) [2 A - sin(t)],             phi <= t <= b;
           sin(t)cos(t)+2 tan(phi)cos(t)^2,    b <= t <= v;
           -sin(t)cos(t),                     v <= t <= pi. (5)

Details for the cancellation in the middle interval: changing u=v+w gives

    D(t) = (b-t) + tan(phi)
         + [A-sin(t)]^2 tan(t)
         + integral_t^b [A-sin(w)]^2 sec(w)^2 dw.

An antiderivative for the last integrand is

    (A^2+1)tan(w) - 2A sec(w) - w.

Use tan(b)=cot(phi), sec(b)=csc(phi), and A=sec(phi). This reduces D(t) to cos(t)(2A-sin(t)). In particular D(phi)=2-sin(phi)cos(phi). Formula (4) then gives

    D(t)=cos(t)^2 [A^2 D(phi)+tan(phi)-tan(t)]
        =cos(t)^2 [2 A^2-tan(t)].

For the third interval the squared r4 coefficient norm is tan(phi)cos(t)^2, and the squared r3 coefficient norm is

    sin(T-t)^2 [tan(phi)-cot(T-t)].

Their sum is the third expression in (5). All adjacent formulas agree at their junctions.

## 3. Maximize over the whole interval

On [0,phi], D(t) <= 2 A^2, with equality at t=0. On [phi,b],

    D'(t) = -1 - 2 sin(t)[A-sin(t)] <= -1,

so D is decreasing. On [b,v], b>pi/4 and

    D'(t)=cos(2t)-4tan(phi)sin(t)cos(t) <= 0.

Thus D is nonincreasing from phi to v. On [v,pi], D<=1/2<2 A^2. Consequently max D=2 A^2, proving the lemma.

## 4. Sharpness in the pinned residual space

Take the residual tuple to equal the coefficient tuple for evaluation at t=0 in (3)-(4). Explicitly,

    r1(u)=sec(u),                              0<u<phi;
    r2(u)=A,                                  phi<u<b;
    r3(u)=A/sin(T-u),                          b<u<v;
    r4(u)=A G_phi(u) for v<u<T, and 0 for T<u<pi.

These are bounded piecewise smooth functions. Reconstruct f by (1)-(4). The resulting f is absolutely continuous, has the required endpoint values, and has exactly these residuals almost everywhere. Its residual norm squared and f(0) are both D(0)=2 A^2. Hence ||f||_infinity/sqrt(E)=2 A and equality is attained. This witness need not be a difference of two admissible cap supports.

## 5. Consequence for the continuous sofa functional

For K in Ki, put Delta=h_K-h_KG, s=-Delta(pi), and f=Delta-s cos(t). The normalized top support gives f(v)=0; the definition of s gives f(pi)=0. The residuals above are precisely the differences of the four cap Mamikon tangent displacements. Compact convex supports are Lipschitz; the source's regularity identifies their derivatives with the tangent vertices almost everywhere. The Mamikon identities give finite residual energy.

For the canonical triples x0=xi_G and x1=xi_K, the affine-minus-squares identity is

    Q((1-lambda)x0+lambda x1)
       = (1-lambda)Q(x0)+lambda Q(x1)+lambda(1-lambda)E_all.

Since Q(x0)=M is the maximum, M-Q(x1)>=(1-lambda)E_all for every 0<lambda<1. Passing to lambda down to zero gives M-Q(x1)>=E_all>=E. Also A(K)<=Q(x1). Therefore

    ||h_K-h_KG-s cos||_{infinity,[0,pi]}
       <= 2 sec(phi) sqrt(M-A(K)).

The cap's lower semicircle support is determined by the two bottom endpoints, so the same bound holds on the full circle. The support-function formula for the Hausdorff distance between compact convex bodies yields

    d_H(K, K_G+(s,0)) <= 2 sec(phi) sqrt(M-A(K)).

For the source range phi in [0.039,0.04], cos(phi)>=1-phi^2/2>=1249/1250, hence

    2 sec(phi) <= 2500/1249 < 1001/500 = 2.002.

This constant bound is rational; it does not depend on a numerical optimization experiment. The theorem remains restricted to Ki. It does not by itself prove a rate for arbitrary moving sofas or for K minus its niche.
