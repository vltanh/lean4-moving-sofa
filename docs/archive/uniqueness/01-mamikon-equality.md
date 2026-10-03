# 01. Mamikon equality as a first-order equation

Date: 2026-10-02. Status: pen-and-paper proof, not a new Lean theorem.

This research track targets uniqueness of the actual maximizing shape up to Euclidean congruence, not uniqueness of Romik's parameters. CI is not being used as a runner. Research commits use `[skip ci]`; existing Lean files and workflows are not changed.

## Sources and conventions

The starting identity is Baek, *Optimality of Gerver's Sofa*, version 1, Theorem 7.4.1; in this repository it is `MovingSofaOptimality/Convex/Mamikon.lean`, `theorem7_4_1`. The square-gap calculation and equality equations below are derived here. The conventions are those of `MovingSofaOptimality/Basic/ConvexBody.lean` and `MovingSofaOptimality/Optimality/Concavity.lean`.

Write u(t)=(cos t,sin t), v(t)=(-sin t,cos t), and h_K(t)=max_{p in K} p.u(t) for a nonempty compact convex set K. At almost every t,

    v_K^+(t) = h_K(t) u(t) + h_K'(t) v(t).

No smooth-boundary assumption is needed. If K is contained in a ball of radius R about the origin, then |h_K(s)-h_K(t)| <= R |s-t|. Thus h_K is Lipschitz and absolutely continuous on every bounded interval. At a differentiability point, the directional derivative of the support function identifies the tangential coordinate of the supporting face; the two face endpoints coincide there. Exceptional normal directions do not affect the integrals below.

For a continuous bounded-variation curve z_K(t) on the supporting line at t, set

    alpha_K(t) = (z_K(t)-v_K^+(t)).v(t).

The existing Mamikon identity is M(K)=1/2 integral_a^b alpha_K(t)^2 dt. All alpha functions below are bounded and measurable by that theorem.

## Result 1: exact gap and its equality case

Suppose z_K is affine under Minkowski combinations and K_c=(1-c)K_0+c K_1. Support functions and supporting-face endpoints are affine under these combinations, so alpha_{K_c}=(1-c)alpha_0+c alpha_1. For 0<c<1,

    (1-c)M(K_0)+c M(K_1)-M(K_c)
      = c(1-c)/2 integral_a^b (alpha_1-alpha_0)^2 dt.

Proof: expand the three squares and integrate. Consequently the gap is zero if and only if alpha_1=alpha_0 almost everywhere on (a,b). At c=1/2 the coefficient is 1/8, not 1/4. For a sum of finitely many such Mamikon terms, equality forces equality in every term separately, because every gap is nonnegative.

This is stronger than merely knowing the value of the sum and does not replace almost-everywhere equality by pointwise equality of a potentially discontinuous face endpoint.

## Result 2: tangent-intersection equation and its complete kernel

Fix a target normal T. For T-pi<t<T, take z_K(t) to be the intersection of the supporting lines with normals t and T. Resolving along u(t),v(t) gives

    z_K(t).v(t) = [h_K(T)-h_K(t) cos(T-t)]/sin(T-t).

Let f=h_{K_1}-h_{K_0}. Equality in this Mamikon term gives, almost everywhere on its open interval,

    f'(t) = [f(T)-f(t) cos(T-t)]/sin(T-t).                 (T)

Every absolutely continuous solution is

    f(t) = f(T) cos(T-t) + C sin(T-t),                   (K)

for a single constant C on the interval. To prove this without differentiating f twice, differentiate

    [f(t)-f(T) cos(T-t)]/sin(T-t).

Its derivative is zero almost everywhere by (T). The quotient is absolutely continuous on each compact subinterval where sin(T-t) is nonzero; it is therefore constant there. Overlapping compact subintervals give one constant on the entire connected open interval. Continuity of f then supplies the endpoint values. This also covers intervals ending at T: no division by sin(0) or differentiability at that endpoint is used.

Equivalently f(t)=p.u(t) on the interval for some fixed vector p satisfying p.u(T)=f(T). Thus equality produces a translation mode on that interval; it does not, by itself, identify its translation with the modes on other intervals.

## Result 3: outer-corner equation

For z_K(t)=h_K(t)u(t)+h_K(t+pi/2)v(t), equality gives

    f'(t)=f(t+pi/2)                                     (O)

almost everywhere on the relevant interval. This is a nonlocal first-order constraint, not f'=0.

## Failed shortcuts recorded

- Nonpositive first variation proves maximality, not uniqueness.
- Zero first variation is insufficient even for f(x)=-x^2 at x=0: every direction has zero first variation there, while nonzero endpoints have smaller values.
- A single tangent Mamikon term has the nontrivial kernel (K). Calling that term strictly convex in the body would be false.
- Almost-everywhere equality cannot simply be evaluated at a junction. The valid bridge is absolute continuity of support functions, followed by continuity at endpoints.

The next task is to match all four cap intervals. This note does not yet conclude uniqueness of a cap or sofa.
