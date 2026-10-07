# An explicit local cap radius

Analytic derivation, not Lean verification. This note quantifies the local
hypotheses used by `separated_upperQ_bound` rather than assuming a nearby cap
has the injectivity or curvature density of the reference.

Write v=pi/2, p=phi, b=v-p. Let Gcap have floor endpoints l,r, top-face
endpoints a,b0, and let h0 be its support. Do not confuse b=v-p with b0.
The reference coordinates satisfy

    r=1, l=2*kappa3.x-1,
    a=1-2*a1, b0=2*kappa3.x-a,
    D=a-l=r-b0 in (403/500,1),
    r-l<13/4, b0-a>1.

Reference facts used below follow from the explicit phase/contact formulas:

* the top face is exactly [a,b0] x {1};
* its upper curvature measure, except for that top face, has density at most16;
* the core path height on [p,v-p] is at least1/20 and everywhere at most2/3;
* writing x'=-A*u+B*v, both A,B are at least1/32 on
  J=[p/2,v-p/2], and both are nonnegative on the full turn;
* the cap contains [a,b0]x[0,1], and its floor endpoints.

The numeric reference checks are collected in the companion radius checker.
The contact/curvature interpretation and matching equations remain analytic
inputs, not facts inferred from sampling.

## 1. Quantitative exposed-point estimate away from the top face

Suppose K is a normalized right-angle cap and

    sup_[0,pi] |h_K-h0| <= delta,    0<delta<=10^(-40).          (1)

Set q=sqrt(delta). For any t whose q-neighborhood avoids v, and any exposed
point z of K at t, the two support inequalities at t+q and t-q bound its
v_t-coordinate. The reference support has the exact local representation

    h0(t+q)=h0(t)cos(q)+h0'(t)sin(q)
             + integral_t^(t+q) rho0(s)sin(t+q-s) ds.

The remainder has absolute value at most8q^2; sin(q)>=q/2. Together with
|h_K-h0|<=delta this gives

    |<z,v_t>-h0'(t)| <= 4delta/q+16q <=20sqrt(delta).

Its u_t-coordinate differs by at mostdelta. Hence every point of the entire
exposed face, including its two endpoints, is within

    64sqrt(delta)

of the unique reference support point. This holds on both angle intervals
needed by t in J, since q<p/4. The right/left corner derivatives are expressed
through those exposed points and the inner corner; the latter moves by at most
2delta. Therefore each one-sided inner-arm excess changes by at most

    128sqrt(delta)<1/64.

Both excesses of K are consequently at least1/64 on J. This controls right
derivatives and almost-everywhere derivatives even when K has edges or atoms.
No smoothness of K has been assumed.

## 2. Quantitative top-face localization

The previous argument cannot be used at v: the reference exposed face is a
segment, not a point. Instead fix 0<eta<=1/100 and put

    s=eta/512,   rho=eta^2/2^20,
    delta<=eta^3/2^24.                                       (2)

For an exposed point z of K at |t-v|<=rho, the containing rectangle and support
comparison imply

    1-z.y <=10rho+delta.

The one-sided top-face expansions are

    h0(v+s)<=cos(s)-a*sin(s)+64s^2,
    h0(v-s)<=cos(s)+b0*sin(s)+64s^2.

Insert z in the competing support inequalities at these two angles and use
sin(s)>=s/2. This gives

    a-E <= z.x <= b0+E,
    E=20rho/s+4delta/s+128s < eta/2.                         (3)

Every top-face point of K satisfies the same bound (take t=v). The point need
not be near the right endpoint of the reference face; only the interval (3)
is asserted. This distinction is needed in the terminal-strip proof.

## 3. Uniform niche-foot localization, including endpoint angles

For a floor-truncated inner wedge at angle t in (0,v), its feet are

    L_K(t)=(1-h_K(t+v))/sin(t),
    R_K(t)=(h_K(t)-1)/cos(t).

Every wedge point with nonnegative height has abscissa strictly between these
feet. The reference feet are in [a,b0]. If t>=rho, the left-foot support error
is at most delta/sin(rho)<=2delta/rho<=eta/8. If t<rho, use a support point of
K at t+v. Formula (3), its height at most one, and

    L_K(t)=z.x+(1-z.y*cos(t))/sin(t)>=z.x

give L_K(t)>=a-eta/2 without dividing delta by a vanishing sine. The right-foot
case near v is identical, using

    R_K(t)=z.x+(z.y*sin(t)-1)/cos(t)<=z.x.

Thus (2) implies that the ENTIRE niche has horizontal projection in

    [a-eta,b0+eta].                                         (4)

The hypotheses hold at delta<=10^(-40), both for eta=10^(-5) (niche windows)
and eta=10^(-8) (top-face accuracy).

## 4. Niche containment with a numerical upper-wall margin

Every niche point lies below its own inner corner. By (1), all competing
corners have height at most2/3+2delta<7/10. For every point z in
[a,b0]x[0,7/10], use a top-face endpoint and the corresponding floor endpoint
as support witnesses. If sin(t)>=1/4 the top witness gives slack at least3/40.
If sin(t)<1/4, the floor witness gives a larger slack, since

    D*|cos(t)|-(7/10)sin(t)> (4/5)*(9/10)-7/40 >1/20.

So every upper wall has reference slack at least1/20 on this rectangle.
Clamping the abscissa of a niche point in (4) to [a,b0] costs at mosteta=10^-5
in any unit-normal projection. Subtract the support error delta as well.
Since eta+delta<1/20, all its upper support inequalities hold for K. Its floor
inequality is already satisfied. Consequently

    N(K) subset K.                                         (5)

This proof does not derive global injectivity from Hausdorff proximity.

## 5. Cut separation and core height

For p<t<=1/2, the perturbed one-sided derivative of
<x_K(t),u_p> is at most -1/64: both core arm excesses are at least1/64, and
cos(t-p)+sin(t-p)>=1. Its value at p is h_K(p)-1, so the right cut is strictly
separated. For t>=1/2, the reference already has a gap at least

    (1/2-p)/32 >1/100.

The reference gap is nondecreasing thereafter because both reference arm
excesses are nonnegative. Moving the support and the corner costs at most
3delta, so separation persists to v. Reflection proves the left cut, using
the interval [v-1/2,v-p] for its near-cut part.

The reference core height is at least1/20; the competing corner differs in
height by at most2delta. It remains strictly positive. The core is a decreasing
Lipschitz graph by its positive one-sided arm margins, exactly as in the
existing nonsmooth core-area argument.

## 6. Canonical triple and area certificate

The horizontal width of K is at least that of Gcap minus2delta and in particular
exceeds21/10. The two cut-arm inequalities are strict by Section1. The elementary
canonical-contact construction therefore gives

    xi_K=(K,rightBody_p(K),leftBody_p(K)) in WideL_p.

The separated three-region niche argument, with (5), then gives

    A(K) <= Q(xi_K) <= M.                                   (6)

This is the original local geometric certificate with all its neighborhood
hypotheses supplied by the single numerical support condition (1). The second
inequality in (6) is the previously established wide-domain algebraic maximum.

## Scope and review

The proposed local support radius is10^(-40); it is deliberately very small,
not optimized. This note relies on the stated explicit reference contact facts
and on the existing separated-core/tail area theorem. It is not a replacement
for reviewing that theorem or for the global entry modulus. The radius checker
verifies numerical reference enclosures and the displayed scalar margins, not
arbitrary-set topology or Lean proofs.
