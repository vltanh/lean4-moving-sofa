# Effective right-angle entry by penalized regularization

Analytic proof, not a Lean formalization. This uses the polygon variation and
curvature arguments of the uniqueness development, but keeps their error
instead of sending a penalty coefficient to zero. The resulting constants are
intentionally coarse. The purpose is effective entry, not sharp stability.

## Statement

Let K be ANY normalized right-angle cap and e=M-A(K). If 0<=e<=10^(-4), then

    d_H(K_c,K_G,c) <= 514*sqrt(e),                            (1)

where the horizontal midpoints are aligned. No injectivity or curvature-density
condition on K is assumed. For an original sofa S admitting a right-angle
motion, if epsilon=M-|S|<=10^(-20), midpoint/top normalization satisfies

    d_H(S_c,G) <= 10300*sqrt(epsilon).                        (2)

The constants use existing explicit reference roof/ball estimates from notes
06 and 08. The new argument proving entry is below; it does not invoke the
local cap certificate to prove its own hypotheses.

## 1. Bounded caps without knowing their shape

For a right-angle cap of horizontal width W, |K|<=W. At t=pi/4 its inner
corner has height at least W/2-sqrt(2), using its two floor endpoints as support
witnesses. If this height is positive, the corresponding triangular niche has
area at least (W/2-sqrt(2))^2. Consequently

    A(K)<=W-(W/2-sqrt(2))_+^2.

Positive A(K) implies W<9: for W>=9, replace sqrt(2) by 3/2 and use
(W/2-3/2)^2-W=(W-9)(W-1)/4>=0, with strictness from sqrt(2)<3/2.
After centering the horizontal projection such a cap lies in [-9/2,9/2]x[0,1]
and has Euclidean radius less than 5.

We use Baek's established global cap bound A(C)<=M for ALL caps. This follows
from the fixed-angle maximizing-cap theorem and optimality; it does not require
the specified cap C to contain its niche. In particular, no assertion that an
arbitrary cap-minus-niche set is connected is hidden here.

## 2. The penalized comparison cap

Assume e>0; the e=0 case follows from the existing maximizer classification.
Let h be the centered support of K, and maximize

    A(C)-lambda*P(C),
    P(C)=integral_0^pi (h_C(t)-h(t))^2 dt,
    lambda=1/(65536*sqrt(e)),                                 (3)

over right-angle caps in [-100,100]x[0,1]. Continuous dependence of cap/niche
area on this compact family gives a maximizer C. Equivalently use the finite
polygon approximation of the selection proof and pass to a subsequence. Its
recovery polygons converge to K and their penalty tends to zero. Uniform
convergence of the finite area functionals yields the same comparison:

    A(C)-lambda*P(C)>=A(K)=M-e,
    A(C)>=M-e,
    P(C)<=e/lambda.                                          (4)

The convergence proof is the existing compact-cap/finite-niche argument. No
numerical mesh index is required: the inequalities after taking the limit
have the explicit constants displayed in (4), not an unknown convergence rate.

Since e<=10^(-4), P(C)<=65536*e^(3/2)<1. Also A(C)>0, so C has width<9.
Writing m for its horizontal midpoint, the support of its centered copy has
absolute value less than 5. The L2 triangle inequality gives

    |m|*sqrt(pi/2) <= sqrt(P(C))+10*sqrt(pi)<21.

Thus |m|<21, and C has Euclidean radius less than 26. The artificial box is
strictly inactive. The selected polygon caps are also eventually strictly
inside it, so the floating-facet variations used next are legitimate.

Let D=||h_C-h||_infinity on [0,pi]. The support difference is 32-Lipschitz:
the two radii are less than 26 and 5. Also D<32. At a point attaining D, at
least one side of length D/64 fits in [0,pi], and the absolute difference on
that side is at least D/2. Hence

    P(C)>=D^3/256,
    D<=(256*e/lambda)^(1/3)=256*sqrt(e).                       (5)

## 3. Keep the nonzero variation error

Here are the precise quantitative changes to the selected-polygon proof.
For a floating normal on mesh delta, the actual support perturbation is its
sine hat. Over the upper support interval its absolute integral is at most
4delta. If D_n is the sup support difference from the target, differentiation
of the penalty gives

    sigma_n(t)-tau_n(t) <= 8*lambda*D_n*delta.                 (6)

Zero-length facets satisfy the same upper bound without variation. The exact
local geometric estimate from the curvature proof is

    tau_n(t) <= tan(delta)*(|g_n^+(t)-1|+tan(delta/2))
                  +(2*tan(delta/2)-sigma_n(t))_+.

Solving its two cases as in the original proof gives the original curvature
bound plus at most the right side of (6). Smearing atoms over mesh intervals,
using bounded perimeter and almost-everywhere convergence of opposite support
points, and then taking the selected subsequence yields

    rho_C(t)<=k(g_C(t))+eta,
    rho_C(t+pi/2)<=k(f_C(t))+eta,
    eta=8*lambda*D<=1/32,                                    (7)

with k(x)=max(|x-1|,(|x-1|+1)/2). The same estimate includes the endpoint cells,
so no atom survives at 0 or pi. The two upper-half curvature measures are
absolutely continuous. The geometric O(delta^2) errors disappear on summation;
D_n tends to D, while lambda is fixed for the specified e. This is not the
invalid inference that a nearby arbitrary cap already has a curvature density.

## 4. A robust arm bootstrap

Set L=pi/2, m(x)=x-k(x). The cap arms are nonnegative, f(0)=g(L)=1, and (7)
gives

    f(t)>=1+integral_0^t [m(g(s))-eta] ds,
    g(t)>=1+integral_t^L [m(f(s))-eta] ds.

For x>=0, m(x)>=1/2-(3/2)(1-x)_+. Put H=max((1-f)_+,(1-g)_+) over [0,L].
If H>0, H<=1. With a=1/2-eta and B=(3/2)H-a, necessarily B>0 and the same
integral inequalities imply

    (1-f(t))_+<=min(H,Bt),
    (1-g(t))_+<=min(H,B(L-t)).

At a maximum point (reflecting if necessary),

    H<=I=integral_0^L [(3/2)min(H,Br)-a]_+ dr.

The rising part of the integrand has length 2/3 and area B/3. If L<=H/B,
I<=B/3<H. Otherwise I=B(L+1/3)-H. Since L<8/5,

    I-H < (9/10)H-29/30+(29/15)eta
         <=-1/15+(29/15)eta<0,

because eta<=1/32<1/29. Both cases contradict H<=I. Therefore f,g>=1, and
substitution gives the strict bounds

    f(t)>=1+(1/2-eta)t,
    g(t)>=1+(1/2-eta)(L-t).

Together with the curvature densities this gives the three injectivity
conditions, by the same support/inner-corner differentiation as in the original
proof. Also |C|>=A(C)>2.2. Thus C belongs to Ki.

## 5. Recover the specified cap, not a different maximizer

The known centered Ki estimate applies to C and (4):

    d_H(C_c,K_G,c)<=1.001*sqrt(e).

Changing from the raw support difference C-K to their separately centered
copies costs at most a factor two: their midpoint difference is at most D,
as follows from the two endpoint supports. Using (5),

    d_H(K_c,K_G,c)<=2D+1.001*sqrt(e)
                   <=513.001*sqrt(e)<514*sqrt(e).

This proves (1) for the original K. The comparison cap need not be unique,
and its construction does not replace K in the conclusion.

## 6. Original right-angle sofas

For S admitting a right-angle motion, normalize and take its own monotone
envelope U=K minus N(K). Then S subset U, N(K) subset K, and

    0<=M-A(K)<=epsilon,       |U minus S|<=epsilon.

Apply (1), obtaining upper support error delta<=514*sqrt(epsilon). The existing
reference estimates are: clipped roof factor 51/5 with clipping threshold
1/2040000, outer margin 1/5, and interior balls with ratio 100/1051 at scale
1/24. Orthogonal erosion gives G eroded by sqrt(2)*delta subset U.

For epsilon<=10^(-20), delta<=514*10^(-10)<1/2040000. Forward recovery costs
at most (51/5)*delta. In the reverse direction choose

    rho=20*(delta+sqrt(epsilon)),    r=sqrt(2)*delta,
    kappa=100/1051.

It is below 1/24. The key numerical bound is not the stronger and
generally FALSE r<=kappa*rho/2: at delta=514*sqrt(epsilon), the left
side is about 727*sqrt(epsilon) while the right is only about
490*sqrt(epsilon). Instead,

    kappa*rho-r
      =(2000/1051-sqrt(2))*delta+(2000/1051)*sqrt(epsilon)
      >sqrt(epsilon),

since sqrt(2)<3/2<2000/1051. A square of side
kappa*rho-r inside the surviving interior ball is contained in
the eroded reference shape and has area greater than epsilon.
It must meet the original sofa. This is the sharp surviving-ball
recovery lemma used by the Lean draft; no unjustified half-radius
hypothesis is required. This proves both directed distances and

    d_H(S_c,G)<=20*(514+1)*sqrt(epsilon)=10300*sqrt(epsilon).

Unlike the sharper local theorem, this argument needs no local canonical-Q
or terminal-loss certificate for the specified input cap. Those are precisely
the hypotheses whose effective entry is being investigated.

## Scope

Equations (1) and (2) are coarse, effective RIGHT-ANGLE results. They do not yet
exclude incomplete motions with omega<pi/2. The next step must quantify the
remaining-angle reduction rather than silently treating every near-maximizer
as a right-angle sofa. Numerical constants alone do not replace review of the
penalized-polygon limit and robust arm argument above.
