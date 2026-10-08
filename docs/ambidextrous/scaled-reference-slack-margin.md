# An analytic slack margin for the scaled-reference family

**Scope.** The supplied minimum-width-frame package observed numerically that its reference-scale family has a negative slack correction of order s^(3/2). The hand proof below gives an explicit function and a rationally specified parameter range. It covers the full canonical saturation of a scaled reference hull, not just the smaller homothetic copy of the actual reference sofa. It does not cover arbitrary minimum-width competitors or close unrestricted full-turn optimality. Labels SM are local.

Attribution: the minimum-width slack identity and the numerical family motivating this calculation come from the user-supplied package reviewed in `minimum-width-package-review.md`. Reference inputs are the explicit cap and its circular end phases, also written in TC.1, and its known open-quarter curvature densities in [0,1]. The upper bound on a regular cap uses the existing written SR/AF comparison; WV's maximizing-cap selection/exposure chain and Gerver's theorem are not needed for this restricted result. These dependencies and the new argument remain subject to independent review.

## 1. The actual feasible family and its minimum-width frame

Use the centered reference hull K_* and sofa Sigma, with projection [-m,m], top and bottom faces [-m/2,m/2], and

$$m=1/(3\sin\beta),\qquad \beta=\arctan Y,\qquad 4Y^3+3Y-1=0,$$

$$2/7<Y<3/10,\qquad 0\le\rho_*\le1\text{ on each open quarter}.$$

Fix 0<=s<=1/64, put k=1-s, and set

$$K_s=kK_*+(0,s),\qquad E_s=E_{full}(K_s).$$

Uniform scaling by k<=1 preserves all canonical hallway depth inequalities: each support depth is multiplied by k. Thus k Sigma+(0,s) has both original full turns and is contained in E_s. Its convex hull is K_s, so E_s has this same actual hull. Its fibers are nonempty intervals because the retained scaled reference projects onto the entire interval; indeed its middle horizontal segment survives. Hence E_s is compact, connected, and genuinely full-turn feasible. No mere sampled fiber test is used.

Its projection is I_s=[-km,km], with width W=2km. Its vertical span is exactly k, between y=s and y=1. The hull contains the rectangle [-km/2,km/2] times [s,1]. Since m>1, the width of that rectangle in any nonvertical normal exceeds k, whereas the vertical width of K_s equals k. Therefore this is a global minimum-width orientation of the actual hull, without having to locate a numerical minimum.

Let U_s be the downward cap of K_s, with roof

$$A_s(x)=s+kA_*(x/k).$$

The reflection (x,y)->(x,1+s-y) leaves K_s invariant, so both caps in the slack identity are U_s. Write n_s for their common full positive niche roof. The top face of U_s is J_s=[-b_s,b_s], with b_s=km/2 and length km=W/2.

## 2. Niche confinement follows from unit curvature

On the upper semicircle,

$$h_s(t)=k h_*(t)+s\sin t,$$

so its open-quarter curvature densities are k rho_* in [0,1]. Let f=h_s(t), g=h_s(t+L), L=pi/2. The single-wall tangency heights satisfy

$$B_y'=(f''+f-1)\cos t\le0,\quad B_y(L)=0,$$

$$D_y'=(1-g''-g)\sin t\ge0,\quad D_y(0)=0.$$

Consequently both are nonnegative. The first baseline intercept (f-1)/cos t is nondecreasing with terminal value b_s; the second (1-g)/sin t is nondecreasing with initial value -b_s. Every positive niche point therefore has

$$\boxed{-b_s<x<b_s.} \tag{SM.1}$$

All niche material is under the common top face; outside J_s its positive roof is zero. On J_s the actual hull's floor and roof are respectively s and 1. The slack correction from the supplied MW identity is therefore exactly

$$G_s=2\int_{J_s}\min(n_s(x),s)\,dx-sW$$

$$\boxed{G_s=-2\int_{J_s}(s-n_s(x))_+\,dx\le0.} \tag{SM.2}$$

The identity |J_s|=W/2 is essential here. No footprint assertion for an arbitrary cap is being inferred from the reference's value.

## 3. A proved circular upper bound near each niche endpoint

Put R=1-k/2=(1+s)/2. The reference's final first-quarter support is 1/2+(m/2)cos t+(1/2)sin t for L-beta<=t<=L. Hence the scaled cap satisfies exactly

$$f(t)-1=b_s\cos t+R(\sin t-1).$$

Its first inner-wall tangency is

$$B_t=(b_s-R\cos t,\ R-R\sin t).$$

For fixed x the first inner-wall height is

$$F_t(x)=(f(t)-1-x\cos t)/\sin t,$$

with derivative

$$\partial_t F_t(x)=(x-(B_t)_x)/\sin^2t.$$

The tangency abscissa (B_t)_x is nondecreasing over the whole quarter, since its derivative is (1-rho_f)sin t>=0. Thus whenever x=b_s-d with 0<d<R sin beta, its global first-wall supremum is attained at t=L-arcsin(d/R) in the displayed end phase. The two-wall niche is at most this single-wall supremum. Therefore

$$\boxed{0\le n_s(b_s-d)\le R-\sqrt{R^2-d^2}.} \tag{SM.3}$$

Reflection in x gives the same upper bound at -b_s+d. No claim about which wall is active for an unknown modified cap is used; global first-wall monotonicity proves the inequality for this cap.

The range needed next is d<=sqrt(s). It is valid throughout 0<s<=1/64: sqrt(s)<=1/8, while

$$R\sin\beta\ge\tfrac12\sin\beta>1/8.$$

The last strict inequality follows from Y>2/7, since sin beta>2/sqrt(53)>1/4. The two endpoint intervals of length sqrt(s) are disjoint: Y<3/10 gives m>10/9, and k>=63/64 gives km>35/32>2sqrt(s). These are explicit inequalities, not a sufficiently-small parameter left unspecified.

## 4. Exact integrated margin

The circular bound reaches height s at d=sqrt(s), because

$$R^2-s=(1-s)^2/4.$$

Insert the two disjoint endpoint intervals into SM.2. This gives

$$-G_s\ge4\int_0^{\sqrt{s}}\left[s-R+\sqrt{R^2-d^2}\right]dd=:\Gamma(s).$$

Elementary integration, using arcsin(2sqrt(s)/(1+s))=2 arctan(sqrt(s)) for 0<=s<1, yields

$$\boxed{\Gamma(s)=(1+s)^2\arctan\sqrt{s}-(1-s)\sqrt{s}.} \tag{SM.4}$$

With x=sqrt(s), the bound arctan x>=x-x^3/3 gives

$$\Gamma(s)\ge\frac83s^{3/2}+\frac13s^{5/2}(1-s)\ge\frac83s^{3/2}.$$

In particular Gamma(s)>0 for s>0, and its expansion is

$$\Gamma(s)=\frac83s^{3/2}+\frac8{15}s^{5/2}+O(s^{7/2}).$$

This proves the negative sign and three-halves exponent analytically, not by fitting a power law to the package's numerical table.

## 5. Ordinary-area conclusion and its dependencies

The two caps have the same signed value, and the true slack identity is

$$|E_s|=2\Psi(U_s)+G_s.$$

Since the cap has height one, global open-quarter density at most one, and width W=2km>2, the existing regular-cap signed-roof identity SR1 and adaptive calibration AF3 give Psi(U_s)<=M/2. This is the same admitted regular-cap comparison used in CT Section 5, not a claim of weighted maximality for U_s. One could alternatively use the existing written WV2 bound, but it is unnecessary here.

Writing Delta_s=M/2-Psi(U_s)>=0, we obtain:

**Theorem SM1.** For every 0<=s<=1/64, the actual connected full canonical envelope E_s of K_s=(1-s)K_*+(0,s) satisfies

$$\boxed{|E_s|\le M-2\Delta_s-\Gamma(s)\le M-\frac83s^{3/2}.} \tag{SM.5}$$

At s=0 this is the exact reference equality. At positive s it gives a strict ordinary-area bound for the entire saturation, whose area can be substantially larger than the obvious scaled feasible subset (1-s)Sigma+(0,s).

No global asymmetry or angle-completion hypothesis is discharged by this theorem. It covers precisely the scalar reference-scale hull family motivating the minimum-width package and makes its observed favorable slab term a proved quantity. General minimum-width bodies can have unequal or point faces, positive above-slab clipping, and niche footprints not summing to W.

## 6. Relation to the partial-turn margin

The earlier CC theorem charges lambda(e)=tan(e/2)-e/2 for a missing angle e. That quantity is cubic in e; Gamma(s) starts at (8/3)s^(3/2). It is tempting to compare these orders, but a bridge between a general partial-turn hull and this precise scaled-reference family has not been proved. Neither e proportional to s nor identical admissible coordinates can be inserted by convention.

A rigorous application to a particular partial hull would require both a proved relation to the present E_s and payment of its actual completion allowance (including empty-fiber/component bookkeeping). The differing exponents alone do not close partial turns.

This is a pen-and-paper result, with a small rational/arithmetic checker recorded separately. No long search, CI, Lean/Lake compilation, dependency installation, or manuscript build is used. The current general full-turn value and the remaining partial-turn margin are still unproved.