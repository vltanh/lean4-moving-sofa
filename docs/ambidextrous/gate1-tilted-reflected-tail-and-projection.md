# A reflected terminal-unit estimate forces positive top overhang

Written proof, independently checked within this research session, October 10, 2026. This applies to every remaining
canonical tilted spatial global maximizer with

    2/3<=C<37/50, 0<h<17/50,
    I=[-2C,2C], J=[-C,C], A(-C)=1-h, A(C)=1,
    top=[C,b], T=b-C>=0.

Neither full regular wing is assumed unit-bounded. The inputs are the
established regularity/arm/source bounds, positive endpoint pressures,
the exact box estimate H(C)<1/3, and the EP finite source projection.

The dependencies are the [endpoint source identities](gate1-global-endpoint-complementarity.md),
[spatial regularity and arm bounds](gate1-spatial-maximizer-curvature-and-horizontal-value.md),
[positive pressures](gate1-global-positive-pressure-and-wing-identity.md),
[first-wing structural notation](gate1-tilted-first-wing-structure.md), and
[forward excess estimate](gate1-tilted-first-excess-ends-early.md).

The conclusion is

    T>0, n_U(-C)=0,
    T=C+x_zero,

where x_zero is the unique zero of the low-wing second-wall envelope.

## 1. The global middle projection requires no unit-curvature hypothesis

Use the first support f and low-left-wing surrogate g from the tilted
notes, and put L=pi/2. Their proper-angle inner walls are

    R_t(x)=(f(t)-1-x cos t)/sin t,
    S_t(x)=(g(t)-1+x sin t)/cos t.

On J, the actual extra high-top-point second wall is nonpositive. Thus
positive niche agrees with the surrogate construction on J.

Let x1=1-2C and F(x)=sup_(0<t<L) S_t(x). Exactly as in the first-good
structural addendum, the support of the low wing gives F finite, convex
and nondecreasing for x<x1. Its endpoint-angle limits are -h at t=0 and
minus infinity at t=L. It is negative for x<=-2C, and its limiting
t=L value at x1 is eL>0. Hence it has a unique zero x_zero<x1, with
strictly negative values to the left and strictly positive values to the
right. Uniqueness follows because a zero is attained at an interior
angle whose affine wall has strictly positive slope.

The pinned high point (C,1) gives f(t)>=C cos t+sin t. Consequently, for
every x<=x1 and every proper angle,

    f(t)-1-x cos t
       >=(3C-1)cos t+sin t-1
       >=cos t+sin t-1>0.                              (RT.1)

Thus every first wall is positive on x<=x1. For x1<x<C, angles approaching
L also give positive niche, because b>=C>x and

    R_t(x)=(b-x)(L-t)+o(L-t)>0,
    S_t(x)->+infinity.

It follows that the exact positive projection in the interior of J is

    {x in (-C,C):n_U(x)>0}
       =(max(-C,x_zero),C).                            (RT.2)

There is no claim about the full positive interval to the right of J;
first-wing excess may produce additional exterior leakage there.

On a compact interval inside J and strictly left of x_zero, all surrogate
second walls are uniformly negative. The extra high-point wall is also
strictly negative when its angle is bounded away from zero. Thus finite
positive graph on that compact interval can use only arbitrarily small
endpoint-angle neighborhoods. EP.22 makes their total source mass and
horizontal projection O(angle cutoff)+o_n(1). On compact subsets of the
positive interval RT.2, uniform convergence supplies the converse bound.

The exact EP horizontal moment therefore gives

    2C-T=integral_0^L(u sin t+v cos t)dt
         =lim_n |{x in J_n:n_n(x)>0}|
         =C-max(-C,x_zero).

Equivalently,

    T=(C+x_zero)_+.                                    (RT.3)

This proof uses no unit bound on u or v. In particular, T>0 will imply
x_zero>-C and n_U(-C)=0. It remains to rule out T=0.

## 2. Reflected arm variables when T=0

Assume T=0, so b=C. Reflect the parameter by r=L-t and define

    p_tilde(r)=-q(t), q_tilde(r)=-p(t),
    u_tilde(r)=v(t), v_tilde(r)=u(t), d=3C.

Before the reflected central normal, these obey the same equations and
sharp spatial arm estimates as the original pair:

    p_tilde'=u_tilde-1-q_tilde,
    q_tilde'=v_tilde-1+p_tilde,
    p_tilde(0)=eL, q_tilde(0)=d-1.                    (RT.4)

After the reflected central normal, the first density u_tilde=v is
identically zero because it comes from the low-wing surrogate's initial
point-supported interval. Thus an excess estimate only needs to cover
the initial regular interval; any terminal central atom is harmless.

Write e=eL. The actual endpoint law and the box bounds give

    e=1/2-3h/4+(3n_- -n_+)/4,
    3/20<1/2-3(17/50)/4-1/12<e<3/4.                 (RT.5)

The displayed middle rational equals 97/600, which exceeds 3/20. The
upper bound follows from n_-<1/3 and h,n_+>=0.

As in the forward excess estimate, every possible u_tilde>1 belongs to
the initial positive-q_tilde component after its first p_tilde=0 time
alpha. If there is no such crossing before the terminal central normal,
there is no excess. Later positive components have q_tilde<=1/8 and do
not generate excess.

On the initial (++), u_tilde=0, v_tilde<=1/2, and the energy
(p_tilde-1/2)^2+(q_tilde+1)^2 is nonincreasing. At alpha it gives

    (q_tilde(alpha)+1)^2<=d^2-e(1-e).                  (RT.6)

Also q_tilde'>=-1 and p_tilde'<=-d+r before alpha. Therefore

    alpha<=d-sqrt(d^2-2e).                            (RT.7)

The bound applies unless the positive component ends or the terminal
central normal arrives first, either of which removes any prospective
excess. Its right side decreases with d and increases with e.

Put eta_ex=(q_tilde(alpha)-1)_+. The universal quadratic arm envelope is

    (u_tilde(alpha+s)-1)_+
        <=[eta_ex-s/2-s^2/4]_+,

so when eta_ex<3/4 all excess ends within

    ell(eta_ex)=sqrt(1+4 eta_ex)-1                     (RT.8)

of alpha. This is the same pointwise envelope as ET3-ET4.

## 3. An exact two-case bound for the reflected excess end time

First suppose e<=2/3. From e>=3/20 and e<=2/3,
e(1-e)>=51/400. Using d<111/50 in RT.6 gives

    (q_tilde(alpha)+1)^2
       <(111/50)^2-51/400=48009/10000<(11/5)^2.

Hence eta_ex<1/5 and ell<7/20, since 9/5<(27/20)^2. Equation RT.7 gives

    alpha<=2-sqrt(8/3)<3/8,
    alpha+ell<3/8+7/20=29/40<11/15.                  (RT.9)

The radical comparison for alpha is 8/3>(13/8)^2.

Now suppose 2/3<=e<3/4. Here e(1-e)>=3/16. Therefore

    (q_tilde(alpha)+1)^2
       <(111/50)^2-3/16=47409/10000<(109/50)^2.

Thus eta_ex<9/50 and ell<5/16, since 43/25<(21/16)^2. Also

    alpha<=2-sqrt(5/2)<21/50,
    alpha+ell<21/50+5/16=293/400<11/15.               (RT.10)

The radical comparison here is 5/2>(79/50)^2. These are all exact rational
comparisons. The two cases prove

    u_tilde(r)<=1 for a.e. r>=11/15,
    v(t)<=1 whenever L-t>=11/15.                     (RT.11)

The already checked alternating cosine estimate gives

    cos(11/15)>37/50,
    11/15<acos C.                                    (RT.12)

## 4. The zero-overhang hypothesis makes the low endpoint strictly dry

Suppose F(-C)>=0. Since S_t(-C)->-h at t=0 and tends to minus infinity
at t=L (because C<1), its nonnegative maximum is attained at a proper
angle t. Regularity of g gives the stationary equation

    0=partial_t S_t(-C)=(-C-D_x(t))/cos^2 t,
    D_x(t)=-C.

If X is the horizontal coordinate of the supporting low-wing point,
D_x=X+sin t and X>=-2C. Consequently sin t<=C, or

    L-t>=acos C>11/15.

By RT.11, the entire original prefix [0,t] has v<=1. The exact support
formula from g(0)=1-h and g'(0)=C is

    g(t)=(1-h)cos t+C sin t
              +integral_0^t v(s)sin(t-s)ds.

It follows that

    S_t(-C)
       =1-h-sec t+(1/cos t)integral_0^t v(s)sin(t-s)ds
       <=1-h-sec t+(1-cos t)/cos t=-h<0.

This contradicts the assumed nonnegative maximum. Therefore F(-C)<0,
so x_zero>-C. But RT.3 with T=0 requires x_zero<=-C. The contradiction
excludes zero top overhang.

**Conclusion.** Every remaining tilted global maximizer with
2/3<=C<37/50 has T>0, x_zero=-C+T, and n_U(-C)=0, without requiring
either entire wing to have unit curvature.

## 5. Two exact support-point bounds for the overhang

The left outer endpoint (-2C,eL) lies in the cap, so
g(t)>=2C sin t+eL cos t. At the proper angle
cos t=eL, sin t=sqrt(1-eL^2), its second wall at
x=-2C+sqrt(1-eL^2) is nonnegative. This x is strictly below x1,
where F has its unique zero. Hence

    T<=sqrt(1-eL^2)-C.                                (RT.13)

In particular T>0 implies eL<sqrt(1-C^2).

The pinned low point (-C,1-h) gives instead
g(t)>=C sin t+(1-h)cos t. At cos t=1-h and
sin t=sqrt(h(2-h)), its second wall is nonnegative at
x=-C+sqrt(h(2-h)). If this x is below x1, the same zero comparison
applies; if it is at or above x1, x_zero<x1 gives the comparison
directly. Therefore

    T<=sqrt(h(2-h)).                                  (RT.14)

Combining these with x_zero<x1 gives the convenient summary

    0<T<=min{sqrt(h(2-h)),sqrt(1-eL^2)-C},
    T<1-C.                                           (RT.15)

These are pure support-point comparisons; they require no curvature or
visibility statement beyond the already established projection formula.
Together with the independently proved forward terminal-unit bound
z=n_U(C)<=lambda T, lambda=C/sqrt(1-C^2), they give

    z<=lambda sqrt(h(2-h)),
    (C+z/lambda)^2+(1/2-3h/4-z/4)^2<=1.              (RT.16)

The second inequality follows from RT.13 and the actual pressure law
eL=1/2-3h/4-z/4; all quantities before squaring are nonnegative.

This is a dependency of the [completed Gate 1 proof](gate1-sharp-full-turn-closure.md).
The written argument has not been externally refereed or formalized in Lean.
