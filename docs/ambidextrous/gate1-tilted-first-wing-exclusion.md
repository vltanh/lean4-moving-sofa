# Every remaining first-good tilted spatial maximizer is excluded

Written theorem, independently checked within the research session, October 10, 2026. This excludes a tilted maximizer whenever its first regular wing has curvature at most one, with arbitrary bounded companion folds. The finite-source occupation proof is expanded in the
[independent source audit](gate1-tilted-folded-source-occupations.md).

## 1. Statement and genuine global inputs

Let U be the selected canonical positively tilted global maximizer for the
actual spatial one-cap score P, normalized by

    I=[-2C,2C], J=[-C,C], A(-C)=1-epsilon, A(C)=1,
    1/2<C<4/5, 0<epsilon<1/2,
    top=[C,b], T=b-C, eR=A(2C), eL=A(-2C).

Assume the established positive endpoint-pressure and regularity theorems,
and assume the first regular wing density satisfies 0<=u<=1. Then U cannot
be a global maximizer. No bound v<=1 on the companion wing is assumed.

Use the actual first support f and the low-left-wing surrogate g. With
L=pi/2, mu=(cos t,sin t), nu=(-sin t,cos t), put

    u=f''+f, v=g''+g,
    p=f'-g+1, q=g'+f-1,
    c=(f-1)mu+(g-1)nu, B=c+p nu, D=c-q mu.

Their endpoint data and kinematics are

    f(0)=g(L)=2C, f(L)=1, g(0)=1-epsilon,
    f'(0)=eR, f'(L)=-b, g'(0)=C, g'(L)=-eL,
    p'=u-1-q, q'=v-1+p,
    B'=(u-1)nu, D'=(1-v)mu,
    B(0)=(2C-1,eR), B(L)=(b,0),
    D(0)=(-C,-epsilon), D(L)=(1-2C,eL).              (GF.1)

The surrogate differs from the actual companion only by an additional
high-top-point wall whose height is nonpositive everywhere on J. Thus
positive niche contacts on J are unchanged. Before the central switch
delta=atan(epsilon/(2C)), both regular densities vanish.

We use the [two-unit theorem TU](gate1-tilted-unit-wing-exclusion.md), the
[first-wing structural lemmas](gate1-tilted-first-wing-structure.md), the
[regularity and sharp arm bounds RG/AR](gate1-spatial-maximizer-wing-curvature-regularity.md),
and the [endpoint/source identities EP](gate1-global-endpoint-complementarity.md). In particular, the last source identities concern limits of
finite exposed-source measures. They do not assert convergence of ordinary
niche arclength at zero height.

If v<=1 a.e., TU already gives the contradiction. If T=0, the audited
first-bad-entry transfer gives v<=1. We may therefore assume

    T>0 and v>1 on a set of positive measure.

The general first-good positive-interval and no-ghost projection theorem,
which does not require monotonicity of D, gives

    {x:n_U(x)>0}=(x_zero,b),
    x_zero=-C+T, n_U(-C)=0.                              (GF.2)

For reference, write the two proper-angle inner wall heights as

    R_t(x)=(f(t)-1-x cos t)/sin t,
    S_t(x)=(g(t)-1+x sin t)/cos t
          =tan t [x-L0(t)],
    L0(t)=(1-g(t))/sin t.

The same positive-interval theorem identifies x_zero with the global
minimum of L0. Also x_zero<1-2C. The actual endpoint pressures are

    eR=1/2+epsilon/4+3z/4,
    eL=1/2-3epsilon/4-z/4, z=n_U(C).                    (GF.3)

## 2. Ordered contact signs and the first bad entry

Let tau be the first entry into {p<-1,q>0}. Before tau, the generic arm
bound and same-sign shadowing give v<=1 a.e. The source-box estimate TU.8,
which needs only the first unit bound, says that p<0 whenever B_x>=C.
If beta denotes the crossing B_x=C, it also gives

    beta>=acos C, sin beta>=3/5, cot beta<=4/3.          (GF.4)

Let alpha be the p-zero on the positive-q component leading to tau. Past
second-unit curvature and global first-unit curvature give strict positive
corner visibility from alpha to tau. Before beta its B tangencies are also
charged. The same argument as in the structural addendum proves
alpha<beta<tau and the first-source lower bounds

    u>=(1+q)/2 on (alpha,beta),
    u>=q on (beta,tau).

The core lies in J there: before tau, D_x is nondecreasing from -C, while
c_x decreases from B_x(alpha)<C. Its height satisfies
c_y=B_y-p cos t>0. In particular q(alpha)<=1 because u<=1.

On (alpha,beta) use

    E=(p-1)^2+(q+1)^2, E'<=0, E(alpha)<=5.

On (beta,tau) use

    K=q+(p-1)^2/4,
    K'=v-1+p+(p-1)(u-1-q)/2
       <=v+(p-1)/2<=0.

At tau, p=-1, so

    1+q(tau)<=K(beta)
       <=1+q(beta)/2-q(beta)^2/4<=5/4.                  (GF.5)

Thus q(tau)<=1/4. A later positive-q component has q<=1/8 by AR7, so its
entry energy is less than 4; the same E/K comparison prohibits a bad
entry there. Consequently the nonunit branch has the ordered signs

    (++): (0,alpha), (-+): (alpha,eta), (--): (eta,L),
    alpha<beta<tau<eta.                                 (GF.6)

The initial positive state remains valid for epsilon<1/2: the positive
pressure side bounds give eR>=2/5, and before delta one has
p(t)>=eR-epsilon/2>3/20, while q(delta)>=3C-1-delta>0.
After beta, p<0 and the arm inequality gives q'<=-1/2. Hence every later
bad point has q<=1/4.

## 3. Fractional source occupations, without a floor-shape assumption

Retain the selected finite source measures jointly in angle and graph
position. Their sin/cos weighted x-marginal is Lebesgue measure on the
finite positive graph projection. The no-ghost projection in GF.2 gives
the limiting weighted x-marginal exactly on (x_zero,C). Thus there is no
residual floor mass. The independent occupation audit gives the following
local disintegration; its proof is recalled to specify its scope.

At a regular positive active point, the max/min first-order condition
places the contact at B(t), D(t), or c(t). Endpoint-angle mass vanishes by
EP.22. The global first unit bound makes B the full first-wall envelope.
On the core it has strict companion slack, so its complete charged
contribution is (1-u)dt on (alpha,beta). Its negative-slope graph lies to
the right of every core corner, because c_x is strictly decreasing from
B_x(alpha).

On a measurable actual corner contact set, the identity n_U(c_x)=c_y and
the level-set chain rule identify the graph tangent a.e. Any competing D
tangent has that same graph tangent. Subtracting its parallel vector flux
and resolving the residual in the two independent wall-ray directions
gives the common ratio q:(-p). The joint horizontal projection bound limits
the remaining occupation to one. Thus one measurable chi in [0,1] gives
the two corner source densities q chi and -p chi.

A positive visible D tangent must have v<=1; if v>1 its second wall has
an angular local minimum with strict first-wall slack. Its remaining
source density is (1-v)d for one measurable d in [0,1], with d=0 wherever
v>1 or D_y<0. Flat projected arcs have no residual measure because the
weighted projection is already exact. Fractions allow arbitrary ties and
measurable contact sets; no finite contact chart is assumed.

All positive core corners and positive D points are inside J. Indeed
S_t(x)>0 implies x>L0(t)>=x_zero>-C. The core's upper bound is
c_x<=B_x(alpha)<C, while D_x=x_g+sin t<=1-C<C. Thus neither family has
an additional positive piece beyond J. One may equivalently set its
occupation to zero outside J; this yields the same equations.

The local first-order classification exhausts the limiting graph pieces;
the exact joint projection rules out any nonnegative residual. EP then
identifies the angular marginals with u dt and v dt. The exact equations
are

    (++): u=0, v=(1-v)d;
    core: u=(1-u)b_flag+q chi,
          v=(1-v)d-p chi;
    (--): u=v=0,
    b_flag=1_(t<beta) on the core.                       (GF.7)

In particular

    u=(b_flag+q chi)/(1+b_flag),
    v=(d-p chi)/(1+d).                                  (GF.8)

The strict visibility already used in Section 2 gives chi=1 before tau.
These source equations do not require D_y to have a unique zero, or D_x
to be monotone.

## 4. The first floor crossing precedes every bad episode

Let gamma be the first zero of D_y. It exists because D_y(0)=-epsilon
and D_y(eta)=c_y(eta)>0. We claim

    gamma<tau.                                          (GF.9)

Suppose D_y has not become positive by tau. While its initial nonpositive
interval persists, L0'=D_y/sin^2 t<=0. At any positive core corner c(t),
write x=c_x(t), y=c_y(t)>0. For every proper earlier angle r<t,

    L0(r)>=L0(t),
    S_r(x)=tan r [x-L0(r)]
           <tan t [x-L0(t)]=S_t(x)=y.

This remains true if the bracket at r is negative. Actual extra high-point
walls are nonpositive on J, so they do not affect the strict inequality
at y>0. For every later angle r>t,

    partial_r R_r(x)=(x-B_x(r))/sin^2 r<0,

because B_x is nondecreasing and x<B_x(t). Thus the current corner is
globally unique and fully exposed: chi=1. Its position is in J by the
argument in Section 3. The same conclusion applies at an isolated first
zero of D_y and extends as long as D_y stays nonpositive.

After tau, while this condition persists, d=0 and b_flag=0. Equations
GF.7 therefore give

    u=q, v=-p, p'=q'=-1,
    D_y'=(1+p)sin t<0.

Consequently D_y cannot leave the nonpositive region; p remains below -1
and q reaches zero while the same strict visibility argument continues.
This contradicts D_y(eta)=c_y(eta)>0.

At the boundary case D_y(tau)=0, justify the initial continuation before
invoking that argument. The corner at tau is positive and in the interior
of J, and p(tau)=-1, q(tau)>0. Its remote-angle gaps are strict; on a
compact set of remote angles they are uniform. The two local wall-angle
derivatives have opposite strict signs, p/sin t<0 and q/cos t>0, so the
current corner remains the unique maximum against nearby angles as well.
Continuity therefore preserves strict corner localization on a
neighborhood of tau, giving chi=1 there. Since b_flag=0, we have u=q and
p'=-1 immediately to the right. For p<-1, equation GF.8 then gives
v=(d-p)/(1+d)>1; the D visibility condition forces d=0. Consequently
D_y'=(1+p)sin t<0, excluding an immediate positive departure from zero.
The preceding continuation argument now applies. This proves GF.9,
including its boundary case and any harmless zero plateaus.

Define the first-floor abscissa

    S=C+D_x(gamma).

Unlike T, this is not assumed to be the global minimum baseline abscissa.
At D_y(gamma)=0 we have L0(gamma)=D_x(gamma), hence

    S>=C+x_zero=T>0,
    S<=1, T<=C.                                         (GF.10)

The bound S<=1 follows from x_g<=-C and D_x=x_g+sin gamma. Integrating
GF.1 gives the exact initial-floor and right-window moments

    S=integral_0^gamma(1-v)cos t,
    epsilon=integral_0^gamma(1-v)sin t,
    T=integral_beta^L(1-u)sin t,
    z=integral_beta^L(1-u)cos t.                         (GF.11)

Here v<=1 on [0,gamma] by GF.9. Later floor recrossings are allowed.

## 5. Every later fold has a paid curvature budget

On (tau,eta), equations GF.8 give

    p'=q chi-1-q<=-1.

Thus p<=-1 throughout that interval, and 0<q<=1/4. For w=q-p, direct
substitution yields

    w'=(1-chi)[p+q+d/(1+d)]
                +chi*d*(1+p)/(1+d)<=0.

Since w(tau)<=5/4, we obtain v<=-p<=5/4-q there. Before tau, v<=1;
after eta, v=0. In particular v<=5/4 globally. Where v>1, d=0 and
v=-p chi, u=q chi, so

    (v-1)_+<=1/4-q<=(1-u)/4.                            (GF.12)

This estimate pays actual excess curvature even if its D image goes below
the floor. It does not assert that every fold stays above zero.

## 6. Calibrated energy with the entire fold defect retained

Use the continuous energy

    (++): H=(p-1/2)^2+(q+1)^2+3/4;
    core: H=(p-1)^2+(q+1)^2;
    (--): H=(p-1)^2+(q+1/2)^2+3/4.

Before beta the source equations and chi=1 give
H'=-(q+1)(1-v)(1-d). On the core after beta put

    G=(1-p)(1-u)-(q+1)(1-v)(1-d).

The exact fractional residual is

    H'-G=(1-chi)(p+q).                                  (GF.13)

It vanishes before tau and is nonpositive afterwards because p+q<=-3/4.
On the final sector H'=1-p. Therefore

    H(L)-H(0)
      <=I_B-integral_0^eta(q+1)(1-v)(1-d),
    I_B=integral_beta^L(1-p)(1-u).                       (GF.14)

On [0,gamma], d=0, giving the exact initial contribution
I_D=integral_0^gamma(q+1)(1-v). Beyond gamma, all pieces with v<=1 are
favorable. Every remaining piece is covered by GF.12 and q<=1/4:

    integral_(v>1)(q+1)(v-1)(1-d)
       <=(5/16)integral_beta^L(1-u)
       <=5T/(16 sin beta).

Thus

    H(L)-H(0)<=I_B-I_D+5T/(16 sin beta).                 (GF.15)

## 7. The first-floor displacement improves the contradiction

The exact endpoint algebra and harmonic support reconstructions give

    H(L)-H(0)=6CT+T^2-(epsilon+z)(epsilon+z/2),
    I_D=3CS-S^2/2+eR epsilon+epsilon^2/2+R_D,
    I_B=3CT+T^2/2+eL z-z^2/2+R_B,                      (GF.16)

where

    R_D=integral_0^gamma(1-v(t))
                       integral_0^t u(s)sin(t-s)ds dt>=0,
    R_B=integral_beta^L(1-u(t))
                       integral_t^L v(s)sin(s-t)ds dt.

For clarity, the I_D identity uses the two initial moments S and epsilon,
not T and epsilon. It follows directly by writing
q+1=3C cos t+(eR-1+epsilon)sin t
plus the u-sine and v-cosine convolutions. Replacing v by 1-(1-v) in
the latter makes its self-interaction (S^2+epsilon^2)/2.

Insert the actual pressures GF.3 into GF.15. The resulting inequality is

    6CT <= (z-epsilon)(2-epsilon-z)/4+R_B-R_D
           +(S-T)[(S+T)/2-3C]+5T/(16 sin beta).          (GF.17)

The new displacement term is nonpositive: S>=T and
(S+T)/2<=(1+C)/2<3C for C>1/2. Thus the first floor need not attain the
global minimum. Any later lower minimum only strengthens the estimate.

Finally GF.4, GF.11 and v<=5/4 give

    z<=cot beta T<=4T/3,
    R_B<=(5/4)[(1-sin beta)/sin beta]T<=5T/6.

Since epsilon+z<2 and R_D>=0, GF.17 implies

    6CT<=z/2+R_B+5T/(16 sin beta)
         <=(2/3+5/6+25/48)T=97T/48<3T.

This contradicts C>1/2 and T>0.

**Conclusion.** Every selected tilted global maximizer in the stated
range whose first wing is unit-bounded is excluded, including arbitrary
bounded nonunit companion folds, arbitrary measurable ties, and later
returns of the companion tangency below the baseline. No lower side-height
condition, unique floor crossing, or companion unit bound is needed.

Combining this theorem with [CH7](gate1-spatial-maximizer-curvature-and-horizontal-value.md) excludes all remaining tilted widths C<=2/3. Combining it with the independently checked [initial-floor criterion](gate1-tilted-initial-floor-energy.md) also excludes 2/3<C<=18/25 with 3/100<=epsilon<17/50. Neither combination settles all larger tilted widths.
