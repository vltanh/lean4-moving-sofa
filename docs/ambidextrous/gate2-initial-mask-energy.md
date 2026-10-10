# Gate 2: initial masking energy and the short-width positive-tilt branch

Written proof, independently checked within the research session,
October 10, 2026. This uses the
actual partial spatial objective and the audited PU normalization. It
does not assume either regular wing is unit. Its two conclusions are
an exact sufficient first-unit criterion using the outgoing strip, and
an unconditional first-unit theorem for 1/2<C<=2/3.

## 1. Inputs and exact initial state

Use the positive tilted normalization of
[PU](gate2-positive-tilt-first-unit-exclusion.md):

    I=[-2C,2C], J=[-C,C], C>1/2,
    A(-C)=1-h, A(C)=1, 0<h<1/2,
    3pi/8<=a<pi/2, c=cos(a), s=sin(a),
    top endpoint b=C+T, T>=0.

Let f and g be the actual first support and the left-wing surrogate
second support, and define

    u=f''+f, v=g''+g,
    p=f'-g+1, q=g'+f-1,
    p'=u-1-q, q'=v-1+p.

The finite partial-source selection, its curvature inequalities and
same-sign laws are those proved explicitly in PU Sections 1–2:

    u=0, v<=1/2 on {p>0,q>0},
    v=0, u<=1/2 on {p<0,q<0};
    p<=1, q>=-1, u<=kappa(q), v<=kappa(p)
       after the central switch d0=atan(h/(2C)),
    kappa(x)=max(|x|,(1+|x|)/2).

Before d0 the two regular source densities vanish. The surrogate
p,q are positive through d0; the inequality p<=1 is not assumed
there. The pressure bound is

    e_R>=1/3+h/2+(2/3)N(C)>=1/3+h/2.                (IM1)

Put

    D=3C, B=e_R-1+h, R2=D^2+B^2.

The initial state is p(0)=1+B=e_R+h>0 and q(0)=D-1>0.
Whenever the initial ++ interval has both densities zero,

    p(t)=1+B cos(t)-D sin(t),
    q(t)+1=D cos(t)+B sin(t),
    D_tangent(t)=(-C+sin(t),1-h-cos(t)).             (IM2)

Here D_tangent names a geometric point; the scalar D is 3C.

## 2. The outgoing strip extends the initial zero-density interval

The only possible companion source in the strict ++ regime is its
D tangency. The corner is locally hidden because both wall heights
increase with angle there, and the B tangency is outside its attached
companion halfplane. These are the same local finite neighboring-wall
facts used in the initial-floor argument of Gate 1.

If the D tangency is strictly below the floor or strictly below the
outgoing line, it cannot be an exposed positive source inside J.
If its abscissa is outside J, it is uncharged for that reason. On
compact intervals with either strict height gap, finite-source
localization therefore gives v=0, while the same-sign law already
gives u=0. Equality at a crossing does not affect the almost-everywhere
statement: in the ++ regime v<=1/2 makes both D_y and its outgoing-line
depth strictly increasing at positive t.

During this zero-density interval the two exact depths are

    D_y(t)=1-h-cos(t),
    F_D(t)=D_tangent(t) dot mu_a-(f(a)-1)
          =1-(2C+T)c-hs-sin(a-t).                  (IM3)

Set

    gamma_floor=acos(1-h),
    K=1-(2C+T)c-hs,
    gamma_out=a-asin(max(K,0)),
    gamma=max(gamma_floor,gamma_out).              (IM4)

One has K<s because the initial D point lies strictly below the
outgoing line. Hence gamma_out belongs to (0,a], with gamma_out=a
meaning that F_D never becomes positive before a. Also
gamma_floor<a and gamma_floor>d0. The latter follows from
tan(gamma_floor)>h>h/(2C).

Therefore, on the initial positive-p, positive-q component,

    u=v=0 up to the earlier of gamma and the first p-zero,
    while the initial q-positive component continues.              (IM5)

If q reaches zero earlier, the initial component already causes no
first-source curvature excess; later positive-q components have the
usual 1/8 amplitude bound. To justify IM5 without solving a circular
switch condition, follow the maximal initial interval with u=v=0.
The explicit depths IM3 show that it cannot end while either mask
is still strict. Their first simultaneous positivity is precisely
gamma. A first-exit argument gives the claimed endpoint.

## 3. An exact sufficient first-unit criterion

In the ++ regime the energy

    Epp=(p-1/2)^2+(q+1)^2

satisfies

    Epp'=2(q+1)(v-1/2)<=0.                         (IM6)

Let H(t)=B cos(t)-D sin(t). Its initial value satisfies 1+B>0,
and H(a)<-1, since B<=h<1/2, D>3/2, c<5/13 and s>12/13.
There is exactly one first zero of 1+H(t) on [0,a], and H stays
below -1 after that zero: when B<0 it may turn upward only after
its minimum, but H(pi/2)=-D<-1. Thus the comparison with -1 below
has no return ambiguity.

If the first actual p-zero occurs before gamma, IM2 gives

    (q+1)^2=R2-1

there. If gamma occurs first, IM2 gives
Epp(gamma)=R2+H(gamma)+1/4; then IM6 gives
(q+1)^2<=R2+H(gamma) at the first p-zero. Consequently

    (q_at_first_p_zero+1)^2
       <=R2+max(-1,H(gamma)).                      (IM7)

This proves the following sufficient criterion:

    R2<=5,
    R2+B cos(gamma)-D sin(gamma)<=4
       imply u<=1 a.e. on (0,a).                  (IM8)

Indeed IM7 then gives q<=1 at the first p-zero. Afterwards q strictly
decreases as long as p<0. Every later positive-q component starts
at q=0 with p<=1; while p>0 the inequalities p'<=-1 and
q'<=p-1/2 limit its possible increase to
integral_0^(1/2)(1/2-r)dr=1/8. Once p<0, q decreases. The arm
bound q>=-1 and u<=kappa(q) then give u<=1 everywhere except the
initial ++ portion, where u=0 already. There is no assertion about
the separate first terminal facet atom.

For an explicit formula, if K>=0 let Z=sqrt(1-K^2). Then

    B cos(gamma_out)-D sin(gamma_out)
       =(Bc-Ds) Z+(Bs+Dc) K.                      (IM9)

At the floor crossing the corresponding expression is

    B(1-h)-D sqrt(h(2-h)).                         (IM10)

Use the larger crossing in IM4, or equivalently apply the -1 clipped
version of H to the two crossings and take the smaller value. Thus
IM8 is an exact algebraic/trigonometric criterion using both actual
masks. No finite-angle numerical screen is a hypothesis.

## 4. The short-width first-unit theorem transfers to the partial score

The following argument is unconditional under the input assumptions
when C<=2/3; it does not require checking IM8 separately.

Let d0=atan(h/(2C)), c0=cos(d0), s0=sin(d0), and set b_R=1-e_R.
The first-wall box at the right middle endpoint gives, for every
visited angle and for the terminal wall itself,

    R_t(C)<=1+(C cos(t)-1)/sin(t)
           <=H_C:=1-sqrt(1-C^2).

Since the two-wall minimum is at most R_t,

    0<=N(C)<=H_C.                                 (IM11)

This is the only endpoint niche box bound used here. No analogous
bound on N(-C) is asserted for the partial objective. From the exact
pressure equation and N(-C)>=0,

    b_R=(2-h-3N(C)+N(-C))/4
       >=(3sqrt(1-C^2)-1-h)/4>1/8.                (IM12)

The last comparison uses C<=2/3, h<1/2, and sqrt(5)>2.
Of course b_R<=1. The central switch state is exactly

    p(d0+)=1-b_R c0-C s0,
    q(d0+)+1=C c0-b_R s0+2C/c0.                  (IM13)

These are also the continuous traces of the surrogate p,q used above.
The final term records the actual uncharged central-facet jump when
one derives IM13 with the actual second support. From IM1,

    p(d0+)=c0(e_R-h/2)+(1-c0)>=c0/3+(1-c0)>0.     (IM14)

This replaces the reflected niche estimate that was available for
Gate 1 but is not valid for the partial objective.

Direct expansion of IM13 gives

    Epp(d0+)=9C^2+1/4+T0(b_R),
    T0(b)=b^2-b(c0+2h)+h^2-hc0/2.                (IM15)

Here c0>4/5 and 1-c0<5h/4. The function T0 is convex in b. On
the enlarged interval b in [1/8,1], its endpoint values satisfy

    T0(1/8)<=-27/320-3h/20<0,
    T0(1)<=-13h/20<0.                             (IM16)

For the first bound use h^2<=h/2 and c0>=4/5. For the second also
use 1-c0<=5h/4. Therefore

    Epp(d0+)<9C^2+1/4<=17/4.                      (IM17)

If the positive-q component reaches a p-zero, IM6 and IM17 force
q<1 there. If it ends earlier, u=0 on its whole positive-p part.
All later positive-q components have amplitude at most 1/8 as above.
The partial arm/curvature law therefore gives

    1/2<C<=2/3 ==> u<=1 a.e. on (0,a).             (IM18)

Combining IM18 with the independently audited PU1 theorem excludes
every positive tilted selected joint maximizer in

    1/2<C<=2/3, 3pi/8<=a<pi/2, 0<h<1/2.          (IM19)

The whole terminal facet remains counted by PS and is bounded by
PU's angle variation; IM18 neither removes that atom nor bounds its
curvature by a Lebesgue density. Horizontal and negative tilts, lower
angles, wider caps and failure of IM8 lie outside this note's scope.
Gate 2 is not a conclusion of this lemma alone; the full argument is
assembled in [the Gate 2 closure](gate2-sharp-partial-turn-closure.md).
