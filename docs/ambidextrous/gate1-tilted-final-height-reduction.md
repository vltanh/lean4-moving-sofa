# The final tilt reduction: every remaining cap has h<1/20

Written proof, independently checked within this research session, October 10, 2026. This combines the
accepted full-triangle estimate with the now accepted global projection
`T>0, n(-C)=0`. It sharpens only the positive-floor loss in the earlier
three-angle proof. No new niche region, stationarity assumption, or angle
discretization is introduced.

The global projection is proved in [RT](gate1-tilted-reflected-tail-and-projection.md).
The sufficient curvature criterion and its earlier high-tilt strip are proved in
[IE](gate1-tilted-initial-floor-energy.md), and the resulting first-unit branch is
excluded by [GF](gate1-tilted-first-wing-exclusion.md).

## 1. Statement and hypotheses

Consider a remaining canonical tilted maximizer. All the already proved
reductions give

    2/3<C<37/50,     0<h<21/100,
    I=[-2C,2C],     J=[-C,C],
    A(-C)=1-h,      A(C)=1,
    n(-C)=0.

Write z=n(C), e_R=A(2C), e_L=A(-2C), and

    H(C)=1-sqrt(1-C^2),
    0<=z<=H(C),
    e_R=1/2+h/4+3z/4,
    e_L=1/2-3h/4-z/4.                                  (FR1)

The endpoint identities are the actual endpoint pressure laws, and n is
the ambient, full continuous-angle positive niche. The accepted
first-good theorem excludes every such maximizer for which the first
regular wing density is at most one. The accepted initial-floor energy
test supplies that conclusion whenever, with d=3C,

    B=-1/2+5h/4+3z/4,
    s_h=sqrt(h(2-h)),
    d^2+B^2<=5,
    d^2+B^2+B(1-h)-d s_h<=4.                            (FR2)

Then every remaining canonical maximizer satisfies

    h<1/20.                                             (FR3)

The proof splits at C=73/100. Below that value (FR2) holds whenever
h>=1/20. Above it, the actual full-triangle upper bound is strictly less
than 41/50, itself below the candidate lower bound for P.

## 2. An exact first-good strip below C=73/100

Suppose

    2/3<C<=73/100,     1/20<=h<=21/100.

The box bound gives H(C)<8/25, since
1-(73/100)^2>(17/25)^2. Therefore

    -1/2+5h/4 <= B <= -13/50+5h/4,
    -7/16 <= B <= 1/400.

The radius condition in (FR2) follows immediately:

    d^2+B^2
      <=(219/100)^2+(7/16)^2
       =798001/160000
       =5-1999/160000 <5.                               (FR4)

Set Q(d,B,h)=d^2+B^2+B(1-h)-d sqrt(h(2-h)). Its derivative in B
on the actual allowed interval obeys

    Q_B=2B+1-h >=3h/2>0.

Its derivative in d is 2d-s_h>0. Thus it is enough to bound

    Q(219/100,-13/50+5h/4,h).

This expression is convex in h. The polynomial part has quadratic
coefficient 5/16, and -sqrt(h(2-h)) is convex. Its maximum on the
displayed interval occurs at an endpoint. At h=1/20 use s_h>31/100;
at h=21/100 use s_h>61/100. These elementary square-root bounds give

    Q(219/100,-79/400,1/20)
      <634973/160000=4-5027/160000,

    Q(219/100,1/400,21/100)
      <553949/160000=4-86051/160000.                      (FR5)

Both conditions (FR2) hold throughout this strip. The accepted general
first-good theorem excludes it.

## 3. The improved full-triangle positive-floor loss

It remains to exclude

    73/100<=C<37/50,     1/20<=h<=21/100.                (FR6)

Use all notation and the exact niche/exterior payments of the accepted
[full-triangle width theorem](gate1-tilted-full-triangle-width-cut.md) (FT4--FT17). In particular set

    a=2C, r=sqrt(2), k=r-1, c=cos(pi/8),
    A_0=1-k, b=2-k, d_0=3r-1,
    gamma=1-r/2, t_0=2c-r.

The subscript on A_0 and d_0 here merely distinguishes these scalar
constants from the roof and from d=3C in (FR2). Let u,v be the lifted
45-degree support parameters, and let

    w_R=a-u,     w_L=a-v+h.

Exactly as in FT9, support containment at the actual endpoints gives
w_R<=1-e_R and w_L<=1-e_L. The stronger endpoint information (FR1)
therefore yields

    w_R<=1/2-h/4,
    w_L<=1/2+3h/4+z/4
        <7/12+3h/4.                                    (FR7)

Here H(C)<1/3 for C<37/50. The exact floor-loss inequality FT13 bounds
the discarded negative-baseline portions by

    gamma[(w_R-t_0)_+^2+(w_L-t_0)_+^2].

Consequently the complete actual-niche estimate becomes

    P<=G_h(a,u,v)+L_asym(h),

    L_asym(h)=gamma[(D-h/4)_+^2+(D+1/12+3h/4)_+^2],
    D=1/2-t_0.                                         (FR8)

G_h is precisely the jointly concave clipped function in FT17; it is
unchanged. Thus this refinement does not replace any actual support
by a surrogate niche and does not drop any clipping term.

For completeness, all geometric range checks in FT4--FT17 still hold
on (FR6), although its left width endpoint is slightly smaller:

* The 45-degree apex has positive height and lies in J, since
  C-h/2-k>=73/100-21/200-k>0 and h<C.
* The endpoint sum E=e_R+e_L>=1-h/2 gives
  M-h/2>=a-1/2-h/4>=363/400>179/200, where M=(u+v)/2.
  This is stronger than the lower bound used for both strict
  crossover inequalities FT11.
* The outer gain-triangle zeros still lie in J: C<37/50<4/5 is
  within the original FT12 range.

The exterior and full niche triangles are therefore exactly the
previously audited disjoint regions. Their Cauchy payment remains
unchanged.

## 4. A support critical point at a=73/50

Write

    a_*=73/50,
    B_0(a)=a-(a-k)^2/2,
    s_0(a)=d_0 a/2-(4c-2).

The completion of squares FT18 shows that the support critical point
at a=a_* is u_*=v_*, with

    u_*=(a_*+k)/2+(b/9)[s_0(a_*)-A_0h/4]+h/4.

It is interior, unclipped, and has S>0 for every h in [1/20,21/100].
Here are direct checks, using the same radical bounds as FT20:

    140/99<r<99/70,     923/1000<c<231/250.

They give 2/3<s_0(a_*)<7/10. Hence
s_0(a_*)-A_0h/4>2/3-(3/5)(21/400)>0. The right clipping
quantity has the form

    -k/2+(b/9)s_0(a_*)+(1/4-b A_0/36)h.

It is strictly smaller than the negative upper bound in FT21, because
s_0(a_*)<71/100 and h<=21/100<17/50. The left clipping
quantity is smaller by h. The lower support bound follows from the
positive bracket, and the strict clipping bound also gives
u_*<a_*/2+k<a_*.

The value at this actual critical point is

    K(a_*,h)=B_0(a_*)-kh/2-h^2/8
             -(2/9)[s_0(a_*)-A_0h/4]^2.                 (FR9)

Its partial derivative in a is

    r-a_*-(2d_0/9)[s_0(a_*)-A_0h/4]<0.

Thus the joint supporting-plane argument FT23--FT24 applies without
change and gives

    G_h(a,u,v)<=K(a_*,h)       for every a>=a_*.          (FR10)

This covers every possible 45-degree clipping pattern in (FR6).

## 5. The scalar bound decreases in h and is below 41/50

On the entire tilt interval in (FR6), the positive parts in (FR8) are
positive. Indeed the displayed radical bounds give

    1/2-2(231/250)+140/99 < D < 239/3500,

and the lower expression is greater than 21/400. We can therefore
expand (FR8) as an ordinary quadratic. The linear coefficient of
K(a_*,h)+L_asym(h) is

    ell=-k/2+A_0 s_0(a_*)/9+gamma(D+1/8).

Using k>2/5, A_0<3/5, gamma<3/10, s_0(a_*)<7/10 and
D<239/3500 yields

    ell<-1/5+(3/5)(7/10)/9
                +(3/10)(239/3500+1/8)<-9/100.

The quadratic coefficient is the same as in FT25:

    q=-1/8-A_0^2/72+5gamma/8<1/16.

The total derivative is therefore less than
-9/100+h/8<=-9/100+21/800<0. The bound is largest at h=1/20.

At that endpoint,

    s_0(a_*)-A_0/80
      >43789/66000>53/80.                               (FR11)

Also D-1/80<7/125 and D+1/12+3/80<19/100, so

    L_asym(1/20)
      <(3/10)[(7/125)^2+(19/100)^2]
       =29427/2500000<3/250.                            (FR12)

Finally B_0(a_*)=(123/50)k-529/5000. Using k<29/70 for its
positive coefficient and k>41/99 for the negative tilt term gives

    P <(123/50)(29/70)-529/5000-41/3960-1/3200
          -(2/9)(53/80)^2+3/250
       =7550393/9240000
       =41/50-26407/9240000 <41/50.                     (FR13)

Thus (FR6) is impossible for a maximizer with P at least the known
candidate value. Together with (FR4)--(FR5), this proves (FR3).

### Provenance of the initial bound h<21/100

The controlling repository note
`docs/ambidextrous/gate1-tilted-initial-floor-energy.md`, IE8, already
contains the following independently audited corollary. On
C<=37/50 and 21/100<=h<=17/50, the box bounds give
-107/400<=B<=69/400. Thus

    d^2+B^2<=(111/50)^2+(107/400)^2
             =799993/160000=5-7/160000<5.

The energy expression Q increases in B because 2B+1-h>=1/8.
At its affine upper endpoint B=-101/400+5h/4 and d=111/50 it is
convex in h. Its upper bounds at h=21/100 and h=17/50 are,
respectively, 17911/5000 and 545121/160000, both less than four;
these use sqrt(h(2-h))>61/100 and >3/4. Hence the general
first-good theorem excludes this whole strip. This is the h<21/100
input in Section 1, and completes its provenance even for a reader
using only the scratch drafts.

The [small-height theorem](gate1-tilted-small-height-exclusion.md) excludes the entire
remaining h<1/20 range. The [Gate 1 closure](gate1-sharp-full-turn-closure.md)
records the full domain coverage. The fixed rational comparisons are reproduced by
[the exact certificate checker](computer-assisted/check_gate1_final_scalar_exact.py).
