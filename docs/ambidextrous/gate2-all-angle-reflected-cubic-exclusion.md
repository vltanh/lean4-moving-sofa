# Gate 2: a reflected curvature envelope pays the complete terminal range

Written mathematical proof, October 10, 2026. This note
supplies the weighted early-excess bound in MP.7 on the entire remaining
angle interval cot(a)>=1/8. The complementary cot(a)<=1/8 interval is
covered by RX.14 and MP.8. All three signs of the affine middle roof
are included.

The inputs are the all-width angle cut
[AT](gate2-all-width-terminal-angle-exclusion.md), the all-angle width
bound [WC](gate2-three-angle-width-cut.md), the canonical saturated
tail data and terminal bounds
[TP](gate2-terminal-facet-and-prefix-reduction.md), the fixed-angle
finite-source theorem [PS](gate2-partial-endpoint-source-and-green.md),
the local support laws rederived in
[PU](gate2-positive-tilt-first-unit-exclusion.md), and the weighted
companion support comparison
[MP](gate2-companion-moment-prefix-exclusion.md).
The complementary curvature theorem is
[RX](gate2-reflected-tail-cot-one-eighth.md), while the exact reflected
impulse calculation is in
[RP](gate2-small-deficit-companion-prefix.md).
No reflected partial objective, two-unit-wing assumption, terminal
first-moment law, or full-turn completion is introduced.

## 1. Domain and all-sign endpoint parameters

For an above-reference largest-angle partial-cap maximum, AT and WC
leave

    1/2<C<37/50,
    1/8<=kappa:=cot(a)<3/8,
    c=cos(a), s=sin(a), epsilon=L-a=atan(kappa), L=pi/2.       (AC1)

Let k=(1-s)/c=tan(epsilon/2). Then

    c<3/8, s>14/15, k<2/11, epsilon<9/25.                    (AC2)

For s, use s>8/sqrt(73)>14/15; after squaring, the latter is
14400>14308. For k, its endpoint value is (sqrt(73)-8)/3<2/11,
since 73<(94/11)^2. Finally
atan(3/8)<3/8-(3/8)^3/3+(3/8)^5/5<9/25;
the last rational margin is 897/819200. The integral inequality
1/(1+x^2)<=1-x^2+x^4 proves the displayed arctangent bound.

Use I=[-2C,2C], J=[-C,C]. Write H=1-h_R for the right middle
height, and D_H=(1-Hs)/c. TP.10--11 give

    m<=c-D_H<=sk, T_L+2T_R<=D_H,
    H>s, min(h_L,h_R)=0.                                      (AC3)

The negative tilt already completed by NT has been discarded. For
positive or horizontal middle H=1 and D_H=k, so T_R<=k/2.
For negative middle T_R=0 and 0<h_R<1-s<1/15.

Let N_-=N(-C), N_+=N(C) be the actual partial barrier endpoints,
including the outgoing wall. The ordinary visited niche has the box
bound H_0(C)=1-sqrt(1-C^2)<1/3 at both endpoints. Thus

    N_-<=max(H_0(C), R_a(-C)),
    R_a(-C)=kappa(2C+T_R-D_H).                                (AC4)

This is not an assumption that the outgoing wall obeys the ordinary
niche box.

### Positive or horizontal middle

The endpoint pressure law gives

    e:=e_L=1/2-3h_L/4+(3N_--N_+)/4<=1/2+3N_-/4.

AC3 implies

    R_a(-C)<=kappa(2C-k/2)
      =2C kappa-(sqrt(1+kappa^2)-1)/2.

This expression increases with both C and kappa: its kappa derivative
is 2C-kappa/(2sqrt(1+kappa^2))>0. At their enlarged endpoints it
is less than

    111/200-(sqrt(73)-8)/16
      <111/200-1/32=419/800,

using sqrt(73)>17/2. Since H_0(C)<1/3<419/800, we obtain

    0<=e<2857/3200<179/200,
    d:=3C+T_R<111/50+1/11=1271/550<2311/1000.               (AC5)

The last rational margin is 1/11000.

### Negative middle

Here the reflected initial pressure is e=e_L+h_R. From PS's endpoint
law,

    e=1/2+5h_R/4+(3N_--N_+)/4.

AC4 gives N_-<=max(H_0(C),2C kappa)<111/200. Therefore

    0<=e<1/2+1/12+333/800=2399/2400<1,
    d:=3C<111/50.                                           (AC6)

All cases have d>3/2. These estimates use the actual partial endpoint
pressures and the explicit outgoing wall. In particular AC5's
improvement over e<1 is paid by the top projection bound.

## 2. The reflected local system and the one terminal impulse

Use the left charged-wing surrogate when the middle tilts upward.
For a downward tilt, remove the unused first central-facet atom by
using the right-wing first-support surrogate. It equals the actual
first support on every visited angle. The harmonic unused tails are
then exactly those in RP.2 and RP.8, and the initial reflected values
are (P,Q)=(e,d-1), with AC5 or AC6.

More explicitly, if p=f'-g+1 and q=g'+f-1, reflect only the local
support equations:

    P(r)=-q(L-r), Q(r)=-p(L-r),
    U(r)=v(L-r), V(r)=u(L-r),
    P'=U-1-Q, Q'=V-1+P.                                     (AC7)

On the regular reflected used interval the finite-source arm laws are

    P<=1, Q>=-1,
    U<=max(|Q|,(1+|Q|)/2),
    V<=max(|P|,(1+|P|)/2).

On the ++ sector U=0,V<=1/2; on the -- sector V=0,U<=1/2.
These are the actual local PS/PU source laws; no stationarity of a
reflected objective is claimed.

Every positive-Q component after the initial one has amplitude at
most 1/8. Indeed it starts at Q=0 with P<=1. While P>0, the ++
laws give P'<=-1 and Q'<=P-1/2. The total positive increase of Q
is therefore at most the integral of 1/2-r over [0,1/2], namely
1/8. Once P<=1/2 the derivative Q' is nonpositive, and once P<=0
the arm bounds make it strictly negative. P cannot rise again while
Q>0. Thus these later components cannot support U>1.

Both densities vanish on 0<r<epsilon. At epsilon there is one
impulse, in the second reflected density, of size

    j=m/s<=k.

Consequently P is continuous and Q jumps upward by j. PS excludes
all subsequent used-angle atoms, including a companion terminal atom.
The unvisited negative central atom has been removed, and in the
positive case the final removed-central interval has U=V=0 directly.
No arm bound for that final surrogate interval is needed.

The free initial trajectory is

    P(r)=1+(e-1)cos r-d sin r,
    Q(r)+1=d cos r+(e-1)sin r.                              (AC8)

The initial Q-positive component persists across the full unused gap:

    Q(epsilon-)+1=ds-(1-e)c
      >(3/2)(14/15)-3/8=41/40>1.                           (AC9)

The impulse is upward, so it preserves this positivity. Also
P'=(1-e)sin r-d cos r<0 throughout the unused gap, since
(1-e)tan r<=tan r<3/8<d. A P-zero there therefore cannot return
to positivity before the impulse; this makes the two entry cases in
Section 4 exhaustive.

For E=(P-1/2)^2+(Q+1)^2 the exact RP impulse calculation gives

    E(epsilon+)-E(0)
      <=k^2[(2e-1+k^2)/(1+k^2)-dc]
      <=k^2<4/121<1/30.                                   (AC10)

Here e<=1, so the bracket is at most one. If the first P-zero occurs
after epsilon, E is nonincreasing in the preceding initial ++ sector,
where E'=2(Q+1)(V-1/2)<=0. If P is already nonpositive at epsilon,
then (P-1/2)^2>=1/4 directly. In both cases, at the beginning r_b
of the possible excess comparison,

    Q(r_b)+1<=sqrt(Z),
    Z=d^2-e(1-e)+1/30.                                     (AC11)

If the initial Q-positive component ends before P reaches zero, it
has U=0 throughout and supports no first-source excess. All later
positive-Q components are too small to support U>1. Thus only the
case covered by AC11 remains.

## 3. Universal decay and the resulting linear excess envelope

After P<=0, as long as Q>1, the curvature bounds give P'<=-1.
With rho=r-r_b>=0, this implies P<=-rho. For rho<=1,

    Q'<=-1/2-rho/2.

When P is in [-1,0], use V<=(1-P)/2. When P<-1, the stronger
bound V<=-P gives Q'<=-1, which implies the displayed estimate
for rho<=1. Therefore

    Q(r)-1<=sqrt(Z)-2-rho/2-rho^2/4.                       (AC12)

Once Q falls to at most one within this component, P remains
nonpositive: on 0<Q<=1 the arm bound gives P'<=-(1+Q)/2, while
P<=0 gives Q'<=-1/2. Thus Q cannot re-enter Q>1 before the
component ends; AC12 is controlling its only possible excess episode.

Put

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.

Every possible excess ends by r_b+D(Z), provided this time increment
is less than one. The following common bound closes that condition:

    Z<(58/25)^2,
    D(Z)<13/25.                                             (AC13)

Indeed e(1-e)>=0 and AC5--6 give
Z<(2311/1000)^2+1/30<(58/25)^2, with squared margin
25037/3000000. The duration comparison follows from
(38/25)^2-(4(58/25)-7)=19/625>0.

If Z<=4 there is no excess. Otherwise D=D(Z)>0 and the polynomial
in AC12 factors as

    sqrt(Z)-2-rho/2-rho^2/4
      =(D-rho)(1/2+(D+rho)/4).

For 0<=rho<=D, its second factor is at most (1+D)/2<19/25.
Since U-1<=Q-1 wherever U>1, we get

    (U(r)-1)_+ <= (19/25)(r_b+D-r)_+                     (AC14)

throughout the possible excess episode. All other components have no
excess. It remains to bound the episode endpoint uniformly.

## 4. Every possible episode ends before 91/100

### 4.1 The first P-zero precedes the impulse

In this case take r_b=epsilon. AC2 and AC13 yield

    r_b+D<9/25+13/25=22/25<91/100.                         (AC15)

This also handles a zero exactly at epsilon. No smooth transition
through the terminal atom is being assumed.

### 4.2 The first P-zero follows the impulse

While P>0 and Q>0, the same-sign law gives U=0. Since Q'>=-1
and the terminal jump is upward,

    Q(r)>=d-1-r,
    P(r)<=e-dr+r^2/2.

If Q ends its component earlier there is no relevant excess.
Otherwise its first P-zero obeys

    r_b<=tau(d,e):=d-sqrt(d^2-2e).                          (AC16)

The square root is real on our whole parameter domain since d>3/2
and e<=1. Consequently

    r_b+D<=W_+(d,e):=tau(d,e)+D(Z).                        (AC17)

We only need to control AC17 when Z>4. Put

    A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7).

For the unclipped expression W on Z>4,

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                                  (AC18)

Both derivatives are strictly positive for 0<=e<=1 on this domain.
For W_e, when e<1/2 observe
S^2-A^2=e+e^2+1/30>0 and Q0>=1. Thus Q0 S>A and the negative
term has magnitude less than 1/A. For e>=1/2 positivity is immediate.

For W_d, Z>4 implies d^2>119/30. Hence

    d/A<sqrt(119/59)<3/2.

Also S<7/3, Q0<sqrt(7/3)<31/20, and d>3/2. Therefore

    W_d>-1/2+180/217>0.                                    (AC19)

The clipped W_+ remains increasing in e across Z=4, since below
that level it is tau(d,e), which increases in e. Raise e to its
orientation-specific upper endpoint in AC5 or AC6. If this places Z
at or below four, its endpoint value is less than 3/5: indeed the
original Z>4 fixes d^2>119/30, and

    tau(d,e)<=tau(d,1)<3/5.

The last comparison is equivalent to d>59/30, which follows from
d^2>119/30>(59/30)^2. Otherwise increase d to its corresponding
upper endpoint while remaining in Z>4, using AC19. It is therefore
enough to check the two following rational endpoint pairs.

**Positive or horizontal:** d=2311/1000, e=179/200. Then

    tau<107/250, sqrt(Z)<2299/1000, D<241/500.              (AC20)

The three squared margins, respectively, are

    2d(107/250)-(107/250)^2-179/100=629/125000,
    (2299/1000)^2-Z=3193/600000,
    (741/500)^2-(4(2299/1000)-7)=81/250000.

All are positive. Thus W_+<107/250+241/500=91/100.

**Negative:** d=111/50, e=1. Then

    tau<51/100, sqrt(Z)<223/100, D<39/100.                  (AC21)

The squared margins are respectively 43/10000, 67/6000, and
121/10000. Thus W_+<9/10<91/100.

Combining AC15--21 with AC14 proves the global reflected envelope

    (U(r)-1)_+ <=(19/25)(91/100-r)_+                      (AC22)

on the used interval. Its support is contained in r<91/100. The
final removed-positive-central interval has U=0, so the same envelope
holds there without appealing to the surrogate arm bounds.

## 5. The weighted cubic payment

MP defines

    theta=asin(C-T_L), lambda=tan(theta),
    E_theta=int_0^theta (v(t)-1)_+(lambda cos t-sin t) dt.

By AC3, 0<C-T_L<=C<37/50. In particular

    cos(theta)>sqrt(1-(37/50)^2)>2/3.                       (AC23)

Also cos(147/200)>37/50. The standard Taylor lower bound
cos x>=1-x^2/2+x^4/25 on [0,1] proves this with exact rational
margin 62448881/40000000000. Therefore

    acos(C-T_L)>=acos C>147/200.

Let t_0=L-91/100. Under t=L-r, AC22 becomes

    (v(t)-1)_+ <=(19/25)(t-t_0)_+.

Moreover

    theta-t_0<91/100-147/200=7/40.                         (AC24)

If theta<=t_0, the weighted excess is zero. Otherwise the exact
kernel identity and sin x<=x give

    lambda cos t-sin t
      =sin(theta-t)/cos(theta)
      <=(theta-t)/cos(theta).

Integrating the product of the two linear factors,

    E_theta
      <=(19/25)/cos(theta) * (theta-t_0)^3/6
      <(19/25)/(6(2/3))*(7/40)^3
      =6517/6400000.                                       (AC25)

This is the full reason only a small early curvature excess must be
paid: the excess envelope and the weighted support kernel both vanish
at opposite ends of the relevant interval.

Finally kappa>=1/8 implies

    c>=1/sqrt(65)>3/25.

Consequently MP's allowed error satisfies

    39c/4400>117/110000>6517/6400000.                       (AC26)

The last rational margin is 3193/70400000. Thus AC25 establishes
MP.7, and the terminal occupation contradiction excludes every
remaining maximum in AC1.

## 6. Coverage and scope

For cot(a)<=1/8, the independently proved RX.14 supplies
v<=1 on [0,asin C], so MP.8 applies with zero weighted excess.
For cot(a)>=1/8, AC1--26 supply MP.7 with the strict cubic payment.
AT has already excluded cot(a)>=3/8. The full-turn endpoint a=L
is bounded by the Gate 1 theorem. Hence, given the established
canonical/attainment, source, width, and MP inputs stated at the start,
there is no above-reference joint partial-cap maximizer at any angle.

This is a proof of the universal partial spatial inequality through
that explicitly listed dependency chain. Passing the original-motion
Gate 2 additionally uses the exact two-cap spatial partition from the
Gate 2 signed-domain reduction; no new motion-completion assumption
is needed for that final implication.
