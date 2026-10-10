# Gate 2: the reflected curvature tail through cot(a) <= 1/8

Written mathematical proof, October 10, 2026. This extends the
[small-deficit reflected estimate](gate2-small-deficit-companion-prefix.md)
(RP) and proves `v<=1` on `[0,asin(C)]` whenever `cot(a)<=1/8`.
The [weighted companion comparison](gate2-companion-moment-prefix-exclusion.md)
(MP) uses only `[0,asin(C-T_L)]`, making this local curvature theorem
sufficient for that angle range.

The inputs are the all-sign tail data, terminal facet bound, top
projection, ordinary endpoint boxes, and width cut in
[TP.1–13](gate2-terminal-facet-and-prefix-reduction.md), together
with the reflected local source laws and exact terminal impulse
identity in RP.6–16. No objective reflection invariance is used.
The curvature theorem is established here; the global exclusion uses
the separately proved geometric implication MP.7–8.

## 1. Parameters and exact impulse bound

Suppose a remaining above-reference largest-angle partial maximum
has

    0<cot(a)<=1/8.

Set c=cos(a), s=sin(a), epsilon=L-a, k=(1-s)/c. TP gives

    1/2<C<37/50, N(-C)<1/3,
    m/s<=k, T_R<=k/2.

Moreover

    epsilon<=atan(1/8)<1/8,
    k=(sqrt(1+cot(a)^2)-1)/cot(a)<1/16.       (RX1)

At the endpoint cot(a)=1/8, k=sqrt(65)-8<1/16;
monotonicity of k in the angle deficit proves the general bound.

The reflection is exactly RP's:

    P=-q(L-r), Q=-p(L-r), U=v(L-r), V=u(L-r),
    P'=U-1-Q, Q'=V-1+P.

On the used interval P<=1, Q>=-1 and the usual curvature/same-sign
inequalities hold. Both densities vanish before epsilon. At epsilon
only Q jumps, upward by j=m/s<=k. There are no further atoms in the
used interval. The unused central facet is removed in the negative
case, as in RP.

The initial values are (P,Q)=(e,d-1), with

    0<=e<3/4, d=3C+T_R<1801/800  (positive/horizontal),
    0<=e<19/25, d=3C<=111/50     (negative).       (RX2)

Here d>3/2. For the negative case, e=e_L+h_R and
h_R<1-s<1/125. Indeed s>=8/sqrt(65)>124/125; the last
squared margin is 112/203125. The endpoint pressure bound then gives
e<3/4+5h_R/4<19/25. In the other cases e=e_L<3/4.
The initial Q-positive component persists through this enlarged gap:

    Q(epsilon-)+1=ds-(1-e)c
      >(3/2)(124/125)-1/8>1.

The upward terminal impulse preserves that positivity.

For E=(P-1/2)^2+(Q+1)^2, the exact impulse calculation gives

    E(epsilon+)-E(0)
      <= k^2[(2e-1+k^2)/(1+k^2)-dc]
      <(53/100)k^2<1/480.                       (RX3)

The penultimate inequality uses e<=19/25 and k<1/16. Thus the
parameter controlling Q at the first P-zero, or at epsilon when
P has already become nonpositive, is

    Z=d^2-e(1-e)+1/480.                          (RX4)

Precisely, Q+1<=sqrt(Z). If P has already crossed zero in the
unused gap, this follows from (P-1/2)^2>=1/4 at epsilon.
Otherwise E is nonincreasing on the subsequent initial ++ sector.

As in RP, every positive-Q component after the initial one has
amplitude at most 1/8 and cannot support U>1. Within the initial
component, once P<=0 and Q>1, the universal decay is

    P<=-rho,
    Q-1<=sqrt(Z)-2-rho/2-rho^2/4,               (RX5)

for elapsed rho<=1. The possible excess duration is consequently

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.

All bounds below are less than one, making the comparison valid up
to its predicted endpoint.

## 2. Small initial P, including an earlier zero in the unused gap

Suppose e<=3/10. If Z<=4, there is no possible excess after the
initial P-zero or the impulse. Before that zero U=0; the unused gap
also has U=0. Thus there is no excess to estimate in this case.

If Z>4, then d^2>4-1/480, whence

    d>1999/1000.                                (RX6)

The squared margin is 5747/3000000. While P>0 and Q>0,
Q'>=-1 and the impulse is upward, so

    P(r)<=e-dr+r^2/2.

The first P-zero occurs by

    tau<=d-sqrt(d^2-2e)<4/25.                    (RX7)

The final inequality follows from e<=3/10, RX6, and

    2(1999/1000)(4/25)-(4/25)^2-3/5=44/3125>0.

The Q-component cannot end first on this interval, since
Q>=d-1-r>0. If P has crossed before epsilon, start RX5 at epsilon;
RX1 still places this start before 4/25.

Uniformly over RX2,

    Z<(451/200)^2,
    sqrt(Z)-2<51/200,
    D(Z)<17/40.

For the first bound the worst value is d=1801/800 and e(1-e)>=0;
the exact margin is 5689/384000. The last comparison uses
1+4(51/200)=101/50<(57/40)^2. Therefore all possible excess for
e<=3/10 has ended before

    4/25+17/40=117/200<18/25.                   (RX8)

This case does not require a positive lower side-pressure bound.

## 3. Larger initial P and two exact endpoint certificates

Suppose e>=3/10. At the impulse,

    P(epsilon)=1-(1-e)s-dc>=e-dc
      >3/10-(1801/800)/8>0.

Thus the first P-zero follows epsilon. If the initial Q-component
ends earlier, it has no first-density excess. Otherwise its crossing
time satisfies

    tau<=d-sqrt(d^2-2e),
    last_excess_time<=W_+(d,e),
    W_+(d,e)=d-sqrt(d^2-2e)+D(Z).                (RX9)

Here Z is RX4. If Z<=4, no excess follows the crossing. If Z>4,
then d>2, since e(1-e)>=114/625>1/480 in this parameter range.

On Z>4 set A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7). The
unclipped W has derivatives

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                         (RX10)

Both are positive on 3/10<=e<=19/25 and 2<=d<=1801/800.
For W_e, the negative term when e<1/2 is at most 1/5 in absolute
value, whereas 1/A>=1/d>11/25. For W_d use d/A<4/3,
S<sqrt(5)<9/4 and Q0<sqrt(2)<3/2 to obtain
W_d>-1/3+32/27>0. Here S<sqrt(5) uses
Z<=d^2-114/625+1/480<5; the endpoint d^2 alone need not be below
five.

The clipped W_+ is increasing in e across Z=4: below that level
it is the increasing function d-sqrt(d^2-2e). If increasing e to
its upper endpoint places Z below 4, this endpoint value is at most
2-sqrt(4-38/25)<9/20. Otherwise increase d to its upper endpoint,
remaining in Z>4. It is therefore enough to check the following
pairs separately.

### Positive or horizontal pair

At d=1801/800 and e=3/4,

    d-sqrt(d^2-2e)<109/300,
    Z<(221/100)^2,
    D(Z)<107/300.                               (RX11)

The first squared margin is 1403/360000. The second margin is
2669/1920000. Finally 4(221/100)-7=46/25 and
(407/300)^2-46/25=49/90000>0. Thus

    W_+<109/300+107/300=18/25.

### Negative pair

At d=111/50 and e=19/25,

    d-sqrt(d^2-2e)<3/8,
    Z<(109/50)^2,
    D(Z)<5/16.                                  (RX12)

The middle margin is 259/60000. The first and last comparisons
are the same elementary squared inequalities as RP.21. Thus
W_+<11/16<18/25.

Together RX8, RX11, and RX12 prove

    U(r)<=1 a.e. for r>=18/25 on the used interval.              (RX13)

In the positive-tilt final surrogate interval the source density is
zero directly, so this conclusion includes that interval too.

## 4. Consequence for the original companion support

The Taylor lower bound cos x>=1-x^2/2+x^4/25 on [0,1] gives

    cos(18/25)>37/50.

Its exact rational margin is 225577/19531250. Since C<37/50,

    acos(C)>18/25.

If t<=asin(C), then r=L-t>=acos(C)>18/25. Therefore

    v(t)<=1 a.e. on [0,asin(C)].                  (RX14)

In particular this holds on [0,asin(C-T_L)] whenever C-T_L>=0.
TP's top projection gives T_L<=D_H<c<1/8<C, so the latter angle
is well defined in every present orientation.

This proves the complete local curvature premise needed by the
weighted second-wall comparison through cot(a)<=1/8. The global
exclusion uses that separately stated geometric comparison; the
present note does not infer a full barrier from these local ODEs.
