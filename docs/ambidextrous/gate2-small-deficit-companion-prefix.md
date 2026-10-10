# Gate 2: a unit companion prefix at small terminal deficit

Written mathematical proof, October 10, 2026. The theorem below
excludes every above-reference partial-cap maximum with
`0<cos(a)<=1/25`, covering positive, horizontal, and the remaining
negative middle tilt. The inputs are the canonical domain reductions
[PD](gate2-partial-cap-domain-reductions.md), the fixed-angle source
and endpoint laws [PS](gate2-partial-endpoint-source-and-green.md),
the local support inequalities in
[PU](gate2-positive-tilt-first-unit-exclusion.md), and the all-sign
terminal bounds [TP](gate2-terminal-facet-and-prefix-reduction.md).
The reflection exchanges only the local support equations; it does
not assert reflection invariance of the partial spatial objective.

For reviewability, Section 1 lists the exact modular hypotheses.
TP supplies all of them for an above-reference largest-angle
maximizer with `0<cos(a)<=1/25`. This proves that entire terminal
angle branch, while Gate 2 still requires the remaining angles.

## 1. Geometric hypotheses for the three middle orientations

Use I=[-2C,2C], J=[-C,C], and assume

    1/2<C<=37/50, 0<c=cos(a)<=1/25,
    s=sin(a), epsilon=pi/2-a=asin(c),
    k=(1-s)/c=c/(1+s), w=sk<c/2.                  (RP1)

Suppose the cap is a canonical saturated joint maximizer, so the
fixed-angle PS source and endpoint laws apply. The terminal first
facet has horizontal length m. The first harmonic unused tail is
supported at (b,H), where the following alternatives cover the
middle signs:

* Positive tilt: b=C+T_R, H=1, g is the low left-wing surrogate,
  with g(0)=1-h and g'(0)=C. Here 0<h<1/2.
* Horizontal middle: b=C+T_R, H=1, the left top overhang is T_L,
  and g(0)=1, g'(0)=C+T_L.
* Remaining negative tilt: b=C, H=1-h, with 0<h<1-s. Replace the
  actual first support by its right-wing surrogate. Its unused
  tail is supported at (C,1-h), removing the central-facet atom
  that lies in the unused arc. On all visited angles the surrogate
  equals the actual first support. Here g(0)=1 and
  g'(0)=C+T_L.

All three have the companion unused tail

    g(t)=2C sin(t)+e_L cos(t), a<t<pi/2.           (RP2)

There is no companion terminal atom. Put

    D_H=(1-Hs)/c, m_max=c-D_H=s(H-s)/c.

Assume the exact terminal consequences

    0<=m<=m_max<=w,
    T_L+2T_R<=D_H.                               (RP3)

These are TP.10–11 for all three signs. For positive tilt they
also occur as PU.16–17, with T_L=0 and D_H=k. The present proof
uses these exact terminal bounds rather than assuming a terminal
first moment.

Finally suppose the ordinary box estimate holds for the partial
barrier at the left middle endpoint:

    N(-C)<=H_C=1-sqrt(1-C^2)<1/3.                 (RP4)

TP.12 supplies this estimate, because c<=1/25 implies cot(a)<1/8;
TP.13 supplies C<37/50. The comparison with 1/3 uses
(37/50)^2<5/9. Only this upper bound, not a lower endpoint pressure
estimate, is needed below.

The first conclusion is

    v=g''+g<=1 a.e. on [0,asin(C+w)].              (RP5)

The second conclusion is a contradiction with terminal source mass.
Thus RP1–RP4, with the standard local partial-source laws, exclude
all three orientations. For the claimed small-deficit branch these
are all established prerequisites. Any extension to larger c must
recheck the displayed parameter bounds and quantitative certificate.

## 2. Reflection of the support system and the terminal impulse

Write L=pi/2. On regular used angles use

    p=f'-g+1, q=g'+f-1,
    p'=u-1-q, q'=v-1+p.

At r=L-t set

    P(r)=-q(L-r), Q(r)=-p(L-r),
    U(r)=v(L-r), V(r)=u(L-r).

Then

    P'=U-1-Q, Q'=V-1+P.                           (RP6)

The arm, curvature and same-sign local source inequalities become

    P<=1, Q>=-1, U<=kappa(Q), V<=kappa(P),
    U=0, V<=1/2 on {P>0,Q>0},
    V=0, U<=1/2 on {P<0,Q<0}.                    (RP7)

They hold on the reflected used interval. In the positive-tilt case,
the final interval beyond the removed central switch has U=V=0
directly, so no arm inequality is asserted for the surrogate there.
The horizontal and negative cases have no removed atom in the
visited interval.

The initial data in the two relevant cases are

    (P(0),Q(0))=(e,d-1),
    e=e_L, d=3C+T_R               (positive/horizontal),
    e=e_L+h, d=3C                (negative).      (RP8)

Both densities vanish on (0,epsilon). At epsilon there is just one
impulse in the second reflected density, of size

    j=m/s<=k.

Thus P is continuous and Q jumps upward by j. There are no further
atoms on the reflected used interval. In particular the unused
negative-tilt central facet has already been removed from f; keeping
it would give the wrong initial height and an extra spurious impulse.

The endpoint pressure and RP4 bound the initial parameters. For
positive tilt,

    e_L=1/2-3h/4+(3N(-C)-N(C))/4<3/4.

The horizontal case has h=0. For negative tilt,

    e=e_L+h=1/2+5h/4+(3N(-C)-N(C))/4
      <3/4+5/4000<19/25,

because h<1-s=c^2/(1+s)<1/1000. No positive lower bound on e is
needed beyond e>=0. From RP1–RP3,

    k<21/1000, epsilon<41/1000,
    3/2<d<2231/1000, 0<=e<3/4   (positive/horizontal),
    3/2<d<=111/50,  0<=e<19/25  (negative).       (RP9)

For k use s>99/100, so k<4/199<21/1000. For epsilon, sin(41/1000)
>=41/1000-(41/1000)^3/6>1/25. Also T_R<=k/2, proving the stated
d bound.

The free initial trajectory is

    P(r)=1+(e-1)cos(r)-d sin(r),
    Q(r)+1=d cos(r)+(e-1)sin(r).                  (RP10)

Throughout this short initial gap Q>0: its terminal value satisfies
Q(epsilon-)+1=ds-(1-e)c>(3/2)(99/100)-1/25>1.

## 3. Exact energy paid by the terminal impulse

Let E=(P-1/2)^2+(Q+1)^2. At r=0,
E_0=(e-1/2)^2+d^2. Direct expansion of RP10 and the Q impulse gives

    E(epsilon+)-E_0
      =(1-e)(1-s)-dc+2j[ds-(1-e)c]+j^2.           (RP11)

The bracket ds-(1-e)c is positive, so the right side increases with
j>=0. At j=k it simplifies exactly to

    k^2[(2e-1+k^2)/(1+k^2)-dc].                   (RP12)

Since e<=19/25 and k<21/1000, this is less than

    (53/100)k^2<1/4000.

Therefore

    E(epsilon+)<=E_0+1/4000.                     (RP13)

This estimate is valid even when P has already become negative in
the unused initial gap. It is an exact impulse calculation, not a
smooth-angle approximation.

In the reflected ++ region after the impulse, RP7 gives

    E'=2(Q+1)(V-1/2)<=0.                          (RP14)

Whenever the first P-zero occurs after the impulse, RP13–14 imply

    Q_at_P_zero+1<=sqrt(Z),
    Z=d^2-e(1-e)+1/4000.                         (RP15)

If P is already nonpositive at the impulse, the same inequality
holds there: (P-1/2)^2>=1/4. The component still has Q>0 at the
impulse, by RP10.

## 4. Duration of a possible reflected first-source excess

Any U>1 requires Q>1, except the other possibility Q<-1 which is
excluded by the arm bound. In the ++ regime U=0. Every positive-Q
component after the initial one has amplitude at most 1/8 by the
same-sign propagation argument, so it cannot contain U>1.

After P has become nonpositive, on the remaining part of the initial
component with Q>1,

    P'<=-1.

Starting at P<=0 and writing rho for elapsed time, P<=-rho. For
rho<=1, RP7 gives

    Q'<=-1/2-rho/2.

When P lies in [-1,0] this is V<=(1-P)/2; if P<-1, the stronger
bound V<=-P gives Q'<=-1. Thus RP15 implies that every possible
remaining excess has ended by elapsed time

    D(Z)=sqrt(1+4 max(sqrt(Z)-2,0))-1.            (RP16)

This is zero for Z<=4 and equals sqrt(4sqrt(Z)-7)-1 for Z>4,
provided the displayed time is less than one. All bounds below
are much smaller than one and therefore close the comparison
without a circular time assumption.

### 4.1 Small initial P needs no lower endpoint estimate

Suppose e<=1/4. As long as P>0 in the initial component,
Q'>=-1 and the terminal jump is upward. Since U=0 there,

    Q(r)>=d-1-r,
    P(r)<=e-dr+r^2/2.

Thus its first P-zero is no later than

    tau<=d-sqrt(d^2-2e)<1/5.                     (RP17)

The last inequality uses d>3/2 and e<=1/4. The component cannot
end through Q=0 earlier, because Q>d-1-1/5>0 on this interval.
If the P-zero occurs before the impulse, start the excess comparison
at epsilon instead; there was no curvature during the unused gap.
In either case the comparison starts by max(tau,epsilon)<1/5.

For e<=1/4, RP9 gives Z<5, hence sqrt(Z)<9/4 and
D(Z)<sqrt(2)-1<5/12. Therefore every reflected excess ends before

    1/5+5/12=37/60<7/10.                         (RP18)

This handles all arbitrarily small positive e as well as the limiting
case e=0. It removes any need for an h-dependent lower bound on e_L.

### 4.2 Larger initial P: two exact endpoint certificates

Now e>=1/4. At the impulse,

    P(epsilon)=1-(1-e)s-dc>=e-dc>0.

Hence the first P-zero follows the impulse and satisfies RP17's
time formula, without its final numerical bound. If Q reaches zero
first, no initial excess occurs. Otherwise combine RP15–16 to obtain

    last_excess_time<=W_+(d,e),
    W_+(d,e)=d-sqrt(d^2-2e)+D(Z).                 (RP19)

If d<=2, then Z<4 on 1/4<=e<=19/25, so there is no excess after
the P-zero. It remains to bound RP19 for d>2 and Z>4.

On Z>4 put A=sqrt(d^2-2e), S=sqrt(Z), Q0=sqrt(4S-7). The
unclipped expression W has derivatives

    W_e=1/A+(2e-1)/(Q0 S),
    W_d=1-d/A+2d/(Q0 S).                         (RP20)

For e in [1/4,19/25] and d in [2,2231/1000], these are positive.
Indeed, if e<1/2 the negative term in W_e has absolute value at
most 1/4, while 1/A>=1/d>4/9. If e>=1/2 both terms are nonnegative.
Also d/A<4/3, S<sqrt(5)<9/4 and Q0<sqrt(2)<3/2, so
W_d>-1/3+32/27>0.

The clipped W_+ remains increasing in e across Z=4: below that
level it is just d-sqrt(d^2-2e), increasing in e. If increasing e
to its upper endpoint places Z below 4, the remaining time is at
most 2-sqrt(4-38/25)<9/20<7/10. Otherwise increasing d to its
upper endpoint keeps Z>4, where W is increasing. It therefore
suffices to check these two endpoint pairs:

    (d,e)=(2231/1000,3/4),
    (d,e)=(111/50,19/25).                         (RP21)

At the first pair,

    d-sqrt(d^2-2e)<11/30,
    Z=4790111/1000000<(219/100)^2,
    D(Z)<1/3.

For the first time comparison, squaring reduces it to
d>1471/660, satisfied by 2231/1000. For the duration comparison,
4(219/100)-7=44/25<16/9. Hence W<7/10.

At the second pair,

    d-sqrt(d^2-2e)<3/8,
    Z=18985/4000<(109/50)^2,
    D(Z)<5/16.

The first inequality follows from (3/4)d>38/25+9/64.
The second duration comparison is 4(109/50)-7=43/25<441/256.
Thus W<11/16<7/10. Together with RP18,

    U(r)<=1 a.e. for r>=7/10 on the reflected used interval.       (RP22)

Any final removed positive-tilt interval has U=0 directly, so the
conclusion includes it as well.

## 5. The resulting original companion prefix

The elementary Taylor estimate

    cos(x)>=1-x^2/2+x^4/25  (0<=x<=1)

gives cos(7/10)>19/25. It follows, since C+w<37/50+1/50=19/25,
that

    acos(C+w)>7/10.

If 0<t<=asin(C+w), then r=L-t>=acos(C+w)>7/10. RP22 proves
exactly RP5. The Taylor inequality follows, for example, from
cos(x)>=1-x^2/2+x^4/24-x^6/720 and
1/24-x^2/720>=29/720>1/25 on [0,1].

## 6. A prefix is enough to contradict the short terminal facet

This final argument only needs RP5 and the general data RP1–RP3.
Write g(0)=1-h_L and g'(0)=C+T_L, where h_L>=0. At
x=-C+z, 0<=z<=m_max, consider the global second-wall maximum over
0<t<L. Its limit at zero is -h_L<=0, and its limit at L is
negative infinity because C+z<1 and the unused tail is RP2.

Consequently any positive maximum is attained at an interior angle.
The support g is C^1 there: its regular pieces have bounded density,
the central atom has been removed when needed, and PS forbids a
companion terminal atom. The stationary equation is D_x(t)=x. If
(X,Y) is the corresponding outer support point, then D_x=X+sin t,
and X>=-2C gives

    sin t<=C+z, hence t<=asin(C+z)<=asin(C+w).      (RP23)

On this prefix, v<=1. The support Green formula yields

    g(t)<=1-h_L cos t+(C+T_L)sin t,
    S_t(-C+z)<=-h_L+(T_L+z)tan t.

From RP3, T_L+m_max<=D_H+(c-D_H)=c. Thus, with
K(x)=x/sqrt(1-x^2), every positive visited niche value at these
abscissae is at most

    c K(C+c/2).                                  (RP24)

The following uniform scalar comparison is elementary:

    K(C+c/2)<2C-c,
    1/2<=C<=37/50, 0<c<=1/25.                    (RP25)

For fixed c, the difference 2C-c-K(C+c/2) is concave in C since
K''(x)>0. Its minimum is therefore at an endpoint. At C=1/2,
K(C+c/2)<=K(13/25)<2/3<24/25<=2C-c. At C=37/50,
K(C+c/2)<=K(19/25)<6/5<36/25<=2C-c. The two radical comparisons
are respectively 1521<1824 and 9025<9504 after squaring.

Meanwhile the outgoing wall at the same x is

    R_a(-C+z)=(c/s)(2C+T_R-D_H-z)
              >=(c/s)(2C-c)>=c(2C-c),            (RP26)

since z<=m_max=c-D_H. Equations RP24–RP26 give strict outgoing
exposure on the whole closed interval [-C,-C+m_max]. The strict
gap at its right endpoint persists a positive distance farther
into J, by continuity. Therefore

    |E|>m_max>=m.

PS's fixed-angle terminal occupation is one on E and has integral m,
a contradiction. This remains a contradiction if m_max=0, because
strict exposure at -C still persists on a positive interval.

**Conclusion RP1.** An above-reference largest-angle partial-cap
maximizer cannot have `0<cos(a)<=1/25`. TP supplies RP1–RP4 for
all three orientations in that interval, RP22 supplies the companion
prefix, and the terminal occupation contradiction then applies.

The proof uses no full barrier contact chart, global unit first wing,
global unit companion wing, terminal first-moment law, or hypothetical
full-turn completion. The remaining Gate 2 problem has larger
terminal deficit; this note does not assert the entire gate.
