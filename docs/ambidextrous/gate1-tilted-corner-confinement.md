# Global tilted corner confinement and one-turn feasibility

Written proof, independently checked within the research session, October 10, 2026. This applies the
[proved C<37/50 width cut](gate1-tilted-full-triangle-width-cut.md). It assumes neither regular wing has curvature
at most one. Every remaining tilted canonical global maximizer gives a
genuine connected one-turn body, so the existing ordinary one-turn area
bound becomes available on the entire remaining tilted branch.

## 1. Setting and statement

Let U be a canonical height-one global maximizer, centered with

    I=[-2C,2C], J=[-C,C],
    1/2<C<=37/50, 0<h<=17/50,
    A(-C)=1-h, A(C)=1,

and with A affine on J. The source and endpoint results already give

    e_R=1/2+h/4+(3n_+-n_-)/4,
    e_L=1/2-3h/4+(3n_--n_+)/4,
    E=e_R+e_L=1-h/2+(n_++n_-)/2,
    max_J n<=E/2, 2P=L_wing.                            (CG1)

Here e_R=A(2C), e_L=A(-2C), n_+=n(C), and n_-=n(-C).
Then every attached inner quadrant with positive apex height has its
apex strictly between -C and C. Consequently n is convex on both
charged wings, n<=A throughout I, and

    S={ (x,y): x in I, n(x)<=y<=A(x) }

is a compact connected genuine one-turn sofa. In particular the already
recorded ordinary one-turn bound G0=22199/10000 implies

    C(3-E-3h/2)+sqrt(C^2+(1-h/2-E/2)^2)<=G0.            (CG2)

One may also use the weaker but sometimes convenient necessary condition

    M/2+C(3-E-3h/2)<=G0.                               (CG3)

## 2. Reduce corner confinement to one explicit trigonometric inequality

Raise the left charged wing by h, make the middle roof horizontal at
height one, and retain the right wing. This is the same genuine lifted
cap Uhat used in the audited finite-angle proofs. Write

    s=sin t, c=cos t,
    f=H_U(c,s), g=H_U(-s,c),
    fhat=H_Uhat(c,s), ghat=H_Uhat(-s,c).

Let delta=arctan(h/(2C)). For t>=delta the original left supporting
point lies on the low wing, so

    f=fhat, g=ghat-hc.

If xhat is the lifted inner corner's horizontal coordinate, the actual
one is therefore

    x_c=xhat+hsc.                                      (CG4)

For the lifted cap, its unit-height box and the actual left middle
endpoint (-C,1) give

    fhat<=2Cc+s, ghat>=Cs+c,
    xhat=(fhat-1)c-(ghat-1)s
         <=C(2-3s^2)+s-c.                             (CG5)

The horizontal corner-confinement lemma already proved in the horizontal
maximizer note uses only these box/endpoint constraints. Since
1/2<=C<=37/50<13/15, it gives xhat>=-C as well. Equation (CG4) then
gives x_c>-C for 0<t<L. For the upper bound it suffices to prove

    c-s-C(1-3s^2)-hsc>0.                              (CG6)

The next section gives an exact certificate on the entire stated
parameter range.

For 0<t<delta the actual second supporting point is instead (C,1),
so g=c-Cs. Its apex height, using f<=2Cc+s, satisfies

    y_c=(f-1)s+(g-1)c
         <=1-c-s+Csc
          =sc[C-2/(1+c+s)]<0.                         (CG7)

Indeed C<=37/50<2/(1+sqrt(2))<=2/(1+c+s). Such a quadrant contributes
no positive niche anywhere. Thus (CG4)-(CG7) suffice to confine all
positive actual corners; no claim about negative corners is needed.

## 3. An elementary certificate for the remaining inequality

### 3a. If s^2<=1/3

The margin in (CG6) decreases with C and h. It is therefore at least

    [c(50-17s)-(37+50s-111s^2)]/50.

We may enlarge 0<=s<=1/sqrt(3) to 0<=s<=3/5. Both terms to be
compared are positive on this interval. Their squared difference is

    Q(s)=(1-s^2)(50-17s)^2-(37+50s-111s^2)^2
         =1131-5400s+3503s^2+12800s^3-12610s^4.

Put z=s-3/8, so -3/8<=z<=9/40. The exact translation is

    Q=49647/2048-(2091/64)z
          +z^2[116213/16-6115z-12610z^2].              (CG8)

The bracket is a concave quadratic, hence its minimum on this interval
is at an endpoint. Its endpoint values are 249061/32 and 839849/160,
both above 5000. Also 49647/2048>24 and 2091/64<33. Therefore

    Q>24-33|z|+5000z^2
      >=24-1089/20000>0.

Taking the positive square roots proves (CG6) in this case.

### 3b. If s^2>=1/3

Now the margin increases with C, so put C=1/2. We may also enlarge h
from 17/50 to 2/5. The desired lower bound factors as

    c-s-(1-3s^2)/2-(2/5)sc
      =c[1-(2/5)s-c(3s+1)/(2(1+s))].                   (CG9)

Here s>=1/sqrt(3)>1/2. The two terms compared inside the brackets
are nonnegative. After squaring, clearing the positive denominator,
and cancelling 1+s, their difference is positive precisely when

    R(s)=75-105s-139s^2+241s^3>0.

Set z=2s-1 in [0,1]. Then

    8R(s)=143-253z+445z^2+241z^3
           >=143-253^2/(4*445)>0.                     (CG10)

For 0<t<L, c>0, so (CG9) is strictly positive. This proves (CG6)
in the second case and completes positive-corner confinement.

## 4. The cap-minus-niche body is genuinely feasible

For x>=C, every positive quadrant uses its descending first wall, since
its apex lies to the left of C. Thus n is the maximum of affine first
walls and zero on [C,2C], hence is convex there. Reflection gives the
same statement on [-2C,-C]. The box bound gives n(+-2C)=0 and in fact
n=0 outside I.

The box endpoint estimate gives n_+,n_-<=2/5. Thus (CG1) yields

    max_J n<=E/2<=7/10-h/4<1-h<=A(x), x in J.          (CG11)

The strict inequality follows from 3/10-3h/4>=9/200>0.
On each charged wing, A-n is concave. It is nonnegative at both wing
endpoints by (CG11), the positive endpoint heights, and n(+-2C)=0.
Hence n<=A on every fiber of I.

The continuous top graph of A is connected, and every vertical interval
fiber of S meets it. Thus S is compact and connected. Its horizontal
placement lies in the unit-height strip. At every canonical turn angle,
the outer support halfplanes are supplied by U and S avoids the entire
attached inner forbidden quadrant by its definition. These are the same
full canonical one-turn placements used in the horizontal feasibility
proof. No equality between U and conv(S) is required.

The already established ordinary one-turn area bound therefore applies:

    |S|<=G0=22199/10000.                               (CG12)

Its external mathematical input remains Baek's ordinary one-turn theorem
with the existing exact AreaBounds enclosure recorded in
[one-turn-single-excess-quarter.md](one-turn-single-excess-quarter.md). This argument introduces no new
numerical one-turn bound or formalization claim.

## 5. The exact tilted Gerver inequality

The central cap area is 2C-Ch. Convexity of the niche on each wing and
the zero outer endpoint values give

    N_out<=C(n_++n_-)/2=C(E-1+h/2).

Consequently

    |S|=P+2C-Ch-N_out
        >=P+C(3-E-3h/2).                              (CG13)

The two charged-wing chord lengths, including a possible horizontal top
overhang in the total length, imply by (CG1)

    P=L_wing/2
      >=[sqrt(C^2+(1-e_R)^2)
          +sqrt(C^2+(1-h-e_L)^2)]/2
      >=sqrt(C^2+(1-h/2-E/2)^2).                       (CG14)

Both vertical drops are nonnegative because the wings are monotone
toward their middle endpoints. The final inequality is the Euclidean
triangle inequality applied to the two chord vectors.

Combining (CG12)-(CG14) proves (CG2). Replacing (CG14) by the reference
lower bound P>=M/2 gives (CG3). For fixed C,h the left side of (CG2)
decreases with E on the actual geometric range E<=2-h, so any separately
proved upper bound on endpoint niche leakage can be substituted safely.

The theorem makes the ordinary one-turn estimate available throughout
the remaining tilted domain. It does not establish small leakage or
exclude that domain by itself.
