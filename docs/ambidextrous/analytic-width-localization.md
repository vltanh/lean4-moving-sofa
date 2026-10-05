# Analytic width proof, part II: localization without parameter boxes

This is the finite analytic case reduction needed by [the loss-partition lemmas](analytic-width-loss-partition.md). It uses a two-variable convex lower bound, four explicitly minimized boundary quadratics, and concavity in the far tails. There is no exhaustive search or list of certified parameter boxes.

Retain

\[
c=\sqrt{3/5},\ s=\sqrt{2/5},\ q=s/c=\sqrt{2/3},\ r=c/s=1/q,
\quad a=8/15,\quad H=1/2,
\]

and put k=1/c-1, l=1/s-1. Define

\[
\kappa=2-rk-ql
=2-\frac{c+s-1}{cs},\qquad
\alpha=qa-k,\qquad\beta=ra-l.
\tag{AL.1}
\]

For d,e>=0, let lambda(d,e) be the one-hallway loss obtained from LP.1, with its outer roof and inner tent given by LP.4. If two hallways are used in LP.1, each one's lambda is at most their combined Lambda.

## 1. Statement

**Lemma AL1 (small loss forces the complete triangles into their assigned bands).** If

\[
\lambda(d,e)\leq9/50,
\]

then

\[
\boxed{3/20<d<3/7,\qquad1/10<e<1/2.}
\tag{AL.2}
\]

In this rectangle the positive inner tent lies entirely in [a,2-a] times [0,1/2]. Its two outer-deficit triangles lie entirely in the outside bands and have heights at most 1/2. Thus none of these three losses is truncated by the partition.

For the complementary angle, the same statement holds after reflection of x and interchange of d,e.

## 2. Elementary constants used below

All the following bounds follow by squaring positive quantities:

\[
22/9<\sqrt6<49/20<5/2,\quad
13/16<q<49/60<5/6,\quad6/5<r<5/4,
\]

\[
129/100<1/c<13/10,\qquad79/50<1/s<8/5.
\]

They imply

\[
0<\alpha<131/900<3/20<3/7<qa<1/2,
\quad0<\beta<13/150<1/10<1/2<ra<2/3.
\tag{AL.3}
\]

Also

\[
\boxed{7/6<\kappa<6/5.}
\tag{AL.4}
\]

For a short exact verification, c+s has square 1+2sqrt(6)/5. The inequality kappa>7/6 is equivalent to c+s<1+sqrt(6)/6; the difference of the squares is 1/6-sqrt(6)/15>0. The inequality kappa<6/5 is equivalent to c+s>1+4sqrt(6)/25; the difference of these squares is (50sqrt(6)-96)/625>0.

## 3. A globally valid lower bound for the one-hallway loss

For m>0 define

\[
C_m(z)=\int_0^a[z-mx]_0^Hdx
=\frac{z_+^2-(z-ma)_+^2-(z-H)_+^2+(z-H-ma)_+^2}{2m}.
\tag{AL.5}
\]

Here z_+=max(z,0), and the clipping notation is from LP.1. The integral formula follows by writing [w]_0^H=w_+-(w-H)_+ and integrating each positive affine part.

The inner triangle has baseline length

\[
G=\kappa-rd-qe
\]

when this is positive, and height cs G. Its whole-plane area capped at height H is

\[
B(G)=\frac{cs}{2}\left[G_+^2-(G-H/(cs))_+^2\right].
\tag{AL.6}
\]

The function B is convex and nonnegative, with second derivative between zero and cs almost everywhere. Subtracting the small triangle above height H proves the formula.

The tent outside the middle band is bounded above on the left by (qx-d-k)_+ and on the right by (r(2-x)-e-l)_+. Integrating these over x<a and x>2-a respectively bounds the omitted areas by (alpha-d)_+^2/(2q) and (beta-e)_+^2/(2r). On the outer bands retain just the left outer wall on the left and the right outer wall on the right. Consequently, for all d,e>=0,

\[
\lambda(d,e)\geq\mathcal L(d,e):=
C_q(d)+C_r(e)+B(\kappa-rd-qe)
-\frac{(\alpha-d)_+^2}{2q}
-\frac{(\beta-e)_+^2}{2r}.
\tag{AL.7}
\]

This is a lower bound even when a tent is clipped, has its apex outside the middle band, or is empty. The omitted tails were overestimated by the individual wall lines, not identified with triangles under an unproved contact pattern.

## 4. Convexity on the central parameter rectangle

Let

\[
\mathcal D=[0,H]\times[0,ra],\qquad
\mathcal R=[3/20,3/7]\times[1/10,1/2].
\]

By AL.3, R lies inside D. On 0<=d<=H, the function

\[
C_q(d)-(\alpha-d)_+^2/(2q)
\]

is convex: its second derivative is zero below alpha, 1/q between alpha and qa, and zero above qa. On 0<=e<=ra the corresponding e function has second derivative zero below beta, 1/r between beta and H, and zero above H. First derivatives are continuous at each breakpoint. Since B is convex, L is convex on D.

On R, and on a neighborhood of the minimizing points on its four sides used below, no tail or height clipping occurs. There L is the quadratic

\[
Q(d,e)=\frac r2d^2+\frac q2e^2+
\frac{cs}{2}(\kappa-rd-qe)^2.
\tag{AL.8}
\]

At d=e=t=cs*kappa/2, which lies between 77/270 and 3/10, this quadratic has value cs*kappa^2/4<9/50. The point lies in the interior of R, and the formula for L there is indeed Q.

The minimum of Q for fixed d occurs at

\[
e_d=\frac{\sqrt6}{7}(\kappa-rd),\qquad
Q(d,e_d)=\sqrt6\left[\frac{d^2}{4}+
\frac{(\kappa-rd)^2}{14}\right].
\tag{AL.9}
\]

The fixed-e formulas are

\[
d_e=\frac{\sqrt6}{8}(\kappa-qe),\qquad
Q(d_e,e)=\sqrt6\left[\frac{e^2}{6}+
\frac{(\kappa-qe)^2}{16}\right].
\tag{AL.10}
\]

At d=3/20 or 3/7, the bounds in Section 2 give 1/10<e_d<1/2. At e=1/10 or 1/2 they give 3/20<d_e<3/7. The inner heights at all four points are below H and their baseline lengths positive. Thus L agrees locally with Q at these points, and its derivative tangent to the relevant side is zero. Convexity on D proves they minimize L on the entire corresponding line segment in D, not just within a guessed quadratic region.

Substitute kappa>7/6, r<5/4, q<5/6 and sqrt(6)>22/9 into AL.9–AL.10. The four minimum values are strictly greater than the following rational numbers:

| Side | Explicit lower bound | Excess over 9/50 |
|---|---:|---:|
| d=3/20 | (22/9)[9/1600+(47/48)^2/14] = 657371/3628800 | 4187/3628800 |
| d=3/7 | (22/9)[9/196+(53/84)^2/14] = 80795/444528 | 19499/11113200 |
| e=1/10 | (22/9)[1/600+(13/12)^2/16] = 47531/259200 | 35/10368 |
| e=1/2 | (22/9)[1/24+(3/4)^2/16] = 649/3456 | 673/86400 |

Each entry is an elementary rational identity and positive comparison. No numerical approximation is required to check this table.

It follows that every point of D with L<=9/50 lies strictly inside R. Indeed, the segment from such a point outside R to the interior point (t,t) would meet the boundary of R; convexity would give L<=9/50 there, contradicting the table.

## 5. The unbounded parameter tails introduce no other small-loss component

If d>=H+qa or e>=H+ra, one of the two C terms equals aH=4/15. The negative terms in AL.7 have total magnitude at most

\[
\frac{(3/20)^2+(1/10)^2}{2(4/5)}=13/640.
\]

Therefore

\[
\mathcal L\geq4/15-13/640=473/1920>9/50.
\tag{AL.11}
\]

For fixed e, on H<=d<=H+qa the second derivative of C_q is -1/q=-r, while that of B(kappa-rd-qe) is at most cs*r^2=(3/5)r. The d-tail subtraction is zero there. Thus L is concave in d on this interval. Likewise, for fixed d, on ra<=e<=H+ra its second derivative is at most -q+cs*q^2=-(3/5)q, so it is concave in e there. These assertions apply piecewise with continuous first derivatives, hence on the whole intervals.

If a point outside D had L<=9/50, concavity along an outlying coordinate and the large-endpoint bound AL.11 would give a point on d=H or e=ra with no greater value. Repeating for the other coordinate if necessary gives a point of D, still outside R, with L<=9/50. Section 4 excludes it. This proves that the small sublevel set of L over the entire nonnegative quadrant is contained in the interior of R.

Since lambda>=L, AL.2 follows.

## 6. Geometric consequences of the localized coordinates

For d,e in R, the inner baseline endpoints are

\[
x_L=(d+k)/q,\qquad x_R=2-(e+l)/r.
\]

The inequalities d>alpha and e>beta put these inside [a,2-a]. Also

\[
0<G=\kappa-rd-qe<6/5-(6/5)(3/20)-(4/5)(1/10)=47/50.
\]

The lower bound follows, for example, from G>7/6-(5/4)(3/7)-(5/6)(1/2)=3/14. Because cs<1/2, its height is below 47/100<H.

The left outer triangle ends at d/q<a since d<3/7<qa. The right one begins at 2-e/r>2-a since e<1/2<ra. Their heights are d<3/7<H and e<H. This verifies all the nontruncation assertions of AL1.

The complementary-angle case is obtained by x-reflection and interchange of the coordinates, with no symmetry assumption on the two actual placements.

This lemma is an analytic localization proof: one convex rectangle, four minimized quadratics, and two concave tails replace the computer certificate's parameter-box enumeration. No CI or Lean/Lake was used; the written derivation is subject to independent review.
