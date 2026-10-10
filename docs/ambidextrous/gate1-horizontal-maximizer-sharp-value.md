# Gate 1: the complete horizontal canonical-maximizer value theorem

**October 10, 2026. Written mathematical proof, independently audited within this research session; not externally refereed or Lean-verified.** The entire horizontal branch of the active scalar maximizer problem is settled here:

**Theorem HW1.** If a MID-canonical global maximizer of the spatial score
\[
\mathcal P(U)=\int_{I\setminus J}A(x)\,dx-\int_J n_U(x)\,dx
\]
has a horizontal middle facet, then \(\mathcal P(U)\le M/2\).

This is a theorem about a global maximizer on the **full cap domain**, using its proved endpoint and exposure laws. No reflection symmetry, fixed contact pattern, or initial unit-curvature bound is assumed. By attainment and MID canonicalization, any counterexample to the universal sharp scalar bound must therefore have a **tilted** canonical maximizing cap. The tilted branch is not settled by this note, and **Gate 1 remains ACTIVE**.

The proof combines four exact intervals. Put \(C=W/4\) and
\[
C_H=\frac1{35}\sqrt{523+2\sqrt{701}}.
\]

| Width parameter | Argument |
|---|---|
| \(C\le1/2\) | [SW1](gate1-horizontal-short-width-exclusion.md): strict value \(\le41/50<M/2\). |
| \(1/2<C\le C_H\) | [CH6](gate1-spatial-maximizer-curvature-and-horizontal-value.md): one good quarter forces both; the general signed-roof calibration gives \(\mathcal P\le M/2\). |
| \(8571/12500\le C\le4/5\) | Part II below: exact leakage bounds contradict the ordinary one-turn area bound. The left endpoint is strictly below \(C_H\). |
| \(C\ge4/5\) | Part I gives \(C<13/15\); Part III excludes \([4/5,13/15]\) by three actual niche angles. |

The endpoint and stationary identities are [EP1–EP2](gate1-global-endpoint-complementarity.md) and [LH2–LH3](gate1-global-positive-pressure-and-wing-identity.md). The spatial curvature estimates, top localization, and short-width sharp comparison are proved in [CH](gate1-spatial-maximizer-curvature-and-horizontal-value.md). All niches below are the **complete positive two-attached-wall niche**, with angles discarded only when obtaining valid lower bounds.

## Part I. A first exact width exclusion

Center \(I=[-2C,2C]\), \(J=[-C,C]\), with \(A=1\) on \(J\). Set \(a=2C\), \(k=\sqrt2-1\), and define the actual support parameters
\[
u=\sqrt2h_U(\pi/4)-1,\qquad
v=\sqrt2h_U(3\pi/4)-1,\qquad m=(u+v)/2.
\]
The central plateau and height-one box give \(a/2\le u,v\le a\). The actual endpoint points imply
\[
u\ge a+e_R-1,\qquad v\ge a+e_L-1.
\]
For a horizontal global maximizer, EP gives
\[
e_R+e_L=1+\frac{n_U(C)+n_U(-C)}2\ge1.
\]
Hence
\[
m\ge a-1/2=2C-1/2.
\tag{HW.1}
\]

The actual 45-degree support lines majorize the exterior roof by
\(A_0(x)=\min(1,1+u-x,1+v+x)\), and its actual niche tent is
\([\min(u-k-x,v-k+x)]_+\). Integrating gives, whenever \(m>k\),
\[
\mathcal P(U)\le F(u,v)
=a-\frac{(a-u)^2+(a-v)^2}{2}-(m-k)^2
+\frac{(u-k-a/2)_+^2+(v-k-a/2)_+^2}{2}.
\tag{HW.2}
\]
At fixed \(a\), this function is symmetric and concave in \((u,v)\). In each of the four clipping regions its Hessian has diagonal entries \(-3/2\) plus the respective clipping indicator and off-diagonal entries \(-1/2\); all are nonpositive. The first derivatives agree across clipping boundaries. Thus
\[
F(u,v)\le F(m,m)
=a-(a-m)^2-(m-k)^2+(m-k-a/2)_+^2.
\tag{HW.3}
\]

Suppose \(C\ge13/15\). Then HW.1 places \(m\) to the right of the unconstrained maximum \(C+k/2\) in the unclipped region; in the clipped region the derivative in \(m\) is \(2(C-m)<0\). Therefore HW.3 is bounded above by its value at \(m=2C-1/2\):
\[
\mathcal P(U)\le
\begin{cases}
Q_1(C)=2C-1/4-(2C-1/2-k)^2,& C\le1/2+k,\\
Q_2(C)=(1+2\sqrt2)C-3C^2-1/4,& C\ge1/2+k.
\end{cases}
\tag{HW.4}
\]
Both branches are decreasing on their stated parts of \([13/15,\infty)\), and their values agree at the switch. Using \(\sqrt2<99/70\),
\[
Q_1(13/15)=\frac{67\sqrt2}{15}-\frac{2477}{450}
<\frac{256}{315}<\frac{41}{50}<\frac M2.
\tag{HW.5}
\]
This contradicts the reference score at a global maximizer. Together with SW1 it proves
\[
\boxed{\frac12<C<\frac{13}{15}.}
\tag{HW.6}
\]

## Part II. Exact horizontal leakage bootstrap

The next argument excludes the whole interval
\[
\frac{8571}{12500}\le C\le\frac45.
\tag{B.1}
\]
Its lower endpoint lies strictly below \(C_H\), as checked exactly below.

## 1. Canonical horizontal hypotheses and one-turn feasibility

Let U be a horizontal canonical global maximizer, centered with
\(I=[-2C,2C]\), \(J=[-C,C]\). SW1 gives C>1/2. CH2 gives top exactly
\(J\times\{1\}\). Write \(e_R,e_L\) for its end heights,
\(E=e_R+e_L\), and \(n_\pm=n(\pm C)\). EP and LH give

\[
e_R=\frac{2+3n_+-n_-}{4},\quad
e_L=\frac{2+3n_--n_+}{4},\quad
E=1+\frac{n_++n_-}{2},\quad
\max_J n\le E/2,\quad 2P=L_{\rm wing}.
\tag{B.2}
\]

The box-wall bound CH5 gives

\[
n_\pm\le H(C):=1-\sqrt{1-C^2},\qquad
\frac12-\frac H4\le e_R,e_L\le\frac12+\frac{3H}4.
\tag{B.3}
\]

Here and below C<1. The following geometric facts justify applying the
ordinary one-turn bound, rather than assuming it transfers automatically.

### Every inner corner lies horizontally in J for 1/2<=C<=13/15

Put s=sin t, k=cos t. The unit-height box and the left top endpoint give
\(f(t)\le2Ck+s\), \(g(t)\ge Cs+k\). Hence

\[
c_x=(f-1)k-(g-1)s\le C(2-3s^2)-k+s.
\]

We show \(C(1-3s^2)\le k-s\).

* If \(s^2\le1/3\), then \(k\ge1-3s^2/5\), as follows by
  squaring positive sides. Using C<=13/15, the desired margin is at least
  \[
  2s^2-s+2/15=2(s-1/4)^2+1/120>0.
  \]
* If \(1/3\le s^2\le1/2\), the left side is nonpositive and the
  right side nonnegative.
* If \(s^2\ge1/2\), use C>=1/2 and
  \[
  2(s-k)=\frac{2(2s^2-1)}{s+k}
       \le4s^2-2\le3s^2-1.
  \]

Thus c_x<=C; reflection gives c_x>=-C. This proof does not use curvature
domination or a source contact chart.

### Convex wing niches and a genuine connected one-turn body

For x>=C, all quadrant apexes have x-coordinate at most C. Each positive
quadrant roof there uses its first descending wall, so n is the maximum
of affine first-wall roofs and zero. Thus n is convex on [C,2C]. It is
convex on [-2C,-C] by reflection. The box bound gives n(+-2C)=0, and
indeed the niche vanishes outside I.

On J, A=1 and B.2 gives n<=E/2<=1. On each wing A-n is concave and is
nonnegative at both endpoints. Therefore n<=A everywhere. The set

\[
S=U\setminus N(U)=\{(x,y):x\in I,\ n(x)\le y\le A(x)\}
\]

is compact and connected: its continuous top graph is connected and
every interval fiber meets that graph. The outer support halfplanes of U
and exclusion of every corresponding inner quadrant provide the full
canonical one-turn placements for S. Actual equality between U's hull
and the moving sofa's hull is not needed.

Thus the existing ordinary one-turn bound applies to S. Use the already
recorded exact bound

\[
G\le G_0:=22199/10000
\]

from SE.1 of [one-turn-single-excess-quarter.md](one-turn-single-excess-quarter.md), whose explicit external
dependency is Baek's ordinary one-turn theorem and whose rational value
comes from the six existing AreaBounds enclosures. No stronger numerical
bound or new Lean computation is assumed here.

Convexity of n on each wing gives

\[
N_{\rm out}:=\int_{I\setminus J}n
\le\frac C2(n_++n_-)=C(E-1).
\]

The two wing chord bounds and the triangle inequality give

\[
P=\frac{L_{\rm wing}}2
\ge\frac12\left[\sqrt{C^2+(1-e_R)^2}
                +\sqrt{C^2+(1-e_L)^2}\right]
\ge\sqrt{C^2+(1-E/2)^2}.
\]

Since \(|S|=P+2C-N_{\rm out}\), we obtain the necessary inequality

\[
\boxed{C(3-E)+\sqrt{C^2+(1-E/2)^2}\le G_0.}
\tag{B.4}
\]

In particular, if \(n_\pm\le B\le1\), then E<=1+B and the left
side of B.4 decreases with E. Hence

\[
\boxed{C(2-B)+\sqrt{C^2+(1-B)^2/4}\le G_0.}
\tag{B.5}
\]

This is the exact scalar inequality used below.

## 2. Curvature excess can occupy only a short initial interval

Use the horizontal velocity notation p,q,u,v of CH.2. The same-sign
shadowing and propagation theorems are valid for the spatial maximizer:
u=0,v<=1/2 on p>0,q>0; every later positive-q component has q<=1/8.
Consequently any u>1 must lie in the initial positive-q component after
its first p=0 time t_A. If this crossing does not occur, u<=1 everywhere
and the endpoint leakage is zero.

Let e=e_R. The initial energy calculation gives

\[
q(t_A)+1\le\sqrt{9C^2-e(1-e)}.
\]

Define

\[
\epsilon=\bigl(\sqrt{9C^2-e(1-e)}-2\bigr)_+,
\qquad h=\sqrt{1+4\epsilon}-1.
\tag{B.6}
\]

While q>1 after the crossing, p'<=-1, hence p(t_A+tau)<=-tau.
The nonlinear bound on v then gives

\[
q'\le-\frac{1+\tau}{2}\qquad(0\le\tau\le1).
\]

When p>=-1 this follows from v<=kappa(p)=(1-p)/2. If p<-1, the
stronger bound q'<=-1 still implies it for tau<=1. Thus

\[
(u(t_A+\tau)-1)_+
\le\left(\epsilon-\frac\tau2-\frac{\tau^2}{4}\right)_+.
\tag{B.7}
\]

For C<=4/5, B.3 gives

\[
\epsilon\le
\left(\sqrt{9C^2-1/4+9H(C)^2/16}-2\right)_+<2/5,
\]

so h<1 and the whole possible excess interval is covered by B.7. All
other parameter values have u<=1.

On the initial positive-positive interval q'>=-1, since v>=0,p>=0.
Therefore p'=-1-q<=-3C+t, and

\[
p(t)\le e-3Ct+t^2/2.
\]

The first root of this upper quadratic bounds the crossing:

\[
t_A\le T(C,e):=3C-\sqrt{9C^2-2e}.
\tag{B.8}
\]

If the positive component ends before such a crossing, the leakage-zero
case has already been treated.

## 3. The endpoint leakage kernel

The top exactly equals J, so f(L)=1,f'(L)=-C. Solving f''+f=u backward
from L gives the exact first-wall identity at x=C:

\[
R_t(C)=\frac1{\sin t}\int_t^L\sin(s-t)[u(s)-1]ds.
\tag{B.9}
\]

The box-wall estimate further says R_t(C)<=0 unless

\[
t>t_{\rm box}(C):=\frac\pi2-2\arctan C
 =2\arctan\frac{1-C}{1+C},
\qquad
\sin t_{\rm box}=\frac{1-C^2}{1+C^2}.
\tag{B.10}
\]

For these remaining angles, discard negative curvature differences in
B.9 and use sin(s-t)<=s-t. B.7 yields

\[
n(C)\le
\frac{A_0(t_A-t_{\rm box})_++A_1}{\sin t_{\rm box}},
\tag{B.11}
\]

where the integrals of the quadratic envelope are

\[
A_0=\int_0^h(\epsilon-\tau/2-\tau^2/4)d\tau
    =h^2/4+h^3/6,
\]
\[
A_1=\int_0^h\tau(\epsilon-\tau/2-\tau^2/4)d\tau
    =h^3/12+h^4/16.
\tag{B.12}
\]

Here epsilon=(h^2+2h)/4. The extra factor bound in B.11 is valid even
if t_A<t_box, because s=t_A+tau and t>=t_box imply
s-t<=(t_A-t_box)_++tau. Reflection gives the same estimates for n(-C).

## 4. Seven exact rational intervals

Every decimal in the following table denotes the exact terminating
rational number. Each row supplies an interval [a,b] and witnesses
\(H_*,h_*,T_*,t_*,B_*\).

| a | b | H_* | h_* | T_* | t_* | B_* |
|---|---|---|---|---|---|---|
| 0.68568 | 0.686 | 0.2724 | 0.0135 | 0.377 | 0.368 | 1/400000 |
| 0.686 | 0.69 | 0.2762 | 0.038 | 0.3784 | 0.3627 | 1/30000 |
| 0.69 | 0.7 | 0.2859 | 0.0971 | 0.3801 | 0.3492 | 1/2000 |
| 0.7 | 0.725 | 0.3113 | 0.2323 | 0.3845 | 0.3161 | 3/400 |
| 0.725 | 0.75 | 0.3386 | 0.3542 | 0.3799 | 0.2837 | 31/1000 |
| 0.75 | 0.775 | 0.3681 | 0.4662 | 0.3765 | 0.2521 | 83/1000 |
| 0.775 | 0.8 | 0.4 | 0.5703 | 0.3742 | 0.2213 | 9/50 |

The following **rational inequalities** verify every row. They are the
certificate, rather than numerical evaluations of a transcendental
function. Put \(z=(1-b)/(1+b)\),
\(\epsilon_*=(h_*^2+2h_*)/4\), and use A0,A1 from B.12 with h=h_*.

\[
\begin{aligned}
&(1-H_*)^2\le1-b^2,\\
&(2+\epsilon_*)^2\ge9b^2-1/4+9H_*^2/16,\\
&6aT_*-T_*^2\ge1+3H_*/2,\qquad T_*<3a,\\
&t_*\le2(z-z^3/3),\\
&B_*\frac{1-b^2}{1+b^2}
 \ge A_0(T_*-t_*)_++A_1.
\end{aligned}
\tag{B.13}
\]

Indeed H(C)<=H_* for C<=b. The second inequality gives h<=h_* by
B.6–B.7 and B.3. The third gives T(C,e)<=T_* whenever C>=a and
e<=1/2+3H_*/4; it is just the squared version of B.8. The fourth uses
the elementary integral bound arctan z>=z-z^3/3. Finally sin t_box(C)
is decreasing with C, so B.11 and the last inequality prove
n(C),n(-C)<=B_* uniformly throughout the row's interval.

For every row the final contradiction is also a rational check:

\[
R_*:=G_0-a(2-B_*)>0,
\qquad
a^2+(1-B_*)^2/4>R_*^2.
\tag{B.14}
\]

Thus
\(a(2-B_*)+\sqrt{a^2+(1-B_*)^2/4}>G_0\). The left side in B.5
increases with C at fixed B_*, so B.14 contradicts B.5 on the whole
interval [a,b].

All B.13 and B.14 inequalities were checked with exact rational
arithmetic, not floating point. The companion
[check_horizontal_leakage_exact.py](computer-assisted/check_horizontal_leakage_exact.py) uses only Python's standard-library
Fraction class and the seven stated rows.
It performs no search or sampled-angle approximation.

The initial rational a0=8571/12500 is below C_H. To check this without
rounding C_H, put z0=a0^2. Then 35z0-15>0 and

\[
4(1-z_0)-(35z_0-15)^2
=\frac{878611101631}{976562500000000}>0.
\]

The increasing defining expression 35z-15-2sqrt(1-z) is therefore still
negative at z0. This proves the claimed overlap with the existing
horizontal sharp-value interval.


## Part III. Wide-width exclusion by three actual niche angles

## Statement

Let a height-one downward convex cap have projection I=[-a,a], horizontal
roof A=1 on J=[-a/2,a/2], and endpoint heights e_R=A(a), e_L=A(-a).
Assume its actual full niche n satisfies the horizontal EP identities

    e_R = 1/2+(3 n(a/2)-n(-a/2))/4,
    e_L = 1/2+(3 n(-a/2)-n(a/2))/4.

If 8/5 <= a <= 26/15, then its actual spatial score satisfies

    P < 261719/320000 < 41/50 < M/2.                 (W1)

Together with Part I's independent 45-degree exclusion for
C=a/2 >=13/15, this excludes every horizontal global maximizer with
C>=4/5. Only the three real niche angles pi/8, pi/4, 3pi/8 are used
to prove (W1); all other niche portions are retained as nonnegative gain.

Put

    r=sqrt(2), k=r-1, c=cos(pi/8), s=sin(pi/8).

Useful exact identities are

    s/c=k, k+1/k=2r, 1+k=r,
    1/s+1/c=4c, 1/s-1/c=4s,
    1/(r c)=2s, 1/(2sc)=r.

## 1. Endpoint and 45-degree data

The unit-height box gives, for C=a/2<1,

    n(+-C) <= H(C):=1-sqrt(1-C^2).

Indeed, the first wall at x=C is at most
1+(C cos(t)-1)/sin(t), whose maximum is H(C); reflect for -C.
Since C<=13/15, H(C)<2/3. Thus EP implies

    e_R,e_L >=1/3,       E:=e_R+e_L >=1.             (W2)

Define the actual supports

    u=r h(pi/4)-1,       v=r h(3pi/4)-1,
    m=(u+v)/2,           d=(u-v)/2,
    w_R=a-u,             w_L=a-v.

The plateau and box give a/2<=u,v<=a. The actual endpoint points give
u>=a+e_R-1 and v>=a+e_L-1. Consequently

    0<=w_R,w_L<=2/3,     m>=a-1/2>=11/10.           (W3)

The cap is below the genuine upper majorant

    A0(x)=min(1,1+u-x,1+v+x),      -a<=x<=a.

Its two charged exterior wings have area

    O0=a-[(a-u)^2+(a-v)^2]/2.

Write D=integral_(I\J)(A0-A)>=0. The actual 45-degree niche tent is

    n45(x)=[min(u-k-x,v-k+x)]_+.

Its apex d is in J. Since m>k, its exact integral on J is

    N45=(m-k)^2
         -[(u-k-a/2)_+^2+(v-k-a/2)_+^2]/2.

Let F=O0-N45. For fixed a, F is concave in (u,v), and symmetric.
This is the same elementary 45-degree concavity used in the
short-width proof: the Hessian in the positive-apex region is
diagonal -3/2 plus the corresponding clipping indicator, with
off-diagonal -1/2; all four resulting Hessians are nonpositive.
Therefore

    F <= Fsym(a,m)
       :=a-(a-m)^2-(m-k)^2+(m-k-a/2)_+^2.           (W4)

## 2. Exterior payment from flat pieces only

Define the actual near-vertical support deficits

    delta_L=c+s v-h(5pi/8),
    delta_R=c+s u-h(3pi/8).

These are nonnegative because A0 supports those directions at its two
top corners. The height-one points at the endpoints of J imply

    0<=delta_L<=s(v-a/2)=s(a/2-w_L),
    0<=delta_R<=s(u-a/2)=s(a/2-w_R).                 (W5)

On the flat portion x=-v+z, 0<=z<=delta_L/s, the new supporting line
cuts A0 by the height delta_L/c-kz. This entire small triangle lies
in the left charged wing by (W5). Its area is

    delta_L^2/(2sc)=r delta_L^2.

The reflected right triangle lies in the other wing. In particular,
there is no need to fit any triangle past a vertical endpoint, and

    D >= r(delta_L^2+delta_R^2).                    (W6)

## 3. Two disjoint additional niche half-triangles

At theta=pi/8 the actual second wall is

    b+kx,       b=1-1/c+k v-delta_L/c.

The actual endpoint (a,e_R) supplies a lower bound for the companion
first wall:

    R_theta(x) >= B-x/k,
    B=e_R+a/k-1/s.

Thus the full niche contains the positive part of the true two-wall
lower tent min(b+kx,B-x/k).

On the right of the 45-degree apex d, the signed 45-degree roof is
u-k-x. Set

    x_L=(u-k-b)/r,
    x_*=(B-b)/(2r),
    Z_R=(B+b)/2-u+k.

Then Z_R=r(x_*-x_L). If Z_R>0, on [x_L,x_*] the lower tent equals
b+kx and exceeds the signed 45-degree roof by r(x-x_L). We now
check that this entire half-triangle is inside J, to the right of d,
and above the positive part of the 45-degree roof.

First,

    x_L-d = k m+2s-1+delta_L/(r c)>0,               (W7)

because m>=11/10, k>2/5, and s>3/8.

Next, writing v=a-w_L,

    x_*=[2a+e_R+k w_L-(1+4s)+delta_L/c]/(2r).

Using delta_L/c<=k(a/2-w_L) and e_R<=1 shows that x_*<=a/2 follows
from

    ((3-r)/2)a <=4s.

This holds throughout a<=26/15: its left side is below 104/75
using r>7/5, while its right side is above 3/2. Hence

    x_* < a/2.                                    (W8)

Finally, x_*<=u-k follows from

    e_R+2r w_R <=(3k/2)a+1+4s-2rk.

Since e_R<=1-w_R and w_R<=2/3, it is enough to prove

    (2r-1)*2/3 <=(12/5)k+4s-2rk.                  (W9)

For a completely rational check, r<10/7 and k<3/7 bound the left
side by 26/21 and bound the right side below by
3/2-48/245=639/490>26/21. We used r>7/5 to note that
12/5-2r<0 when applying the bound k<3/7. Therefore

    x_* < u-k.                                    (W10)

Equations (W7)-(W10) prove the claimed half-triangle containment.
Its area is Z_R^2/(2r). If Z_R<=0 the zero lower bound is immediate;
no interval assertion is needed in that case.

Reflection, using the actual angle 3pi/8 and endpoint (-a,e_L),
gives a half-triangle on the left of d of area (Z_L)_+^2/(2r), with

    Z_R=Z_R^0-delta_L/(2c),
    Z_L=Z_L^0-delta_R/(2c),

and

    Z_R^0+Z_L^0
      =E/2+a/k+(k-2)m+1-1/s-1/c+2k=:S0.            (W11)

The two half-triangles lie on opposite sides of d, so there is no
overlap overcount. Hence the actual full niche satisfies

    integral_J n >= N45+[(Z_R)_+^2+(Z_L)_+^2]/(2r). (W12)

## 4. Combine the ordinary exterior and niche payments

Put D0=r(delta_L^2+delta_R^2),
G0=[(Z_R)_+^2+(Z_L)_+^2]/(2r), and Delta=delta_L+delta_R.
By (W11) and Cauchy-Schwarz,

    (S0)_+ <= sqrt(4r G0)+sqrt(r D0/(4c^2)),

so

    (S0)_+^2 <= [4r+r/(4c^2)](D0+G0) <=8(D0+G0).

The coefficient is strictly below 8 already from r<3/2 and c^2>3/4;
the displayed product inequality also covers D0+G0=0.
Together with (W6) and (W12), this yields the weak bound sufficient
for the proof:

    P <= Fsym(a,m)-(S0)_+^2/8.                     (W13)

Use E>=1 and the elementary coefficient inequalities

    1/k>12/5,        k-2>-8/5,
    3/2+2k-4c >-11/8

to lower-bound S0 by the simple affine expression

    S(a,m)=(12/5)a-(8/5)m-11/8.

For the last constant comparison, 4c<7/8+2r follows by squaring:
the difference of the squared right and left sides is 49/64-r/2>0.
Consequently

    P <= G(a,m):=Fsym(a,m)-[S(a,m)_+]^2/8.          (W14)

## 5. A single concave scalar bound

The function Fsym is jointly concave in (a,m) on the region in use.
Its Hessian before window clipping is

    [[-2,2],[2,-4]],

and after clipping is

    [[-3/2,1],[1,-2]].

Both are negative definite, and the first derivatives match at the
clipping boundary. Subtracting the convex positive square of the
affine function S preserves concavity of G.

At a0=8/5, m0=11/10, the clipping term vanishes and S=141/200>0.
The exact derivatives are

    G_a(a0,m0)=-423/1000,
    G_m(a0,m0)=2k-459/500<0.

For every a>=a0, m>=a-1/2, the displacement decomposes as

    (a-a0,m-m0)=(a-a0)(1,1)
                      +(m-a+1/2)(0,1).

Both directional derivatives are negative, so the supporting-plane
inequality for the concave G gives G(a,m)<=G(a0,m0). Finally

    G(a0,m0)=(21/5)k-295081/320000
             <261719/320000<41/50,

where k<29/70 follows from sqrt(2)<99/70. This proves (W1).

All payments used ordinary cap area and ordinary portions of the
actual full two-ray niche; no niche connectivity, reflection
symmetry, curvature bound, artificial grid stationarity, or
candidate contact chart was assumed.


## Conclusion and remaining Gate 1 obligation

Parts I–III and CH6 cover every positive width, with an exact overlap at the lower endpoint of the leakage certificate. They prove HW1. The only external area theorem used in the new wide-width argument is the established ordinary one-turn theorem, applied after proving the cap survivor is a genuine connected one-turn sofa; its numerical constant is the exact rational enclosure SE.1. The short horizontal comparison CH6 instead uses the direct signed-roof calibration and does not depend on that external one-turn theorem.

The result removes **all horizontal canonical global maximizers** from the possible above-reference alternatives. The remaining sharp scalar obligation is precisely the tilted canonical branch: \(A(j_{\rm high})=1\), \(1/2<A(j_{\rm low})<1\), two strict corners pinned at \(j_-,j_+\), positive endpoint pressures, and the global stationary identity \(2\mathcal P=L_{\rm wing}\). CH7 controls one regular source quarter for width at most \(8/3\), but neither the other quarter nor the tilted sharp value follows from HW1.

The universal scalar claim G1.SD2, the full-turn Gate 1 acceptance target, and the unrestricted two-partial-turn theorem therefore remain **unproved**. The fixed rational checker evaluates only the displayed finite arithmetic certificate and performs no search, Lean/Lake compilation, or CI.
