# Gate 2: a shorter companion prefix from a weighted support moment

Written mathematical proof, October 10, 2026. This note strengthens
the conditional companion-prefix exclusion in
[TP, Section 5](gate2-terminal-facet-and-prefix-reduction.md). It uses
the all-angle width bound [WC](gate2-three-angle-width-cut.md), the
terminal mass and top-projection bounds TP.10--11, and the regular
charged-wing measure and terminal occupation theorem
[PS](gate2-partial-endpoint-source-and-green.md).

The conclusion is conditional on a companion-curvature estimate on
an explicitly shorter initial interval. Curvature exceeding one after
that interval does not weaken the comparison. A weighted allowance for
excess inside the interval is also recorded. No reflection of the
partial spatial objective or common shape/angle terminal occupation is
assumed. Labels MP are local.

## 1. Geometric setting and the conditional exclusion

Suppose an above-reference partial-cap maximum exists. Choose its
largest terminal angle and the canonical representative used in TP.
All-width [AT](gate2-all-width-terminal-angle-exclusion.md), TP, and WC
give

\[
I=[-2C,2C],\qquad J=[-C,C],\qquad
\frac12<C<\frac{37}{50},\qquad
0<c:=\cos a<\frac3{\sqrt{73}},\qquad s:=\sin a.
\tag{MP.1}
\]

Retain TP's original, unreflected orientation and notation:

\[
A(-C)=1-h_L,\quad A(C)=1-h_R,\quad
\min(h_L,h_R)=0,\quad H=1-h_R,
\]
\[
d=\frac{1-Hs}{c},\qquad w=c-d,\qquad
0<d<c,\qquad 0<w<\frac c2,
\]
\[
T_L+2T_R\le d,\qquad m\le w.
\tag{MP.2}
\]

Here \(T_L,T_R\) are the height-one top overhangs and \(m\) is the
horizontal length of the charged first terminal facet. The negative
tilt branch already completed by the negative-tilt theorem has been
discarded, so \(s<H\le1\). The actual outgoing wall is

\[
R_a(-C+z)=\frac cs(2C+T_R-d-z).
\tag{MP.3}
\]

Let \(g\) be the support of the left charged wing. In positive tilt
this is the low-wing surrogate; in the other two signs it is the
actual companion support. Its initial data are

\[
g(0)=1-h_L,\qquad g'(0+)=C+T_L.
\tag{MP.4}
\]

Write \(v=g''+g\ge0\) for its regular curvature density. PS, after
removing the uncharged central facet when required, makes \(g\)
continuously differentiable on the proper used interval and gives no
interior singular curvature or companion terminal atom. All support
identities below are consequently valid by absolute continuity.

Put

\[
A_0=C-T_L,\qquad \theta=\arcsin A_0,\qquad
G(x)=\sqrt{1-x^2},\qquad K(x)=\frac{x}{\sqrt{1-x^2}},
\qquad \lambda=K(A_0).
\tag{MP.5}
\]

The possible weighted early excess is

\[
\mathcal E_\theta
=\int_0^\theta (v(r)-1)_+
\bigl(\lambda\cos r-\sin r\bigr)\,dr.
\tag{MP.6}
\]

The kernel is nonnegative on this interval. The conditional theorem is

\[
\boxed{\mathcal E_\theta\le\frac{39}{4400}c
\quad\Longrightarrow\quad\text{no such maximum exists}.}
\tag{MP.7}
\]

In particular, it suffices that

\[
\boxed{v\le1\text{ a.e. on }(0,\arcsin(C-T_L)).}
\tag{MP.8}
\]

The stronger assumption \(v\le1\) on \((0,\arcsin C)\) is often
more convenient. Both intervals are shorter than the old TP.15
interval \((0,\arcsin(C+w))\).

## 2. Every relevant companion-wall maximum is interior and localized

First observe that

\[
0<C-T_L<C+w\le C+\frac c2<s<1.
\tag{MP.9}
\]

The first inequality follows from \(T_L\le d<c<C\). For the last
nontrivial inequality, its left side minus \(\sqrt{1-c^2}\) increases
with both \(C\) and \(c\). At their enlarged endpoints it is
negative because

\[
\frac{37}{50}+\frac3{2\sqrt{73}}
<\frac8{\sqrt{73}},\qquad
37^2\,73=99937<105625=325^2.
\]

For \(x=-C+z\), \(0\le z\le w\), define

\[
S_t(x)=\frac{g(t)-1+x\sin t}{\cos t}\qquad(0\le t\le a).
\]

The omitted high charged wing in the positive-tilt surrogate
contributes only nonpositive companion walls on \(J\): each of its
points has \(X\ge C\), \(Y\le1\), and its wall is at most
\(1-\sec t+(x-C)\tan t\le0\). The affine middle segment is
controlled by its endpoints: the low endpoint belongs to the left
wing and the high endpoint has the same nonpositive wall bound.
Therefore in every sign the positive
visited niche satisfies

\[
n_a(x)\le\left[\max_{0\le t\le a}S_t(x)\right]_+.
\tag{MP.10}
\]

The shifted companion support point has coordinates

\[
D_x=-g'\cos t-(g-1)\sin t,\qquad
D_y=-g'\sin t+(g-1)\cos t.
\tag{MP.11}
\]

Its actual outer abscissa is \(X=D_x-\sin t\ge-2C\), and direct
differentiation gives

\[
S'_t(x)=\frac{x-D_x(t)}{\cos^2t},\qquad
D_x'=(1-v)\cos t,\qquad D_y'=(1-v)\sin t.
\tag{MP.12}
\]

In particular \(S'_t(x)<0\) whenever \(\sin t>C+z\). Since
\(C+z<s\), a positive maximum of this companion-wall family is
attained in \((0,a)\); its value at zero is \(-h_L\le0\), and
the function is strictly decreasing after \(\arcsin(C+z)\).
At a positive maximizing angle \(t\),

\[
D_x(t)=x,\qquad S_t(x)=D_y(t),\qquad
\sin t\le C+z.
\tag{MP.13}
\]

This argument does not require the terminal companion wall to be
negative. It also handles a maximum at the joining point
\(\arcsin(C+z)\), which remains an interior differentiability point.

## 3. A weighted moment needs only the shorter prefix

MP.4 gives \(D_x(0)=-C-T_L\), \(D_y(0)=-h_L\). At an angle
satisfying MP.13, integration of MP.12 yields

\[
D_y(t)+h_L-\lambda(T_L+z)
=\int_0^t(1-v(r))\bigl(\sin r-\lambda\cos r\bigr)\,dr.
\tag{MP.14}
\]

The kernel changes sign precisely at \(r=\theta\). Before
\(\theta\), the integrand is at most
\((v-1)_+(\lambda\cos r-\sin r)\). After \(\theta\), its
upper bound is simply \(\sin r-\lambda\cos r\), since \(v\ge0\).
Consequently, when \(t\ge\theta\),

\[
D_y(t)+h_L
\le G(A_0)-\cos t+\lambda(C+z-\sin t)
+\mathcal E_\theta.
\tag{MP.15}
\]

The right side apart from the excess has derivative
\(\sin t-\lambda\cos t\ge0\) on \([\theta,\pi/2)\).
Since \(t\le\arcsin(C+z)\), it is at most
\(G(A_0)-G(C+z)\). If \(t<\theta\), MP.14 instead gives
\(D_y+h_L\le\lambda(T_L+z)+\mathcal E_\theta\); monotonicity
of \(K\) gives the same conclusion because

\[
\lambda(T_L+z)=K(A_0)(C+z-A_0)
\le\int_{A_0}^{C+z}K(q)\,dq
=G(A_0)-G(C+z).
\]

Using MP.10 also when there is no positive maximum proves

\[
\boxed{
n_a(-C+z)
\le\bigl[-h_L+G(C-T_L)-G(C+z)+\mathcal E_\theta\bigr]_+
\le G(C-T_L)-G(C+z)+\mathcal E_\theta.}
\tag{MP.16}
\]

The last right side is nonnegative. This is why curvature exceeding
one after \(\theta\) carries no adverse error: its weighted kernel
in MP.14 is already nonnegative.

## 4. Reduce the terminal comparison to one symmetric average

The outgoing wall decreases with \(z\), while the circle difference
in MP.16 increases. It is enough to compare them at \(z=w=c-d\).
Using \(T_R\ge0\) and \(T_L\le d\), their gap is at least

\[
\frac cs(2C-c)-\bigl[G(C-d)-G(C+c-d)\bigr].
\tag{MP.17}
\]

Moreover \(H\le1\) implies

\[
d\ge\delta:=\frac{1-s}{c}=\frac c{1+s}.
\]

The bracket in MP.17 decreases with \(d\), since its derivative is
\(K(C-d)-K(C+c-d)<0\). It is therefore at most its value at
\(d=\delta\). Put

\[
\eta=\delta-\frac c2
=\frac{c^3}{2(1+s)^2}\ge\frac{c^3}{8},\qquad
\mathcal A_q(y)=\frac1q\int_{y-q/2}^{y+q/2}K(x)\,dx.
\tag{MP.18}
\]

The desired normalized gap is bounded below by

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta).
\tag{MP.19}
\]

On every interval used below, \(K\) is increasing and convex.
Thus \(\mathcal A_q(y)\) is increasing in both \(y\) and \(q\),
and is convex in \(y\). Width monotonicity follows, for example,
by writing the average on \([-1/2,1/2]\) and pairing the positive
and negative integration variables; the derivative in \(q\) is
nonnegative because \(K'\) is increasing. A linear function of
\(C\) minus either fixed-width average is therefore concave in
\(C\), so its lower bound can be checked at the two width endpoints.

## 5. Exact scalar margin on the complete remaining angle interval

### 5.1 The range \(0<c\le1/3\)

Here

\[
\mathcal A_c(C-\eta)\le\mathcal A_{1/3}(C).
\]

Also \((2C-c)/\sqrt{1-c^2}\) decreases with \(c\), since its
derivative is \((2Cc-1)/(1-c^2)^{3/2}<0\). The bound
\(\sqrt2<99/70\) gives

\[
\frac{2C-c}{s}>\frac{35}{33}\left(2C-\frac13\right).
\tag{MP.20}
\]

At \(C=1/2\),

\[
\mathcal A_{1/3}(1/2)=2\sqrt2-\sqrt5
<\frac{23}{35}<\frac23,
\]

using \(\sqrt2<10/7\), \(\sqrt5>11/5\). The gap from the
right side of MP.20 is greater than
\(70/99-2/3=4/99\). At \(C=37/50\),

\[
\mathcal A_{1/3}(37/50)
=\frac{8\sqrt{59}-\sqrt{1001}}{25}<\frac65,
\]

using \(\sqrt{59}<77/10\), \(\sqrt{1001}>158/5\). The gap
is greater than \(602/495-6/5=8/495\). All four radical bounds
follow by squaring positive rationals. Concavity in \(C\) now gives

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta)>\frac8{495}
>\frac{39}{4400}.
\tag{MP.21}
\]

### 5.2 The range \(1/3\le c\le3/\sqrt{73}\)

Use

\[
\eta\ge\frac1{216},\qquad c<q:=\frac{44}{125},\qquad
s\le\frac{2\sqrt2}{3}<\frac{33}{35}.
\]

The rational angle bound follows from
\(9\cdot15625=140625<141328=1936\cdot73\). Thus

\[
\mathcal A_c(C-\eta)\le\mathcal A_q(C-1/216),\qquad
\frac{2C-c}{s}>\frac{35}{33}\left(2C-\frac{44}{125}\right).
\tag{MP.22}
\]

At \(C=1/2\), the two integration endpoints are
\(8623/27000\) and \(18127/27000\). They satisfy

\[
G(8623/27000)<\frac{19}{20},\qquad
G(18127/27000)>\frac{37}{50}.
\]

For the first comparison, use
\(8623/27000>5/16\) and \((5/16)^2>1-(19/20)^2\).
For the second, use
\(18127/27000<84/125\) and
\((84/125)^2+(37/50)^2<1\). Hence

\[
\mathcal A_q(1/2-1/216)<\frac{105}{176}<\frac23.
\]

Its gap from the linear expression in MP.22 is greater than
\(189/275-2/3=17/825\).

At \(C=37/50\), the endpoints are
\(15103/27000\) and \(24607/27000\). The exact inequalities

\[
G(15103/27000)<\frac{829}{1000},\qquad
G(24607/27000)>\frac{411}{1000}
\]

follow respectively from

\[
15103^2=228100609>228001311
=27000^2\bigl(1-(829/1000)^2\bigr),
\]
\[
24607^2=605504449<605856591
=27000^2\bigl(1-(411/1000)^2\bigr).
\]

Therefore

\[
\mathcal A_q(37/50-1/216)<\frac{19}{16},
\]

whose gap from MP.22 is greater than
\(329/275-19/16=39/4400\). Concavity in \(C\) yields

\[
\frac{2C-c}{s}-\mathcal A_c(C-\eta)>\frac{39}{4400}
\tag{MP.23}
\]

throughout this second range. Together, MP.17--23 give the uniform
strict terminal margin

\[
\boxed{
R_a(-C+z)-\bigl[G(C-T_L)-G(C+z)\bigr]
>\frac{39}{4400}c
\quad(0\le z\le w).}
\tag{MP.24}
\]

## 6. The occupation contradiction

If MP.7's excess bound holds, MP.16 and MP.24 imply
\(R_a>n_a\) on the entire interval \([-C,-C+w]\).
The right endpoint lies in the interior of \(J\), and the strict
gap persists a positive distance farther right by continuity. Hence
the strict terminal exposure set has measure greater than \(w\).

PS.34--35 give a terminal occupation equal to one on that strict
exposure set, with total occupation \(m\). This contradicts
\(m\le w\) from TP.10. The contradiction proves MP.7--8 for
positive, horizontal, and every remaining negative middle tilt.

Keeping the nonpositive term \(-h_L\) in MP.16 would allow the
slightly larger error \(\mathcal E_\theta\le h_L+39c/4400\).
The uniform version MP.7 suffices for a prefix theorem stated without
separating the tilt signs. Establishing such a curvature or weighted
excess estimate remains a separate input; this note does not assert
it throughout the full angle range.

## 7. A concrete cubic allowance for a late excess tail

The following modular criterion is useful when a reflected-support
estimate controls an excess tail rather than proving the exact unit
prefix. Suppose additionally that \(\cot a\ge1/8\), and assume

\[
(v(t)-1)_+\le\frac{19}{25}
\bigl(t-(\pi/2-91/100)\bigr)_+
\quad\text{for a.e. }0<t<\theta.
\tag{MP.25}
\]

Then MP.7's weighted allowance holds. Indeed, its kernel has the exact
form

\[
\lambda\cos t-\sin t
=\frac{\sin(\theta-t)}{\cos\theta}.
\]

Put \(t_0=\pi/2-91/100\) and
\(\ell=(\theta-t_0)_+\). Since \(C-T_L\le37/50\),

\[
\cos\theta>\frac23,\qquad
\ell<\frac{91}{100}-\frac{147}{200}=\frac7{40}.
\tag{MP.26}
\]

The first assertion uses \(1-(37/50)^2>4/9\). For the second,
the Taylor lower bound \(\cos x\ge1-x^2/2+x^4/25\) on
\([0,1]\) gives

\[
\cos(147/200)>\frac{37}{50},\qquad
1-\frac{(147/200)^2}{2}+\frac{(147/200)^4}{25}
-\frac{37}{50}=\frac{62448881}{40000000000}>0.
\]

Thus \(\arccos(C-T_L)>147/200\), proving MP.26. If
\(\ell=0\), MP.25 gives \(\mathcal E_\theta=0\). Otherwise,
\(\sin(\theta-t)\le\theta-t\), and a direct integral yields

\[
\begin{aligned}
\mathcal E_\theta
&\le\frac{19}{25\cos\theta}
\int_{t_0}^{\theta}(t-t_0)(\theta-t)\,dt\\
&=\frac{19\ell^3}{150\cos\theta}
<\frac{19}{100}\left(\frac7{40}\right)^3
=\frac{6517}{6400000}.
\end{aligned}
\tag{MP.27}
\]

Finally \(\cot a\ge1/8\) implies
\(c\ge1/\sqrt{65}>3/25\). Therefore

\[
\frac{6517}{6400000}<\frac{117}{110000}
<\frac{39c}{4400},\qquad
\frac{117}{110000}-\frac{6517}{6400000}
=\frac{3193}{70400000}>0.
\tag{MP.28}
\]

This proves the conditional exclusion from MP.25. The reflected
curvature estimate that supplies MP.25 is a separate obligation; the
cubic payment itself uses only MP's geometric hypotheses.
