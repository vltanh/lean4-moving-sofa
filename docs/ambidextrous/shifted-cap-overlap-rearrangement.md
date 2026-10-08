# An exact rearrangement theorem for horizontally displaced two-turn caps

**Theorem SO1 (sharp translation penalty, pure hand proof).**
Let \(m>0\), \(b=m/2\), and \(0<h<\min(b,1/2)\).
Suppose \(T\subset\mathbb R\times[0,1]\) is a compact set
whose horizontal sections satisfy the following conditions:

* For \(0\le y\le1/2\),
  \(T_y=[-m,m]\setminus N_y\), where \(N_y\) is
  a measurable set, \(N_y=\varnothing\) for \(y\ge h\),
  and
  \[
  \boxed{N_y\subseteq[-(b-y),b-y]\quad(0\le y<h).}
  \tag{SO.1}
  \]
  The fibers \(N_y\) do **not** have to be intervals.
* For \(1/2\le y\le1\),
  \(T_y=[-R(y),R(y)]\), where \(R\) is nonnegative,
  concave, \(R(1/2)=m\), and \(R(1)=b\).

Write \(\rho(x,y)=(x,1-y)\), and let
\[
\Phi(d)=\left|T\cap\bigl(\rho T+(d,0)\bigr)\right|.
\]
Then for **every real horizontal displacement** \(d\),

\[
\boxed{\Phi(d)\le\Phi(0)
-\frac{\min(|d|,b)^2}{m(m+1)}.}
\tag{SO.2}
\]

This is a global-in-\(d\), strictly sharp-at-\(d=0\)
comparison for the whole stated class. It is not an
unrestricted moving-sofa theorem. It uses ordinary
planar Lebesgue area, not an auxiliary signed functional
or a sampled hallway area.

## 1. One-dimensional overlap loss

For \(a\ge c\ge0\), let
\(I_a=[-a,a]\), \(I_c=[-c,c]\), and
\[
L_{a,c}(d)=|I_a\cap(I_c+d)|.
\]
For \(d\ge0\), elementary interval intersection gives
\[
L_{a,c}(d)=
\begin{cases}
2c,&0\le d\le a-c,\\
a+c-d,&a-c\le d\le a+c,\\
0,&d\ge a+c.
\end{cases}
\]
Thus the loss
\[
D_{a,c}(d)=L_{a,c}(0)-L_{a,c}(d)
\]
is nonnegative, Lipschitz and absolutely continuous,
with derivative, for almost every \(d>0\),
\[
\boxed{D'_{a,c}(d)=
\mathbf1_{\{a-c<d<a+c\}}.}
\tag{SO.3}
\]

Let \(I_y=[-R(1-y),R(1-y)]\)
for \(0\le y\le1/2\). The full lower half
of \(T\) is \([-m,m]\) with the notch
\(N_y\) removed; the corresponding upper
half at height \(1-y\) is \(I_y\).
Fubini, with the reflected counterpart,
gives
\[
\Phi(d)
=2\int_{1/2}^{1}L_{m,R(z)}(d)\,dz
-\int_0^{h}\!\!\left(
|N_y\cap(I_y+d)|+
|N_y\cap(I_y-d)|\right)\,dy.
\tag{SO.4}
\]
The first identity uses only the upper sections'
horizontal symmetry. The two notch terms need
not be equal; in particular no symmetry of
\(N_y\) is assumed.

Because \(R(1-y)\ge b\ge b-y\),
SO.1 implies \(N_y\subseteq I_y\).
Both notch terms at displacement zero are
therefore \(|N_y|\). For any displacement \(d\),
\[
|N_y|-|N_y\cap(I_y\pm d)|
\le
|I_{b-y}|-|I_{b-y}\cap(I_y\pm d)|
=D_{R(1-y),\,b-y}(|d|).
\]
Subtract SO.4 from its zero-displacement version:
\[
\boxed{\begin{aligned}
\Phi(0)-\Phi(d)
&\ge F(|d|),\\
F(t)&=
2\int_{1/2}^1D_{m,R(z)}(t)\,dz
-2\int_0^hD_{R(1-y),\,b-y}(t)\,dy.
\end{aligned}}
\tag{SO.5}
\]

## 2. Concavity pays the entire possible notch gain

Since \(R\) is concave, its graph lies **above**
the chord between \((1/2,m)\) and \((1,b)\):
\[
\boxed{R(z)\ge m-m(z-1/2)
\quad(1/2\le z\le1),}
\tag{SO.6}
\]
using \(b=m/2\). Equivalently,
\[
R(1-y)\ge b+my\quad(0\le y\le1/2).
\tag{SO.7}
\]

Differentiate the two integrals in SO.5 under
the integral sign, permissible by SO.3 and
dominated convergence for a.e. \(t>0\).
Let \(A(t)\) be the measure of upper-section
heights \(z\in[1/2,1]\) with
\(m-R(z)<t<m+R(z)\).
Let \(B(t)\) be the measure of lower-notch
heights \(y\in[0,h]\) with
\(R(1-y)-(b-y)<t<R(1-y)+(b-y)\).
Then
\[
F'(t)=2(A(t)-B(t))
\quad\text{for almost every }t>0.
\tag{SO.8}
\]

For \(0<t<b\), SO.6 implies that
**every** \(z\in(1/2,\,1/2+t/m)\)
is counted in \(A(t)\). Indeed
\(m-R(z)\le m(z-1/2)<t\), and
\(t<b<m+R(z)\). Therefore
\[
A(t)\ge t/m.
\tag{SO.9}
\]

On the other hand SO.7 implies
\[
R(1-y)-(b-y)\ge (m+1)y.
\]
Every y counted in B(t) therefore satisfies
\(y<t/(m+1)\), whence
\[
\boxed{B(t)\le t/(m+1).}
\tag{SO.10}
\]
Combining,
\[
F'(t)\ge
2t\left(\frac1m-\frac1{m+1}\right)
=\frac{2t}{m(m+1)}
\quad\text{a.e. }0<t<b.
\]
Since \(F(0)=0\),
\[
\boxed{F(t)\ge t^2/[m(m+1)]\quad(0\le t\le b).}
\tag{SO.11}
\]

For \(b<t<m+b\), **every**
\(z\in[1/2,1]\) is counted in A(t),
because \(m-R(z)\le m-b=b<t\)
and \(t<m+b\le m+R(z)\).
Thus \(A(t)=1/2\), while
\(B(t)\le h<1/2\), and \(F'(t)>0\).
For \(t\ge m+b\), no y can contribute
to B(t), since
\(R(1-y)+(b-y)\le m+b\);
hence \(F'(t)=2A(t)\ge0\).
Therefore \(F\) is nondecreasing for
\(t\ge b\), and
\[
F(t)\ge F(b)\ge b^2/[m(m+1)].
\tag{SO.12}
\]
SO.5, SO.11 and SO.12 prove SO.2
for all \(d\), with strict inequality
relative to \(\Phi(0)\) whenever \(d\ne0\).
QED.

## 3. Significance and exact boundary

This theorem is a genuine ordinary-area
**rearrangement inequality** for two
**horizontally offset, vertically reflected**
copies of a nonconvex one-turn survivor.
The notch can have arbitrary measurable
horizontal sections; it does not need
a symmetric or piecewise smooth boundary.
Only its **triangular containment** SO.1
matters. The two upper outer sections
are controlled by the single concavity
condition SO.6.

The inequality is *sharp in its equality
location*, meaning zero relative shift
is a strict global maximizer. The
quadratic coefficient is a conservative
hand estimate, not claimed optimal.

For applying this to the sharp moving-sofa
constant \(M\), one must separately prove
that the reference one-turn survivor has
the stipulated triangular niche containment,
bottom half-rectangle and symmetric
concave upper cap; those are checked in
[the companion reference note]
(romik-horizontal-misalignment-sharp-bound.md).
SO1 alone is not a general inequality
for arbitrary pairs of distinct caps,
arbitrary motions or unknown contact patterns.

No numerical optimizer, Lean formalization
or certified area search is used.
