# A sharp hand theorem for asymmetric horizontal misalignment of Romik's two one-turn halves

**Theorem RH1 (global sharp bound along a genuine asymmetric family).**
Let \(Y>0\) solve \(4Y^3+3Y-1=0\);
let \(\beta=\arctan Y\), \(m=1/(3\sin\beta)\),
\(b=m/2\), and
\[
M=1+4Y^2+\arctan Y.
\]
Let \(U_*\) be Romik's horizontally centered **downward convex
one-turn cap**, and \(N(U_*)\) its complete positive-height
one-turn niche. Put \(T_*=U_*\setminus N(U_*)\).
For every real \(d\) define
\[
E_d=T_*\cap\bigl(\rho T_*+(d,0)\bigr),
\qquad \rho(x,y)=(x,1-y).
\]

Then, with **no restriction on the displacement** \(d\),

\[
\boxed{\qquad
|E_d|\le M-\frac{\min(|d|,m/2)^2}{m(m+1)}
\le M,\qquad}
\tag{RH.1}
\]
and equality with \(M\) holds only for \(d=0\).

This is a **sharp ordinary-area bound at the actual Romik
constant** for an asymmetric two-turn family, not a numerical
upper bound far from that constant. The proof uses a new
planar-slice rearrangement theorem
[SO1](shifted-cap-overlap-rearrangement.md) and the
explicit reference supports, with hand inequalities.
It does **not** establish that arbitrary competitors
are horizontal misalignments of two copies of \(T_*\).
The unrestricted full/partial-turn optimum remains open.

## 1. Exact reference support and rational constants

On \(0\le t\le L=\pi/2\), write \(c=\cos t\),
\(s=\sin t\), and
\[
f(t)=h_{U_*}(c,s),\qquad
g(t)=h_{U_*}(-s,c).
\]
Put
\[
R_0=\frac{\cos\beta}{\sin(3\beta/2+\pi/8)}.
\]
Romik's exact support formulas are
\[
(f,g)=
\begin{cases}
(mc+s/2,\;bs+c/2+1/2),
                   &0\le t\le\beta,\\
(R_0\cos(t/2+\pi/8)+s/2,\;
 R_0\sin(t/2+\pi/8)+c/2),
                   &\beta\le t\le L-\beta,\\
(bc+s/2+1/2,\;ms+c/2),
                   &L-\beta\le t\le L.
\end{cases}
\tag{RH.2}
\]

The following deliberately conservative inequalities are
proved by substituting the rational root bounds
\(298/1000<Y<2981/10000\) into the displayed
algebraic formulas and using alternating Taylor
bounds for sine, cosine and arctangent:
\[
\boxed{
\frac{116}{100}<m<\frac{117}{100},\quad
\frac{289}{1000}<\beta<\frac{29}{100},\quad
\frac{128}{100}<R_0<\frac{131}{100}.
}
\tag{RH.3}
\]

For clarity, \(\beta<29/100\) follows from
\(\arctan x\le x-x^3/3+x^5/5\)
at \(x=2981/10000\); and
\(\beta>289/1000\) follows from
\(\arctan x\ge x-x^3/3\).
For the R bound, put \(\alpha=3\beta/2+\pi/8\).
From \(3.14<\pi<22/7\) and the beta interval,
\(.826<\alpha<.83\).
Alternating Taylor inequalities give
\(\sin\alpha\in(.735,.74)\),
\(\cos\beta\in(.95,.959)\),
hence \(1.28<R_0<1.31\).
The m inequalities follow by squaring
\(m^2=(1+Y^2)/(9Y^2)\).
All comparisons here can be made with
finite rational arithmetic; no reference
decimal or optimization is needed.

The cap U_* is invariant under \(x\mapsto-x\),
has projection \(I=[-m,m]\), top-face interval
\([-b,b]\) at \(y=1\), and contains the entire
rectangle \(I\times[0,1/2]\). Its upper
horizontal sections are consequently
\([-R(y),R(y)]\) for \(y\ge1/2\),
where \(R\) is concave, \(R(1/2)=m\),
and \(R(1)=b\).
These are direct geometric properties of
the support formulas and convexity of U_*.

## 2. The key candidate-specific hand inequality: a triangular niche

Let the positive lower one-turn niche be the
union of its open forbidden quadrants.
At a fixed angle t, its two inner-wall roofs
over horizontal abscissa x are
\[
F_t(x)=\frac{f(t)-1-xc}{s},\qquad
G_t(x)=\frac{g(t)-1+xs}{c},
\]
and the quadrant roof is \(\min(F_t,G_t)\).
Its two walls meet at the inner corner
\[
C_t=(x_C,y_C)
=((f-1)c-(g-1)s,\ (f-1)s+(g-1)c).
\tag{RH.4}
\]

**Lemma RH2 (whole continuum triangular enclosure).**
Every positive-height point of the entire reference
niche satisfies
\[
\boxed{0\le y,\qquad |x|+y\le b.}
\tag{RH.5}
\]
Moreover the niche is entirely below
\[
\boxed{y<41/100<1/2.}
\tag{RH.6}
\]
Both assertions are statements about the **entire
continuous** turning-angle family, not sampled
angles or an assumed stationary contact pattern.

**Proof of the triangular part.**
By horizontal reflection symmetry it suffices
to bound the roof on \(x\ge0\).
First note a universal **reference**
baseline intercept inequality
\[
\boxed{f(t)-1\le b\cos t\quad(0\le t\le L).}
\tag{RH.7}
\]
Indeed \(f(L)=1,f'(L^-)=-b\) and the
open-quarter reference curvature density
\(\rho_f=f''+f\) lies in [0,1]:
it is 0 on the first phase,
\((3R_0/4)\cos(t/2+\pi/8)<(3/4)(131/100)<1\)
on the middle, and \(1/2\) on the final phase.
For \(k(t)=1+b\cos t-f(t)\) one has
\(k(L)=k'(L^-)=0\), \(k''+k=1-\rho_f\ge0\).
Solving this scalar terminal-value equation gives
\[
k(t)=\int_t^L\sin(v-t)(1-\rho_f(v))\,dv\ge0,
\]
proving RH.7. No curvature restriction is
imposed on any *competing sofa* here.

When \(t\in[\pi/4,L]\), RH.7 gives
\[
F_t(x)\le(b-x)\cot t\le b-x
\quad(0\le x\le b),
\]
and \(F_t(x)\le0\) for \(x\ge b\).

For \(0<t\le\pi/4\), the slopes of
\(F_t-(b-x)\) and \(G_t-(b-x)\)
are respectively \(1-\cot t\le0\)
and \(1+\tan t>0\).
Therefore the maximum, over **all x**,
of \(\min(F_t(x),G_t(x))-(b-x)\)
is attained at their crossing, and equals
\[
x_C(t)+y_C(t)-b.
\]
It suffices to prove
\[
\boxed{x_C(t)+y_C(t)<b
\quad(0<t\le\pi/4).}
\tag{RH.8}
\]

For \(0\le t\le\beta\), RH.2 gives
\[
x_C+y_C=(f-1)(c+s)+(g-1)(c-s).
\]
Using \(s<.29\), \(c+s<1.29\),
\(f-1<.17+.145=.315\),
\(g-1\le bs\), \(c-s\in[0,1]\),
and \(b<.585\), yields
\[
x_C+y_C
<(.315)(1.29)+(.585)(.29)
=.576<.58<b.
\tag{RH.9}
\]

For \(\beta\le t\le\pi/4\), set
\(u=3t/2+\pi/8\). Direct substitution
from RH.2, retaining both walls, gives
\[
J(t):=x_C+y_C=
\tfrac12-2\cos t+
R_0(\cos u+\sin u).
\tag{RH.10}
\]
On this interval \(u\in(.826,\pi/2]\);
therefore
\[
J''(t)=2\cos t-
(9R_0/4)(\cos u+\sin u)
<2-\tfrac94<0.
\]
So J is strictly concave and lies below
its tangent at \(t=1/2\).

For the single fixed argument
\(u_0=3/4+\pi/8\in(1.142,1.144)\),
the alternating Taylor bounds give
\[
.4<\cos u_0<.42,\qquad
.9<\sin u_0<.915,
\]
and
\(.47<\sin(1/2)<.5\),
\(\cos(1/2)>7/8\).
With RH.3 these imply
\[
J(1/2)<\tfrac12-2(7/8)
+(131/100)(.42+.915)<\tfrac12
\]
and
\[
|J'(1/2)|=
\left|2\sin(1/2)+
(3R_0/2)(\cos u_0-\sin u_0)\right|
<.1.
\]
Every \(t\in[\beta,\pi/4]\)
satisfies \(|t-1/2|<.3\).
Concavity therefore gives
\[
J(t)\le J(1/2)+J'(1/2)(t-1/2)
<.5+.1(.3)=.53<.58<b.
\tag{RH.11}
\]
Together RH.9–RH.11 prove RH.8,
hence \(n_*(x)\le b-x\) for \(x\ge0\).
Horizontal reflection gives
\(n_*(x)\le b-|x|\) for \(|x|\le b\),
and the earlier wall argument excludes
positive niche outside [-b,b].
This proves RH.5.

**Proof of the height assertion.**
Each inner quadrant lies below its
own corner height
\(y_C(t)=(f-1)s+(g-1)c\).
In the initial phase RH.2 simplifies this to
\[
y_C=(3m/2)sc+\tfrac12-s-\tfrac12c.
\]
Since \(sc\le s<.29\),
\(1-c<t^2/2\), and \(m<1.17\),
\[
y_C<(.755)(.29)+.29^2/4<.241.
\tag{RH.12}
\]
On the middle phase,
\[
y_C(t)=R_0\sin(3t/2+\pi/8)
+\tfrac12-(\sin t+\cos t).
\]
The argument of the sine ranges in
\([\alpha,\pi-\alpha]\), with
\(\alpha>.826\); therefore
\(\sin(3t/2+\pi/8)>.735\).
The second derivative is
\[
y_C''=
-(9R_0/4)\sin(3t/2+\pi/8)
+(\sin t+\cos t)<0.
\]
By the explicit symmetry \(t\mapsto L-t\),
the maximum on the middle phase is at
\(t=\pi/4\), where
\[
y_C(\pi/4)=R_0+\tfrac12-\sqrt2
<1.31+.5-1.4=.41.
\tag{RH.13}
\]
The last phase is the horizontal reflection
of the initial phase. This proves RH.6.
QED.

## 3. Apply the abstract overlap theorem

The support geometry from Section 1 gives
the required outer concave section radius
\(R(y)\) with endpoints \(R(1/2)=m\),
\(R(1)=b=m/2\).
The downward cap contains its full
bottom half-rectangle, while RH2 says
every removed niche section \(N_y\)
lies inside \([-(b-y),b-y]\)
and is empty for \(y\ge.41<1/2\).
Thus the one-turn survivor \(T_*\)
satisfies **all the hypotheses** of
[SO1](shifted-cap-overlap-rearrangement.md).

The abstract theorem immediately yields
\[
|T_*\cap(\rho T_*+(d,0))|
\le
|T_*\cap\rho T_*|
-\frac{\min(|d|,b)^2}{m(m+1)}.
\]
The exact reference construction has
\(T_*\cap\rho T_*=\Sigma\),
Romik's feasible two-turn sofa,
with area \(M\). This proves RH.1.
There is no finite hallway-angle
sampling or width box in this proof.

## 4. The shifted bodies genuinely enter the difficult face class

For \(0<d<1/10\), the intersection
\(E_d\) is a **compact connected feasible
full-two-turn sofa**.

Each one-turn survivor has vertical
interval fibers, and every one of its
fibers contains height \(1/2\), since
the cap contains the full half-height
rectangle and the niche height is
strictly less than \(1/2\).
Consequently the vertical fibers of
\(E_d\) also contain height \(1/2\)
throughout its nonempty horizontal
projection \([d-m,m]\).
They are intervals, so \(E_d\) is
connected. It follows both full canonical
motions as a subset of their respective
one-turn survivors, starting from the
same horizontal incoming strip.

The reference niche has positive bottom
trace precisely on \((-b,b)\), by the
explicit initial/final floor-trace
relations already established for \(\Sigma\).
Thus the reference survivor has
bottom horizontal trace
\([-m,-b]\cup[b,m]\);
its top trace is the cap's
horizontal face \([-b,b]\).
For \(0<d<1/10\), elementary
intersection of the shifted traces yields

\[
\begin{aligned}
E_d\cap\{y=1\}
&=[-b,-b+d]\times\{1\},\\
E_d\cap\{y=0\}
&=[b,b+d]\times\{0\}.
\end{aligned}
\tag{RH.14}
\]

These are *two nondegenerate horizontal
faces at opposite ends*, each of length
exactly d. Because their endpoints are
actual sofa points, the same intervals
are the **actual convex-hull top and
bottom faces**, not merely proposed
cap faces. The horizontal width of
\(E_d\) is \(2m-d>2\).
Thus \(E_d\) belongs to the
opposite-end positive-face class
left open by FD1/PD3, **not** the
previously solved aligned-face class.

As \(d\downarrow0\), translation
continuity in planar \(L^1\)
gives \(|E_d|\to|E_0|=M\).
The explicit strict quadratic bound
RH.1 controls these **genuinely
asymmetric near-optimal sofas**:

\[
\boxed{|E_d|\le
M-\frac{d^2}{m(m+1)}<M
\qquad(0<d<1/10).}
\tag{RH.15}
\]

This explains why excluding opposite
positive faces by a **uniform positive
area gap** is impossible, while proving
a sharp inequality on a nontrivial
subset of that class is possible.

## 5. Remaining global proof obligation

The two one-turn halves of an *arbitrary*
competitive sofa need not be translated
copies of the **same** horizontally
symmetric cap. They can have independent
outer profiles, different positive niches,
nonzero contact-switch defects, and
different outgoing terminal angles.
Neither the abstract SO1 theorem
nor RH1 controls those arbitrary deformations.

The new theorem establishes a global-in-shift
and quantitatively **strict** Romik-area
comparison for one natural asymmetric family.
It is a hand proof of a genuine
sharp-constant subclass, **not** a
hand proof of Romik optimality over all
full/partial ambidextrous sofas.
No Lean formalization, CI, optimizer or
numerical upper-bound search was used.
