# An *explicit* far-wide exclusion for complete ambidextrous turns

**Theorem EW1 (effective width gap).**
Every compact connected sofa following both complete
conventional quarter turns from a common incoming
unit-width strip, whose horizontal width obeys

\[
\boxed{2\sqrt2-10^{-9}\le W\le2\sqrt2,}
\tag{EW.1}
\]

has ordinary area

\[
\boxed{|S|\le
\frac{171272278310700620236561}
{104857600000000000000000}
=1.633379729372\ldots
<\frac{41}{25}<M.}
\tag{EW.2}
\]

This replaces the **nonconstructive** positive width gap
from [SWG](strict-competitive-width-gap.md)
by a genuinely explicit (albeit very small) gap.
It is a global exclusion on a positive-width
outer domain; no Romik-reference support closeness,
competitor symmetry, curvature or contact pattern
is assumed. It does not solve the full interior-width
sharp-area problem and does not assert sharpness for
arbitrary partial turns.

The proof quantitatively stabilizes the three-point
switches of [TSW](three-point-switching-fiber-width.md),
then robustly reuses the exact six-angle **actual point**
area certificate from
[EXW](extreme-width-anchored-area.md).

## 1. Switch angles are quantitatively close to 45 degrees

Let \(\varepsilon=2\sqrt2-W\in[0,10^{-9}]\),
\(D=W/2=\sqrt2-\varepsilon/2\),
and choose any actual point \(p=(W/2,y)\in S\).
Choose actual extreme horizontal points
\(P=(0,y_L),Q=(W,y_R)\).
For the lower and reflected upper turns
the two closed-set safe-wall switches from
TSW supply angles \(\theta,\varphi\in(0,\pi/2)\)
with both support depths at most one.

As in TSW.7, the four extreme-point tests give
\(0\le G_D(\theta)+G_D(\varphi)\),
where

\[
G_D(t)=\frac{\sin t+\cos t-D}{\sin t\cos t}.
\]

For the present \(D\ge3/(2\sqrt2)\),
the **exact** scalar maximum TSW.13 is

\[
G_D(t)\le2\sqrt2-2D=\varepsilon
\quad(0<t<\pi/2).
\]

Hence each of \(G_D(\theta)\) and
\(G_D(\varphi)\) is also \(\ge-\varepsilon\).
For either switch angle \(t\),

\[
\sin t+\cos t
\ge D-\varepsilon\sin t\cos t
\ge\sqrt2-\varepsilon.
\]

Write \(z=t-\pi/4\). Then
\(\sin t+\cos t=\sqrt2\cos z\), so
\(1-\cos z\le\varepsilon/\sqrt2\).
For \(|z|\le\pi/4<1\) the elementary Taylor
bound \(1-\cos z\ge z^2/4\) holds. Thus

\[
\boxed{|\theta-\pi/4|,\,
|\varphi-\pi/4|\le2\sqrt\varepsilon.}
\tag{EW.3}
\]

There is no assumption that \(\theta=\varphi\).

## 2. Three anchor heights and four midpoint supports are controlled

By TSW.1, \(W\le2\sqrt2\).
The common vertical span is at most one,
so \(\operatorname{diam}S\le\sqrt{W^2+1}\le3\).
For a fixed sofa point p, its support depth
is therefore 3-Lipschitz in the normal
vector. A normal moved in angle by \(\delta\)
moves by Euclidean distance at most
\(|\delta|\). At each of the **four**
proper 45-degree support normals, the
corresponding depth relative to p is at
most

\[
\boxed{1+6\sqrt\varepsilon.}
\tag{EW.4}
\]

Test EW.4 against Q for the first lower
normal and P for the second. Their
respective dot-product depth lower
bounds are

\[
\frac{D+y_R-y}{\sqrt2},
\qquad
\frac{D+y_L-y}{\sqrt2}.
\]

Repeat with both reflected upper normals
to obtain the reverse inequalities.
Since \(\sqrt2-D=\varepsilon/2\),

\[
\boxed{|y_R-y|,\ |y_L-y|
\le \frac\varepsilon2+6\sqrt2\sqrt\varepsilon
<9\sqrt\varepsilon.}
\tag{EW.5}
\]

For the final strict bound use
\(\sqrt2<17/12\) and
\(\varepsilon\le\sqrt\varepsilon\).

At each of the four 45-degree supporting
normals, the actual support is at least
the corresponding **anchor** support.
By EW.4 and EW.5, its excess over that
anchor support is at most

\[
6\sqrt\varepsilon+
\frac{\varepsilon}{2\sqrt2}
+\frac{9}{\sqrt2}\sqrt\varepsilon
<14\sqrt\varepsilon.
\tag{EW.6}
\]

Multiplying by \(\sqrt2\) to convert each
rotated-wall offset into the corresponding
vertical line intercept gives an error
strictly smaller than \(20\sqrt\varepsilon\).

Let \(d(x)=\min(x,W-x)\).
The two *actual* 45-degree hallway placements,
with the bounded deviations from the
anchors, imply

\[
\boxed{|y'-y|\le
\min(d(x),\sqrt2-d(x))
+30\sqrt\varepsilon}
\tag{EW.7}
\]

for every actual point \((x,y')\in S\).
The estimate comes from pairing the
lower outer/inner interval with the
reflected upper outer/inner interval:
anchor-height errors cost at most
\(9\sqrt\varepsilon\), and moving any
actual wall from its anchor position
costs at most \(20\sqrt\varepsilon\).
The extra unit of rounding slack makes
the displayed coefficient 30.
No side or sign of these errors is
discarded.

## 3. Six fixed rational frames require no unknown support data

Use the **same six** Pythagorean frame
normals \(\mathcal T\) in EXW.4.
Their lower and upper inner-wall
implications follow from the true retained
points P and Q, whose heights now differ
from y by at most \(9\sqrt\varepsilon\).
For the exact
\(b_t(x;W)=\min(((W-x)c-1)/s,(xs-1)/c)\),
these necessary inequalities are

\[
\boxed{|y'-y|\le
-b_t(x;W)+9\sqrt\varepsilon}
\quad\bigl((c,s)\in\mathcal T\bigr).
\tag{EW.8}
\]

The left and right halves have the same
upper bound after replacing unknown
anchor heights by the symmetric error
in EW.5, because \(\mathcal T\) is closed
under swapping cosine and sine.

Intersect EW.7–EW.8 and the original
incoming strip of height at most one.
For the left half \(0\le x\le W/2\),
its fiber has length at most
twice the positive part of

\[
\min\left(\tfrac12,\
x+30\sqrt\varepsilon,\
\sqrt2-x+30\sqrt\varepsilon,\
\{-b_t(x;W)+9\sqrt\varepsilon:t\in\mathcal T\}
\right).
\tag{EW.9}
\]

This is a *true pointwise ordinary-area*
upper bound. No vertical-fiber filling
or candidate comparison theorem is needed.

## 4. Compare with the previous exact rational envelope

Let \(r_{\rm up}(x)\) be the rational
majorant in EXW.10, calculated using
\(q_-<\sqrt2<q_+\) and \(W_-=2q_-\).
For present widths
\(W\ge2\sqrt2-\varepsilon_0\),
\(\varepsilon_0=10^{-9}\),
one may replace the true W in
the negative-of-b affine expression
by \(W_--\varepsilon_0\).
Relative to EXW.10, this raises
each rational-angle branch by at most

\[
\varepsilon_0\max_{t\in\mathcal T}
\frac{\cos t}{\sin t}
\le\frac{12}{5}\varepsilon_0.
\]

Pointwise minima and maxima are
1-Lipschitz in their inputs. Therefore,
using the 30, 9, and 12/5 bounds
above, every left-half interval radius
from EW.9 is at most

\[
r_{\rm up}(x)+
30\sqrt{\varepsilon_0}
+\frac{12}{5}\varepsilon_0
\le r_{\rm up}(x)+33/30000.
\tag{EW.10}
\]

Here
\(\sqrt{\varepsilon_0}<1/30000\)
because \(10^{-9}<1/900000000\).
The added \(3/30000\) covers
the tiny rational width-rounding term.

The positive part is 1-Lipschitz and
the left-half integration interval
lies inside \([0,q_+]\).
The symmetric right-half bound gives

\[
\begin{aligned}
|S|
&\le4\int_0^{q_+}
\bigl[(r_{\rm up}(x))_++33/30000\bigr]dx\\
&\le
\frac{170619797734244653516561}
{104857600000000000000000}
+4q_+\frac{33}{30000}\\
&=
\frac{171272278310700620236561}
{104857600000000000000000}.
\end{aligned}
\tag{EW.11}
\]

The first term is EXW's already **exactly
replayed** 1024-cell rational upper sum.
The second is a simple, uniform,
rational robustness allowance.
The strict margin below 41/25 equals

\[
\boxed{
\frac{694185689299379763439}
{104857600000000000000000}>0.
}
\tag{EW.12}
\]

Finally EXW.15 independently proves
\(41/25<M\) using Romik's defining
cubic and the elementary arctangent
lower estimate. This proves EW1.

## 5. Boundaries and provenance

The theorem now excludes **a positive explicit
interval of horizontal widths**, not just the
single \(W=2\sqrt2\) endpoint.
The coefficient and interval are deliberately
conservative and not claimed optimal.
No numerical optimizer suggested the
interval size: it was obtained from the
exact area certificate's spare margin
and elementary quantitative switching.

The exact arithmetic in EW.11–EW.12
was evaluated with rational fractions.
A full independent mathematical review
of the continuum geometry has not
occurred. The proof does not use Lean,
CI, unknown contact-pattern stability,
symmetry of S, curvature domination,
or any claim that fullturn completion
of partial motions is area-free.

The large interior width range and
arbitrary partial-turn sharp optimum
remain open.
