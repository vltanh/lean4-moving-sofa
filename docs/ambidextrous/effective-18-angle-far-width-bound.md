# A stronger explicit far-wide ordinary-area exclusion: eighteen rational angles

**Theorem E18.** Every compact connected sofa that completes
both conventional unit-hallway quarter turns from one common
incoming strip and has horizontal width

\[
\boxed{2\sqrt2-10^{-7}\le W\le 2\sqrt2}
\tag{E18.1}
\]

satisfies the *ordinary area* upper bound

\[
\boxed{
|S|\le
\frac{29445615694824921292289629699}
{17993564160000000000000000000}
=1.6364526467904024\ldots
<\frac{41}{25}<M.
}
\tag{E18.2}
\]

Here \(M\) is the exact area of the feasible Romik sofa.
This **widens the explicit excluded width interval by a factor
of 100** compared with the six-angle result
[EW](effective-max-width-exclusion.md), while
relying on the same geometric strategy, not on
a new auxiliary optimization or a numerical guess.

The proof is a self-contained exact finite-angle
upper-area check joined to the **actual**
two-handed support-switching geometry.
Neither a candidate contact pattern, a bound
on competitor curvature, competitor symmetry,
nor a local reference-hull hypothesis is assumed.
It is a **partial** optimality result, not a
global sharp area theorem and not an unrestricted
partial-turn area result.

## 1. The eighteen genuinely visited supporting directions

Use the nine exact primitive Pythagorean triples

\[
\begin{gathered}
(3,4,5),\quad(5,12,13),\quad(8,15,17),\\
(20,21,29),\quad(28,45,53),\quad
(33,56,65),\\
(48,55,73),\quad(65,72,97),\quad
(60,91,109).
\end{gathered}
\tag{E18.3}
\]

For each triple \((a,b,h)\), include
**both** proper normals
\((c,s)=(a/h,b/h)\) and \((b/h,a/h)\).
Thus there are 18 exact rational-angle
frames in the lower turn and their 18
reflected frames in the upper turn.
Every \(c,s\) is strictly positive,
\(c^2+s^2=1\), and both
\(c/s\) and \(s/c\) are at most \(12/5\).
The six old directions from
[EXW](extreme-width-anchored-area.md)
form a subset of this list.

## 2. Exact anchor area at the maximal width

At \(W=2\sqrt2\), the switching equality
from [TSW](three-point-switching-fiber-width.md)
forces the horizontal extreme anchor points and
the midpoint anchor to share one vertical ordinate
\(y_0\). It also forces the true
\(45^\circ\) wall offsets on both turns.
For \(0\le x\le\sqrt2\), the same actual-anchor
argument as EXW.3–EXW.8 bounds the
vertical fiber halfwidth by

\[
r(x)=\min\left(
\frac12,\;x,\;\sqrt2-x,\;
\left\{\max\left(
\frac{1-(2\sqrt2-x)c}{s},
\frac{1-xs}{c}
\right):(c,s)\in\mathcal T_{18}
\right\}
\right).
\tag{E18.4}
\]

Consequently
\(|S|\le4\int_0^{\sqrt2}(r(x))_+\,dx\),
where \(z_+=\max(z,0)\). Inclusion of 12
additional valid frames can only **decrease**
this area majorant.

Take rational
\(q_-=1414213562/10^9<\sqrt2<
q_+=1414213563/10^9\), and
replace \(2\sqrt2\) by \(2q_-\) in
the *first* affine inner-wall branch,
and \(\sqrt2-x\) by \(q_+-x\).
This produces a rational upper
envelope \(r_{\rm up}\ge r\) over
the actual half projection.

Because all affine branch slopes have
absolute value at most \(L=12/5\),
so do the min/max/positive-part
compositions. With \(N=1024\),
\(\delta=q_+/N\) and
\(x_i=(i+1/2)\delta\), the rigorous
upper midpoint sum is

\[
\boxed{
|S|\le4\delta\sum_{i=0}^{N-1}
(r_{\rm up}(x_i))_+ +2Lq_+\delta
= \frac{28393817005577902939649629699}
{17993564160000000000000000000}
=1.5779984861864023\ldots.
}
\tag{E18.5}
\]

The whole sum is **rational** and includes
every cell plus the one-sided
Lipschitz quadrature allowance.

## 3. Quantitative robustness for nearby widths

Set \(\varepsilon=2\sqrt2-W\)
with \(0\le\varepsilon\le10^{-7}\).
For each of the **two true turns**, apply
the safe-wall first-intersection argument
to an actual midpoint-fiber point.
The exact TSW midpoint function has maximum
\(G_D\le\varepsilon\) on this range,
where \(D=W/2\). Since the lower and upper
switch contributions have nonnegative sum,
each individually is at least
\(-\varepsilon\). This forces the two
switch angles to lie within
\(2\sqrt\varepsilon\) of \(\pi/4\)
by the elementary identity
\(\sin t+\cos t=\sqrt2\cos(t-\pi/4)\).

The uniform diameter bound
\(\operatorname{diam}S\le3\)
is already supplied by TSW.1 and
the incoming span \(H\le1\).
Thus every pertinent support depth
moves by at most \(6\sqrt\varepsilon\)
between the actual switch and
the \(45^\circ\) frame.
The retained left/right anchor heights
are within \(9\sqrt\varepsilon\)
of the midpoint anchor height.
Keeping *both* true outer and
inner \(45^\circ\) wall constraints
as in EW Section 2 gives
a symmetric radius error at most
\(30\sqrt\varepsilon\) around the
exact-width envelope.

At the 18 additional rational frames,
there is no approximated support:
testing the *actual two horizontal
extreme anchors* gives the
necessary lower/upper interval
halfwidth
\[
\max\left(
\frac{1-(W-x)c}{s},
\frac{1-xs}{c}
\right)+9\sqrt\varepsilon.
\]
Since \(W\ge2q_--\varepsilon\),
comparison with the rational
max-width branches incurs at most
\((12/5)\varepsilon\).
Therefore the entire true
radius for \(0\le x\le W/2\) is
bounded by

\[
r_{\rm up}(x)+30\sqrt\varepsilon
+\tfrac{12}{5}\varepsilon.
\tag{E18.6}
\]

For the **explicit interval** \(\varepsilon\le10^{-7}\),

\[
\sqrt\varepsilon<1/3000,\qquad
30\sqrt\varepsilon+\tfrac{12}{5}\varepsilon
<\tfrac{31}{3000}.
\tag{E18.7}
\]

The angle family is closed under \(c\leftrightarrow s\),
so the same robust bound applies on the horizontally
reflected right half. Fubini, the positive-part
1-Lipschitz property and E18.5 yield

\[
\begin{aligned}
|S|
&\le4\int_0^{q_+}
\left[(r_{\rm up}(x))_+
+\frac{31}{3000}\right]dx\\
&\le
\frac{28393817005577902939649629699}
{17993564160000000000000000000}
+4q_+\frac{31}{3000}\\
&=
\frac{29445615694824921292289629699}
{17993564160000000000000000000}.
\end{aligned}
\tag{E18.8}
\]

The **exact positive rational** gap below
\(41/25=1.64\) equals

\[
\boxed{
\frac{63829527575078707710370301}
{17993564160000000000000000000}>0.
}
\tag{E18.9}
\]

EXW Section 4 independently proves
\(41/25<M\) from the defining cubic
of the candidate. This proves E18.2.

## 4. Checker and trust boundary

[check_wide_18_angle.py](computer-assisted/check_wide_18_angle.py)
is a standard-library-only, deterministic
Fraction checker. It verifies both
root enclosures, nine Pythagorean
identities, the global affine slope
bound \(12/5\), all 1024 rational
midpoint cells, the full Lipschitz
allowance, the \(31/3000\)
robust perturbation cushion, and
the strict exact rational comparison.
It passed in a short local execution.

Executed source SHA-256:
`c5cf231519eb4ff6b457b06f7e49ce108db3ded610b6c60d802a9dfe2fac2ab1`.
Git blob:
`68a3a1a4f896215f630eb96460a7ac73137e5887`.
The committed Git blob was fetched and
checked identical to the executed source.
The finite script is not a verifier of
all geometric lemmas in Sections 1–3.
Those remain self-reviewed mathematical
arguments. No Lean/Lake build,
CI, long optimizer run, or independent
referee review was performed.

**Remaining frontier:** this explicit
upper-width exclusion still covers
only the outermost \(10^{-7}\)
of the width domain. The known
analytic width gate below \(W=2\)
and the lower-area boundary lemmas
do **not** cover the whole intervening
class. No sharp global value or
unrestricted partial-turn bound
is asserted here.
