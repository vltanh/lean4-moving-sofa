# Exact ordinary-area exclusion at maximal ambidextrous width

**Theorem EXW1.** Let S be compact and connected, contained in
an incoming horizontal strip of height H<=1, and capable of both
complete conventional quarter turns. If its horizontal width is
W=2 sqrt(2), then

\[
\boxed{|S|\le
\frac{170619797734244653516561}
{104857600000000000000000}
<\frac{41}{25}<M.}\tag{EXW.1}
\]

Thus Romik's feasible candidate wins strictly against **all full-turn
sofas at the maximal possible horizontal width**. This is a
boundary-stratum area theorem, not unrestricted optimality and
not an area theorem for all partial turns.

The proof uses only (i) three actual retained anchor points
forced by [the TSW switching equality](three-point-switching-fiber-width.md),
(ii) the exact two forced 45-degree hallway placements,
(iii) six additional rational-angle **inner-wall** constraints
from these same anchors, and (iv) a rigorous rational
1024-cell area upper sum. There is no support curvature,
candidate neighborhood, symmetry assumption, auxiliary
one-cap maximization, or untrusted global optimizer.

## 1. Equality in the width theorem fixes the 45-degree placements

Translate the horizontal projection of S to [0,W].
At W=2 sqrt(2), the equality discussion in TSW gives
three **actual** sofa points

\[
P=(0,y_0),\quad C=(\sqrt2,y_0),\quad
Q=(2\sqrt2,y_0)\quad\text{in }S.
\tag{EXW.2}
\]

The vertical fiber at the midpoint is a singleton. Both
opposite-handed full-turn safe-wall switches at C must
occur at angle pi/4. At those two switches, the anchor
support depths are already exactly one and both true
depths are at most one. Therefore the **true**
supports at both proper 45-degree hallway frames
equal the anchor supports; no unobserved point can
raise those four supports.

Put \(d(x)=\min(x,W-x)\). Solve the two lower and
two upper 45-degree hallway wall inequalities
at their **forced** offsets. Every (x,y) in S obeys

\[
\boxed{
y_0-d(x)\le y\le y_0+d(x),\qquad
y_0+d(x)-\sqrt2\le y\le
y_0-d(x)+\sqrt2.
}
\tag{EXW.3}
\]

Consequently the two 45-degree snapshots alone
give a centered interval of halfwidth
\(\min(d(x),\sqrt2-d(x))\).
These are actual placements of the moving hallway,
not merely candidate support functions.

## 2. Six Pythagorean-triple angles and anchored inner cuts

Take the following six pairs (cos t,sin t),
which all belong to the full lower and upper
conventional quarter-turn intervals:

\[
\mathcal T=\left\{
(3/5,4/5),(4/5,3/5),
(5/13,12/13),(12/13,5/13),
(8/17,15/17),(15/17,8/17)
\right\}.
\tag{EXW.4}
\]

For any one frame with c=cos t>0, s=sin t>0,
the actual lower support depths at (x,y) are
at least the corresponding depths measured
from the **actual** anchors Q and P.
Since at least one inner-wall depth must be
at most one, one of the two anchored depths
must also be at most one. Explicitly,

\[
y\ge y_0+b_t(x),\qquad
b_t(x)=\min\left(
\frac{(W-x)c-1}{s},\frac{xs-1}{c}
\right).
\tag{EXW.5}
\]

For the reflected upper-handed hallway, the
same two anchored inequalities imply
\(y\le y_0-b_t(x)\). Hence the allowed
vertical interval must satisfy

\[
\boxed{|y-y_0|\le-b_t(x)}
\quad\text{for all }(c,s)\in\mathcal T.
\tag{EXW.6}
\]

When the right-hand side is negative this
means the interval is empty, as it should.
No assumption was made about the other
support points at these six orientations.

The incoming strip has vertical length at
most one. Its intersection with an arbitrary
centered interval \([y_0-r,y_0+r]\) can
have length at most \(2\min(1/2,r)_+\),
regardless of where the original incoming
strip lies relative to \(y_0\). Thus an
area *upper bound* may use the centered
length-one strip without modifying S.

For \(0\le x\le\sqrt2\), define

\[
r(x)=
\min\left(
\tfrac12,\;x,\;\sqrt2-x,\;
\{-b_t(x):(c,s)\in\mathcal T\}
\right).
\tag{EXW.7}
\]

The actual vertical fiber has length
at most \(2(r(x))_+\), with
\(z_+=\max(0,z)\).
The angular set is closed under swapping
cosine and sine, so the corresponding
bound on the right half is its horizontal
reflection. Fubini yields

\[
\boxed{|S|\le4\int_0^{\sqrt2}(r(x))_+\,dx.}
\tag{EXW.8}
\]

Connectedness supplied C via TSW;
**vertical-fiber convexity is not needed**
here. Even a disconnected fiber has
Lebesgue measure at most its containing
interval's length.

## 3. Rational majorant and exact Lipschitz upper sum

Choose

\[
q_-=\frac{1414213562}{10^9}
<\sqrt2<
q_+=\frac{1414213563}{10^9},
\qquad W_-=2q_-.
\tag{EXW.9}
\]

Squaring these positive rationals certifies
both strict comparisons. For rational
\(0\le x\le q_+\), set

\[
r_{\rm up}(x)=
\min\left(
\tfrac12,\;x,\;q_+-x,\;
\left\{
\max\left(
\frac{1-(W_--x)c}{s},
\frac{1-xs}{c}
\right):(c,s)\in\mathcal T
\right\}
\right).
\tag{EXW.10}
\]

For \(0\le x\le\sqrt2\), one has
\(r(x)\le r_{\rm up}(x)\):
the upper \(\sqrt2-x\) term uses
\(q_+>\sqrt2\), while replacing
\(W=2\sqrt2\) by \(W_-<W\)
increases the first negative-of-b
branch. All min/max operations
preserve these one-sided inequalities.

Every affine branch in EXW.10 has
slope with absolute value at most
\(L=12/5\). Pointwise min, max,
and positive part preserve this
common Lipschitz constant. Divide
\([0,q_+]\) into N=1024 equal cells,
\(\delta=q_+/N\), with midpoints
\(x_i=(i+1/2)\delta\).
The exact midpoint-rule upper estimate is

\[
\begin{aligned}
|S|
&\le4\int_0^{q_+}(r_{\rm up}(x))_+\,dx\\
&\le4\delta\sum_{i=0}^{N-1}
(r_{\rm up}(x_i))_+
+2Lq_+\delta.
\end{aligned}
\tag{EXW.11}
\]

All data in the final expression are
rational, including the angle normals.
The standalone standard-library
[exact checker](computer-assisted/check_extreme_width_anchor_area.py)
evaluates all 1024 midpoint terms and
the upward Lipschitz correction,
obtaining

\[
\boxed{
4\delta\sum_i(r_{\rm up}(x_i))_+
+2Lq_+\delta
=\frac{170619797734244653516561}
{104857600000000000000000}
=1.627157189695\ldots.}
\tag{EXW.12}
\]

The exact margin below 41/25 is

\[
\boxed{
\frac{1346666265755346483439}
{104857600000000000000000}>0.}
\tag{EXW.13}
\]

The checker was run with exact Fraction
arithmetic. Its executed source has
SHA-256
9c03302ba0af2c3f3ab61676b1bfee4ef8eab65f0322e0ab0248098942807c76,
and the committed source's Git blob
matches the executed file's
43405785aee38fa8442ea19afac7e232c6641085.
No floating-point numerical optimizer,
Numpy arrays, Lean build or CI is
part of the proof. The finite arithmetic
alone is not the continuum argument:
the geometric reduction is EXW.2–EXW.11.

## 4. Exact rational comparison with Romik's area

Use the explicit exact candidate formula

\[
M=1+4Y^2+\arctan Y,\qquad
4Y^3+3Y-1=0,\quad Y>0.
\tag{EXW.14}
\]

The cubic is strictly increasing for
positive Y, negative at 297/1000
and positive at 3/10, so
\(297/1000<Y<3/10\).
For \(0<Y<1\), integrating
\(1/(1+t^2)\ge1-t^2\) proves
\(\arctan Y\ge Y-Y^3/3\).
The lower polynomial in Y is
increasing on this interval.
Therefore

\[
\boxed{
M>
1+4(297/1000)^2
+297/1000-\frac13(297/1000)^3
=\frac{1641103309}{10^9}
>\frac{41}{25}.
}
\tag{EXW.15}
\]

EXW.12–EXW.15 prove EXW.1
with **strict rational comparisons**.

## 5. What is still missing

This excludes the exact extreme-width
boundary \(W=2\sqrt2\) of the full-turn
feasible domain from beating Romik.
It is a genuinely global ordinary-area
theorem on **one boundary stratum**,
not the entire width interval.

At smaller W the switching angles need
not equal pi/4, the endpoint anchor
heights need not coincide, and the
45-degree support offsets are no
longer fixed exactly. Extending
this certificate to a positive-width
neighborhood requires explicit
quantitative stability of the
switching anchors and offsets.
The remaining interior widths and
arbitrary partial-turn motions
are not covered by EXW.1.
No unrestricted sharp optimality or
uniqueness is claimed.
