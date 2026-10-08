# A three-point *location* ribbon, not merely a midpoint thickness bound

**Theorem TSW-R1 (anchored central ribbon).** Under the hypotheses of
[TSW](three-point-switching-fiber-width.md) or the more general
competitive partial-turn hypotheses of
[PTW](partial-turn-three-point-width.md), let
\(P=(l,y_L)\), \(Q=(r,y_R)\) be **any actual**
leftmost and rightmost retained points.
For \(x\in(l+1,r-1)\), let
\(L=x-l>1\), \(R=r-x>1\), and define

\[
H_{L,R}:=\max_{0<t<\pi/2}
\frac{\sin t+\cos t-R\cos^2t-L\sin^2t}
{\sin t\cos t}.
\tag{TSW-R.1}
\]

Then **every actual sofa point** \(p=(x,y)\in S\)
lies in the *same* ribbon centered at the average of the
two extreme-point heights:

\[
\boxed{\left|y-\frac{y_L+y_R}{2}\right|
\le\frac{H_{L,R}}2.}
\tag{TSW-R.2}
\]

This is stronger than bounding the length of each
individual vertical fiber: the fiber cannot shift up
or down independently between columns. There is no
assumed common top face, curvature domination,
connected vertical fibers, or reference hull.

## Proof

Apply the first-entry safe-wall switch of PTW
to **the same point** \(p\) for each of the two
handed motions (reflect vertically for the upper one).
The lower angle \(\theta\) gives, from the two horizontal
extreme anchors,

\[
y_R-y\le F_R(\theta),\qquad
y_L-y\le F_L(\theta),
\]

hence

\[
y\ge\tfrac12(y_L+y_R)-\tfrac12G_{L,R}(\theta)
\ge\tfrac12(y_L+y_R)-H_{L,R}/2.
\]

For the upper-angle switch \(\varphi\), the
reflected anchor tests give

\[
y-y_R\le F_R(\varphi),\qquad
y-y_L\le F_L(\varphi),
\]

hence

\[
y\le\tfrac12(y_L+y_R)+\tfrac12G_{L,R}(\varphi)
\le\tfrac12(y_L+y_R)+H_{L,R}/2.
\]

Combine the two. Every inequality tests *true*
support depths against actual sofa points; no
independence or common-rotation-angle assumption
was used. QED.

## Exact midpoint corollary

At \(x=(l+r)/2\), let \(D=W/2\in(1,\sqrt2]\).
The explicit scalar maximum computed in TSW.13 gives

\[
\boxed{
\left|y-\frac{y_L+y_R}{2}\right|
\le
\begin{cases}
\tfrac12(D-\sqrt{D^2-1}),
  &1<D\le3/(2\sqrt2),\\[2pt]
\sqrt2-D=\sqrt2-W/2,
  &3/(2\sqrt2)\le D\le\sqrt2 .
\end{cases}}
\tag{TSW-R.3}
\]

In particular for competitive width \(W\ge3/\sqrt2\),
the midpoint fiber is confined to a vertical interval
of length \(2\sqrt2-W\) whose **center is prescribed
by the two extreme-point heights**. At maximal
width \(W=2\sqrt2\) the entire midpoint fiber
is the single point at height \((y_L+y_R)/2\);
the TSW equality argument moreover forces
\(y_L=y_R\).

This ribbon inequality is an exact, testable
finite-anchor condition suitable for pruning
**direct geometric cell-occupation** proposals.
A putative area proof would still have to bound
the two one-unit-wide outer regions; the ribbon
alone does **not** control their combined area.

No Lean, CI, numerical optimization or sharp
area-value conclusion is involved.
