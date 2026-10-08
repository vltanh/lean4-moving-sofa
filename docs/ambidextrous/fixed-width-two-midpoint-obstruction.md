# A fixed-width exact witness defeats the two-midpoint-only area route

**Result FM45.** An explicit *connected* two-hallway
envelope passes the incoming unit strip and both
opposing proper \(45^\circ\) hallway placements,
has **any prescribed horizontal projection width**
\(2\le W\le2\sqrt2\), and has ordinary area

\[
\boxed{
A_{45}(W)=2\sqrt2-1-\frac{(2\sqrt2-W)^2}{4}
\ \ge\ 4(\sqrt2-1)=1.656854249\ldots>M.
}
\tag{FM45.1}
\]

Thus the new sharp global width bound
\(W\le2\sqrt2\), even together with
**both complete \(45^\circ\) hallway snapshots**,
does not imply the desired sharp area \(M\).
Additional **intermediate** directions or a
genuinely continuum/topological inequality
are indispensable. This is a geometric
*finite-relaxation witness*, **not** a
full-turn sofa and not a counterexample to
Romik optimality.

The two-angle spatial geometry below is
independent of \(P_J\), curvature repairs,
candidate support formulas, and numerical optimization.
The relation to the existing global MH bound
\(2\sqrt2-1\) is acknowledged; the useful
new point is its entire fixed-horizontal-width
interpolation within the TSW width range.

## 1. Two \(45^\circ\) hallways as four piecewise-linear roofs

Let \((x,y)\) be the incoming body coordinates.
For the lower proper \(45^\circ\) frame,
with perpendicular normals
\((1,1)/\sqrt2,(-1,1)/\sqrt2\), choose
outer support offsets so that its two outer
walls intersect in the tent

\[
U(x)=u_0-|x-W/2|.
\]

The inner disjunction is then simply
\(y\ge U(x)-\sqrt2\). Indeed both outer
wall heights have slopes \(+1,-1\),
their minimum is \(U(x)\), and moving
each physical wall one unit along its
normal lowers its vertical line height
by \(\sqrt2\). Thus the exact lower-handed
hallway section is

\[
U(x)-\sqrt2\le y\le U(x).
\tag{FM45.2}
\]

For the vertically reflected proper
upper \(45^\circ\) hallway choose the
symmetric placements, with lower outer
wall roof

\[
L(x)=1-U(x).
\]

Its vertical section is

\[
L(x)\le y\le L(x)+\sqrt2.
\tag{FM45.3}
\]

Set \(u_0=W/4+(1+\sqrt2)/2\) and
restrict to the common incoming strip
\(0\le y\le1\) and horizontal interval
\(0\le x\le W\).
The combined finite-hallway envelope is

\[
E_W=\left\{(x,y):0\le x\le W,\
\max(0,U(x)-\sqrt2,1-U(x))
\le y\le
\min(1,U(x),1-U(x)+\sqrt2)\right\}.
\tag{FM45.4}
\]

All inequalities here come from *actual
L-shaped hallway placements*, not just
a relaxed formal support functional.
They are symmetric under \(y\mapsto1-y\).
For the indicated width range every
vertical fiber is a **nonempty closed interval**
centered at \(y=1/2\), so the set is compact
and connected, with horizontal projection
exactly \([0,W]\). It has continuous actual
motions only at the **two stated** orientations;
no intervening turning feasibility is claimed.

## 2. Exact area by three elementary height layers

Put \(a=W/4+(1-\sqrt2)/2\).
Then \(0<a\le1/2\), \(u_0=\sqrt2+a\),
and \(W/2=2a+\sqrt2-1\).
For \(t=|x-W/2|\in[0,W/2]\),
the vertical fiber height is

\[
\ell_W(t)=
\begin{cases}
1-2a+2t,&0\le t\le a,\\
1,&a\le t\le a+\sqrt2-1,\\
1-2(t-a-\sqrt2+1),
   &a+\sqrt2-1\le t\le W/2.
\end{cases}
\tag{FM45.5}
\]

Each of the outer and central ramps has
horizontal length \(a\) and average
height \(1-a\). The plateau has length
\(\sqrt2-1\) and height one. The geometry
is mirrored about \(x=W/2\), so

\[
\begin{aligned}
|E_W|
&=2[2a(1-a)+(\sqrt2-1)]\\
&=4a(1-a)+2(\sqrt2-1)\\
&=2\sqrt2-1-\frac{(2\sqrt2-W)^2}{4}.
\end{aligned}
\]

This is FM45.1. Since \(2\le W\le2\sqrt2\),
the quadratic area is increasing in \(W\),
and its minimum is \(A_{45}(2)=4(\sqrt2-1)\).
The reference area \(M=1.6449552184\ldots\)
is strictly smaller. The strict comparison
can use \(4(\sqrt2-1)>33/20>M\),
where \(M<33/20\) is the independently
established candidate constant bound.

At the maximal horizontal width \(W=2\sqrt2\),
the shape has a *single-point central fiber*
and single-point endpoint fibers, yet its
area is \(2\sqrt2-1\approx1.828427\).
This illustrates that a **central pinch
alone** does not limit area sharply.

## 3. What was tested and what follows

A short numerical optimization of the
true two-\(45^\circ\)-hallway *polygonal
area* at widths \(2.0,2.2,\dots,2.8\)
recovered the above symmetric tent family
to the sampling resolution. These
exploratory values did **not** prove a
universal fixed-width maximum:
FM45.1 is a direct *feasible witness*,
not a general bound on every pair of
hallway offsets.

The mathematical consequence is exact
and negative: **no proof that uses only**
the two fixed \(45^\circ\) snapshots
plus the horizontal-width restriction
\(W\le2\sqrt2\) can establish
\(|S|\le M\), even when it also requires
connectedness and the full projection
of the finite envelope.

The stronger all-angle
[three-point switching ribbon](three-point-switching-ribbon.md)
is a separate continuum consequence and
is **not** assumed by this witness.
The natural next direct-geometric
experiment is to combine interval
ribbon restrictions with **additional
intermediate** hallway frames, and
prove a whole-domain box-area upper
bound rather than trusting a local
numerical optimum.

No Lean, CI, machine proof or huge
global search was run. The exact
piecewise-linear area calculation is
a complete hand proof about this
finite-angle witness.
