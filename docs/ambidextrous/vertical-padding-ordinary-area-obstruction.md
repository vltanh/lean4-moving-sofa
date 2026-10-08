# Vertical Minkowski padding: exact ordinary-area formula and a unit-span obstruction

**Status:** Exact, continuum-angle geometry. This is a *universal ordinary-area accounting identity* for vertical-symmetric convex hulls, together with a fully feasible connected full-turn example disproving **unconditional area-monotone vertical height padding**. It does **not** prove Romik optimality, rule out a height-normalization theorem for competitive/maximizing bodies, or show that the original and padded shapes are themselves identical. No CI, Lean/Lake, or numerical certificate enters the proof.

The motivation is [SEC](reflection-equivariant-connectedification.md): although a left-right symmetric disconnected complete-turn envelope can be connectedified with its area and vertical span unchanged, its span may be below one. Adding a vertical segment to the hull is a possible way of restoring hull span, but one must compare the *ordinary surviving area* rather than merely the convex hull area.

## 1. Exact translation of the two full forbidden sweeps

Let \(K\) be a compact convex body of nonempty interior, with horizontal projection \(I\), width \(W=|I|\), and vertical reflection symmetry
\[
\rho_H(x,y)=(x,H-y),\qquad \rho_HK=K.
\]
Normalize the vertical span of \(K\) to \([0,H]\), where \(0<H\le1\). Let its lower and upper vertical boundary functions be \(b(x)\) and \(a(x)\); reflection gives \(a(x)+b(x)=H\).

For an interior lower conventional turn angle, use the orthogonal normals
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad 0<t<\pi/2.
\]
The open canonical forbidden quadrant is
\[
Q^-_K(t)=\{p:p\cdot u_t<h_K(u_t)-1,\quad p\cdot v_t<h_K(v_t)-1\}.
\]
Its union over the full turn has vertical sections of the form \((-\infty,n(x))\); define the *ambient* roof \(n(x)\) by taking the supremum of the minimum of its two wall ordinates. Use this **signed** ambient roof, not just its positive part; its value is finite for each \(x\in I\) because the angle \(t=\pi/4\) gives finite wall ordinates. The upper forbidden sweep is the \(\rho_H\)-reflection of the lower one.

For \(0\le\delta\le1-H\), let
\[
K_\delta=K+[-\delta/2,\delta/2]e_y.
\]
Every lower-frame normal has nonnegative vertical component, so
\[
h_{K_\delta}(u_t)=h_K(u_t)+(\delta/2)\sin t,\quad
h_{K_\delta}(v_t)=h_K(v_t)+(\delta/2)\cos t.
\]
Consequently the **entire lower open sweep**, including the two limiting frames, is exactly the old sweep translated upward by \(\delta/2\), and the reflected upper sweep is translated downward by \(\delta/2\). In particular, the new lower ambient roof is \(n(x)+\delta/2\). The outer hull section becomes
\[
[b(x)-\delta/2,\ a(x)+\delta/2].
\]

Set \(\eta(x)=n(x)-b(x)\). The full canonical two-turn envelope \(E_\delta=E(K_\delta)\) therefore has, with no smoothness, contact-order, or connectedness assumption, **exact fiber length**
\[
\boxed{\ell_\delta(x)=
\left[a(x)-b(x)+\delta-2(\eta(x)+\delta)_+\right]_+.}\tag{VP.1}
\]
This formula correctly retains any empty fiber using the final positive part. It also retains *both* clipping corrections: the quantity \((\eta+\delta)_+\) is the niche depth **inside the current convex hull**, not the whole ambient niche height.

If the midline \(y=H/2\) survives all complete canonical hallways of \(K_\delta\) for every \(x\in I\), then every fiber is nonempty and the outer positive part can be dropped. Integrating \(a-b\) gives
\[
\boxed{|E_\delta|=|K|+W\delta
-2\int_I(\eta(x)+\delta)_+\,dx.}\tag{VP.2}
\]
Here \(|K_\delta|=|K|+W\delta\) exactly, without polygonal approximation. Since \(z\mapsto(z+\delta)_+\) is convex in \(\delta\), the ordinary-envelope area in VP.2 is **concave** on any interval of thickness values where the midline survives.

For such thickness values \(\delta\ge0\),
\[
\boxed{|E_\delta|-|E_0|
\le\delta\bigl(W-2|\{x\in I:\eta(x)>0\}|\bigr).}\tag{VP.3}
\]
Indeed \((z+\delta)_+-z_+\ge\delta\) for \(z>0\) and is nonnegative elsewhere. This is the exact occupancy-width test for the proposed padding operation: if effective lower niche covers more than half the projection, **vertical padding strictly loses ordinary area**, even though it gains convex hull area.

The sharp candidate's aligned reference configuration is at the boundary of this test: its niche is confined to a central interval of length \(W/2\). VP.3 by itself offers no strictly improving normalization at that boundary.

## 2. A fully feasible, saturated symmetric counterexample to monotone padding

Choose the exact rational rectangle
\[
\boxed{W=3/2,\quad H=19/20,\quad
K=[-3/4,3/4]\times[0,19/20].}\tag{VP.4}
\]
It is invariant under both horizontal and vertical reflection. Let \(q=\sqrt{1-H^2}=\sqrt{39}/20\), \(a=W/2-q=(15-\sqrt{39})/20\), and
\[
r=W/2+q-1/H=\frac{\sqrt{39}}{20}-\frac{23}{76}>0.
\]
The last positivity is exact: \(19^2\cdot39=14079>115^2=13225\).

For each lower turn angle \(t\), its two positive-y supporting values are
\[
f(t)=(W/2)\cos t+H\sin t,\qquad
g(t)=(W/2)\sin t+H\cos t.
\]
An angle-\(t\) quadrant meets the baseline \(y=0\) exactly on the open interval
\[
\left(-W/2+\frac{1-H\cos t}{\sin t},\
W/2+\frac{H\sin t-1}{\cos t}\right),
\]
when its left endpoint is smaller than its right. Choose \(t_0=\arccos H\), so \((\cos t_0,\sin t_0)=(H,q)\), and the complementary angle \(t_1=\pi/2-t_0\). Their exact forbidden baseline intervals are
\[
(-a,r)\quad\text{and}\quad(-r,a).
\]
Since \(r>0\), these intervals overlap and their union is **all of \((-a,a)\)**. The roof \(n(x)\) is therefore **strictly positive** on that entire interval: every point at its baseline is strictly forbidden at one of these two angles, so a small positive vertical neighborhood is forbidden as well.

For the required *whole-continuum* ceiling, the corner ordinate at an arbitrary \(t\) is
\[
c_y(t)=W\sin t\cos t+H-\sin t-\cos t.
\]
Put \(z=\sin t+\cos t\in[1,\sqrt2]\). Then
\[
c_y(t)=\frac W2(z^2-1)+H-z,
\]
a convex quadratic in \(z\). Its maximum is attained at an endpoint and equals
\[
\max(H-1,\ H+W/2-\sqrt2)
=\frac{17}{10}-\sqrt2<\frac9{20},
\]
where the last comparison follows from \(\sqrt2>5/4\).

The complete lower forbidden niche of \(K\) therefore lies below \(y=9/20\). In the vertically padded rectangle
\[
K_\delta=[-3/4,3/4]\times[-\delta/2,H+\delta/2],
\qquad 0\le\delta\le1/20,
\]
the lower sweep moves up by \(\delta/2\le1/40\) and the upper sweep moves down by \(\delta/2\). The entire horizontal segment
\[
[-3/4,3/4]\times\{H/2\}
\]
survives both complete sweeps, since \(9/20+1/40=19/40=H/2\) and the prior bound is strict. Each envelope \(E_\delta\) consequently has nonempty **interval** fibers all meeting that segment, and is compact, connected, and follows **both complete conventional 90-degree turns** by continuous canonical support motions. After a vertical translation it lies in the usual incoming strip of unit width.

Moreover \(\operatorname{conv}E_\delta=K_\delta\): every point on the two extreme *vertical edges* \(x=\pm W/2\) survives both turns. On the right edge the first lower-wall depth never exceeds the total rectangle height \(H+\delta\le1\); on the left edge the second lower-wall depth never exceeds \(H+\delta\le1\). The upper-turn statements are their vertical reflections. Thus all four extreme vertices are actual surviving body points.

For this rectangle \(b(x)=0\), so \(\eta(x)=n(x)\). VP.2 applies over the entire permitted padding interval. Since \(n(x)>0\) throughout \((-a,a)\), VP.3 gives, for **every** \(0<\delta\le1/20\),
\[
\begin{aligned}
|E_\delta|-|E_0|
&\le\delta(W-4a)\\
&=\boxed{\delta\left(\frac{\sqrt{39}}5-\frac32\right)<0.}
\end{aligned}\tag{VP.5}
\]
The last strict inequality is immediate from \(4\cdot39=156<225=9\cdot25\).

**Theorem VP1.** Even for a compact connected, canonically saturated, left-right and up-down reflection-symmetric, full-two-turn sofa with exact actual hull and positive area, increasing its convex hull's incoming vertical span from \(19/20\) to **exactly one** by vertical Minkowski addition strictly **decreases** the ordinary area of its fully saturated two-turn envelope.

No numerical area estimate or finite-angle motion check is involved. This example is far below Romik's candidate: \(|E_0|\le|K|=57/40<M\).

## 3. Scope and remaining sharp global obligations

VP.1 is valid for arbitrary convex vertical-symmetric hulls even with disconnected envelopes; VP.2–VP.3 require the explicitly stated midline survival. The rectangle family proves that one cannot fill the subunit-span gap in the hull-reflection program by invoking unconditional area monotonicity under vertical Minkowski padding. It does **not** rule out an operation specialized to high-area sofas or global maximizers. It does not refute [HS.4](hull-reflection-symmetrization-budget.md), which averages a hull with its **horizontal** reflection and concerns a different operation.

The sharp unrestricted full-turn clipping-deficit inequality, the symmetric **subunit-span sharp bound**, and unrestricted **partial turns** remain unproved. No sharp optimality claim is inferred here.
