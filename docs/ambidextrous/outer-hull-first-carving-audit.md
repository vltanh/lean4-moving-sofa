# Outer supporting hull first, then carve both inner sweeps: an exact audit

**Scope (October 8, 2026).** This note takes seriously the proposed proof strategy “determine the convex hull from the moving **outer walls**, then remove the **inner-wall niches**.” It gives an exact, global formulation and a concrete obstruction to **optimizing the outer hull in isolation**. The hull-first *parameterization* is valid and already underlies canonical support tightening in [Note 8](08-common-hull-tightening.md). No claim of a sharp ambidextrous upper bound or of a verified counterexample to Romik optimality follows.

The new elementary rectangular calculation below illustrates, using just one angle of each handed turn, how increasing the outer convex hull may **strictly decrease** the entire carved envelope area. The existing [MH](midpoint-hallways-global-bound.md) obtains a different, universal finite-angle upper bound for **arbitrary outer offsets**; this note does not rebrand that result or turn a finite-position relaxation into a full-turn certificate.

## 1. First determine outer supports — but not a maximum outer hull

Normalize the common incoming orientation so \(K=\operatorname{conv}S\subset\mathbb R\times[0,1]\). For a complete conventional lower quarter turn, write
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
f_K(t)=h_K(u_t),\quad g_K(t)=h_K(v_t).
\]
Here \(h_K(w)=\max_{p\in K}p\cdot w\). If the hallway's **outer** walls are translated until they support \(K\), they have equations
\[
p\cdot u_t\le f_K(t),\qquad p\cdot v_t\le g_K(t).
\tag{OH.1}
\]
These hold at **every point of \(K\)** by definition. The corresponding inner walls lie exactly one unit back, at offsets \(f_K(t)-1\), \(g_K(t)-1\), so the *actual* forbidden inner quadrant is
\[
Q^-_{K,t}=\{p:p\cdot u_t<f_K(t)-1,\quad
                 p\cdot v_t<g_K(t)-1\}.
\tag{OH.2}
\]
The other handed family is the vertical reflection of the same construction for \(\rho K\), \(\rho(x,y)=(x,1-y)\).

**Lemma OH1 (outer-only problem is unbounded).** For every \(W>0\), the rectangle
\[
K_W=[-W/2,W/2]\times[0,1]
\tag{OH.3}
\]
admits **both complete continuous quarter-turn families of outer supporting-wall placements**, and their incoming and outgoing **outer straight-arm strip widths** are one. Consequently the supremum of outer-hull area over these outer-only constraints is **infinite**.

**Proof.** At every angle choose the two translated supporting outer walls OH.1. They enclose \(K_W\) automatically; the support offsets depend continuously on the angle. At the incoming frame the entire rectangle fits a width-one horizontal strip because its vertical span equals one. At the terminal quarter-turn frame the relevant outgoing strip has vertical normal and is therefore also width one. Repeat for the vertically reflected handedness. Yet \(|K_W|=W\to\infty\). The **inner disjunction** has intentionally been omitted; this is not a genuine sofa motion for large \(W\). \(\square\)

So one can **parametrize** a hull by outer supports first, but cannot **maximize** its area first and carve later.

## 2. Carving two \(45^\circ\) niches already reverses the outer-area ordering

At the single lower frame \(t=\pi/4\), both support values of \(K_W\) equal \((W/2+1)/\sqrt2\). In the horizontal slice at abscissa \(x\), the forbidden quadrant OH.2 has the exact upper roof
\[
m_W(x)=\frac W2+1-\sqrt2-|x|.
\]
Let \(d=\sqrt2-1\) and \(a=W/2\). Its actual positive forbidden roof above the baseline is
\[
n_{45}(x)=(a-d-|x|)_+.
\tag{OH.4}
\]
The opposite handed midpoint quadrant is the reflection about \(y=1/2\). Consequently the **ordinary surviving vertical length after these two single-angle carve-outs** is
\[
\boxed{\ell_{45,W}(x)=[1-2(a-d-|x|)_+]_+.}
\tag{OH.5}
\]
The final positive part is indispensable: the two niches can eliminate the whole fiber.

Integrate over the true outer projection \(x\in[-a,a]\), putting \(z=a-|x|\) on the right half:
\[
\begin{aligned}
A_{45}(W)
&:=\int_{-a}^a\ell_{45,W}(x)\,dx\\
&=2\int_0^a[1-2(z-d)_+]_+\,dz\\
&=\boxed{\begin{cases}
W,&W\le2d,\\[2pt]
W-2(W/2-d)^2,&2d\le W\le2d+1,\\[2pt]
2d+\tfrac12=2\sqrt2-\tfrac32,&W\ge2d+1.
\end{cases}}
\end{aligned}\tag{OH.6}
\]
This exact piecewise formula is obtained by splitting the integral at \(z=d\) and \(z=d+1/2\). There is no angular sampling *claim*: these are the **exact two specified midpoint placements** and give a valid upper bound for the full-turn envelope
\[
\boxed{|E_{\rm full}(K_W)|\le A_{45}(W).}\tag{OH.7}
\]

Even though the outer-only convex-hull area is \(W\to\infty\), after just these two inward cuts the surviving total ordinary area is at most
\[
\boxed{2\sqrt2-\tfrac32<\tfrac32<M
\quad\text{for }W\ge2\sqrt2-1.}\tag{OH.8}
\]
For \(W>2\sqrt2-1\), OH.5 also shows a central open interval of **empty fibers**. Taking both continuous full turning sweeps can only remove more.

**Concrete containment reversal at Romik.** Let \(K_*\) be the horizontally centered Romik candidate's actual convex hull. Its known horizontal span is \(2m<8/3<3\) (for example, [Romik's exact width formula](https://arxiv.org/html/1606.08111v3#S1.SS2), or the existing explicit reference support notes). Its vertical span is one. Thus
\[
K_*\subsetneq K_3=[-3/2,3/2]\times[0,1],
\qquad
|K_*|<|K_3|=3,
\]
yet
\[
\boxed{
|E_{\rm full}(K_3)|
\le2\sqrt2-\tfrac32
< M
=|E_{\rm full}(K_*)|.
}\tag{OH.9}
\]
The last equality is the reference construction, *not* an optimality assertion. Enlarging the convex hull can enlarge its canonical inner forbidden quadrants so much that the **carved** area goes down. The area of the outer hull is therefore the wrong objective.

## 3. A correct self-consistent hull-first procedure

For a proposed compact convex hull \(K\) in the incoming strip, define the complete canonical survivor
\[
E(K)=K\setminus\bigcup_{0\le t\le\pi/2}
(Q^-_{K,t}\cup Q^+_{K,t}).
\tag{OH.10}
\]
Its ordinary area is **exactly** the integral of the positive vertical-fiber lengths. Let \(a_K(x)\), \(b_K(x)\) denote the upper/lower outer hull boundaries; let \(n_K(x)\) be the complete positive lower-niche roof and \(n_{\rho K}(x)\) the reflected upper roof. Then
\[
\boxed{
|E(K)|=\int_{\operatorname{proj}_x K}
\Big[\min\{a_K(x),1-n_{\rho K}(x)\}
-\max\{b_K(x),n_K(x)\}\Big]_+\,dx.
}\tag{OH.11}
\]
This formula retains **all ordinary-area clipping, overlap and disconnection**. For partial turns the *whole-body outgoing strip* bounds must also be included as in [OS1](original-motion-signed-convex-domain.md); an endpoint L-placement alone is insufficient.

The next step is the **actual-hull self-consistency test**. If \(E(K)\) has nonempty fibers on the full horizontal projection, it is connected. Put
\[
K^\sharp=\operatorname{conv}E(K)\subseteq K.
\]
Because \(h_{K^\sharp}(u)\le h_K(u)\) for every normal \(u\), shrinking these outer supports shifts the inner forbidden quadrants inward (they become smaller). All points previously in \(E(K)\) remain protected:
\[
\boxed{E(K)\subseteq E(K^\sharp),\quad
|E(K^\sharp)|\ge |E(K)|,\quad
\operatorname{conv}E(K^\sharp)=K^\sharp.}\tag{OH.12}
\]
This is the one-step support-tightening repair from [FH3](feasible-hull-minkowski-nonconvexity.md) and [SAT1](saturation-does-not-rescue-repair.md), reproduced here as the correct hull-first algorithm. If there are empty horizontal fibers, first apply the [GC4](horizontal-gap-compression.md) **area-preserving connectedification**; that may change the horizontal width and the final convex hull.

For a globally maximizing body, the chosen hull may therefore be taken **self-consistent**, and no candidate needs to credit disconnected components as a connected sofa.

## 4. The precise remaining optimality obligation

The geometric sequence **outer hull → canonical inner niches → ordinary area → support retightening** is correct and globally covers complete conventional turns. The true target is not
\(\max |K|\), but rather the *coupled* functional OH.11. A sharp proof would require a universal comparison showing
\[
|E(K)|\le M\quad\text{for every normalized convex }K,
\]
or a different joint calibration of the signed version. This is still **open**; the direct support-based outer/inner boundary first variations produce Romik's contact equations locally, but local stationarity alone does not prove global optimality.

The original unrestricted problem also permits proper **partial** terminal turning angles. The exact [OS1–OS2](original-motion-signed-convex-domain.md) formulation covers them by adding two independent terminal angles and both outgoing-strip constraints. Thus a truly unrestricted sharp theorem must either bound that larger objective or validly eliminate the partial-turn branch.

The result of this note is a clear *hull-first proof architecture* and an exact outer-only obstruction, **not** a claim that the missing globally sharp comparison has been supplied. No CI, Lean/Lake build, numerical optimizer or new global area certificate was run.
