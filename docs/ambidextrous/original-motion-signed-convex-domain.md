# Original ambidextrous value as one signed, joint convex-domain optimization

**Status (October 8, 2026):** An exact **value-equivalence theorem for the original ambidextrous moving-sofa problem**, including arbitrarily partial, backtracking and nonmonotone physical motions. It removes the separate *completion-of-partial-turns* requirement at the **formulation** level, without asserting that partial turning sofas can be completed and without assuming the sharp Romik upper bound.

The resulting maximization is over **all compact convex hulls in one fixed rectangle** and **two independent proper terminal angles**. Each convex hull's signed vertical-fiber objective uses both conventional turning constraints **and the two actual outgoing unit strips**. The domain is convex under Minkowski interpolation in the hull and is a rectangle in the angular parameters. It is not asserted that the *objective* is jointly concave or that its maximum is Romik's \(M\).

Inputs requiring separate review: the proper-angle reduction for all sofas above \(\sqrt2\) from [Note 10, Theorem 30](10-wrong-angle-exclusion.md) and the original-motion midpoint argument in [GH](midpoint-bound-general-motions.md); the area-preserving connectedification [GC4](horizontal-gap-compression.md). All geometric formulas and the value comparison are given below independently of any one-cap weighted theorem or \(G\)-inequality. No Lean, CI or numerical optimization.

## 1. Two independent terminal angles and exact signed fibers

Write \(\rho(x,y)=(x,1-y)\). For any nonempty compact convex
\[
K\subseteq\mathbb R\times[0,1]
\]
write \(I_K=[l,r]\) for its horizontal projection and \(a_K(x)\), \(b_K(x)\) for the upper/lower boundaries of its vertical fibers.

For each **proper lower-turn** angle \(0<t<\pi/2\) put
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad
m_{K,t}(x)=
\min\left(
\frac{h_K(u_t)-1-x\cos t}{\sin t},\
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\right).
\]
For an independent terminal magnitude \(\alpha\in[\pi/4,\pi/2]\), the positive partial niche roof is
\[
n_{K;\alpha}(x)=
\max\left\{0,\sup_{0<t<\alpha}m_{K,t}(x)\right\}.
\tag{OS.1}
\]
The actual **outgoing straight-arm strip** for this lower motion has normal \(u_\alpha\), and (after support tightening) it adds the entire-body condition
\[
h_K(u_\alpha)-1\le p\cdot u_\alpha\le h_K(u_\alpha).
\]
The upper outer inequality is automatic for \(p\in K\). Because \(\sin\alpha\ge1/\sqrt2>0\), the other condition is exactly the vertical lower barrier
\[
\boxed{e_{K;\alpha}(x)=
\frac{h_K(u_\alpha)-1-x\cos\alpha}{\sin\alpha}.}
\tag{OS.2}
\]
This is a *full-body outgoing strip condition*, **not** merely one additional corner placement. At \(\alpha=\pi/2\) it is redundant because \(h_K(e_y)\le1\) and \(p_y\ge0\).

Define the upper-handed objects by applying the same lower-turn formulas to the vertically reflected hull \(\rho K\), with an independent
\(\gamma\in[\pi/4,\pi/2]\):
\[
n^+_{K;\gamma}=n_{\rho K;\gamma},\qquad
e^+_{K;\gamma}=e_{\rho K;\gamma}.
\]
The opposite outgoing strip in the original coordinates is \(y\le1-e^+_{K;\gamma}(x)\).

For the **joint** two-turn-and-two-outgoing-strip envelope \(E_{\alpha,\gamma}(K)\), each fixed-\(x\) surviving section is
\[
E_{\alpha,\gamma}(K)_x=
\begin{cases}
[L_{K,\alpha}(x),U_{K,\gamma}(x)],
&L_{K,\alpha}(x)\le U_{K,\gamma}(x),\\
\varnothing,&L_{K,\alpha}(x)>U_{K,\gamma}(x),
\end{cases}
\]
where
\[
\boxed{
\begin{aligned}
L_{K,\alpha}(x)&=
\max\{b_K(x),\,n_{K;\alpha}(x),\,e_{K;\alpha}(x)\},\\
U_{K,\gamma}(x)&=
\min\{a_K(x),\,1-n_{\rho K;\gamma}(x),\,
             1-e_{\rho K;\gamma}(x)\}.
\end{aligned}}\tag{OS.3}
\]
No curvature, symmetry, common top face or support-contact mode is assumed. Every relevant outer wall is already satisfied by \(K\); the lower forbidden union is downward closed, the reflected upper one upward closed, and the two terminal strips give one additional lower and upper affine bound respectively.

Let
\[
\ell_{K;\alpha,\gamma}(x)
=U_{K,\gamma}(x)-L_{K,\alpha}(x).
\]
Define the **signed, joint original-motion objective**
\[
\boxed{\mathscr V(K,\alpha,\gamma)=
\int_{I_K}\ell_{K;\alpha,\gamma}(x)\,dx.}
\tag{OS.4}
\]
It is finite and measurable for compact convex \(K\) and the stated nonzero angles; the roof functions are suprema of continuously parametrized wall functions. Its *ordinary* full-envelope area is exactly
\[
\boxed{
|E_{\alpha,\gamma}(K)|
=\int_{I_K}(\ell_{K;\alpha,\gamma})_+\,dx
=\mathscr V(K,\alpha,\gamma)
+\int_{I_K}(-\ell_{K;\alpha,\gamma})_+\,dx.
}\tag{OS.5}
\]
The second term is the physical **empty-fiber correction**. It is not silently removed for arbitrary proposed hull data. In contrast, whenever \(K\) is the actual convex hull of a **connected** sofa following these two motions and outgoing strips, every signed fiber is nonnegative and this correction vanishes.

## 2. One fixed convex hull domain suffices for every potentially maximal sofa

Let \(V_{\rm amb}\) be the supremum of ordinary areas of all compact connected planar bodies that negotiate **both actual physical** unit right-angle hallways from a common incoming orientation. Romik's explicit sofa gives \(V_{\rm amb}\ge M>\sqrt2\); the strict comparison is established arithmetically in [Note 10](10-wrong-angle-exclusion.md).

For any genuine sofa \(S\) with \(|S|>\sqrt2\), the wrong-way exclusion and proper-angle reduction of Note 10 produce **two actually visited conventional families** \([0,\alpha]\) and \([0,\gamma]\), with
\[
\alpha,\gamma>\pi/4,\qquad\alpha,\gamma\le\pi/2,
\]
and **actual outgoing whole-body unit strips** normal to the respective \(u_\alpha,u_\gamma\) in the lower and reflected-upper frames. Neither motion must be monotone; intermediate value continuity forces every angle on its selected interval to be visited. By canonical support tightening, \(S\) satisfies all these inequalities with offsets \(h_{\operatorname{conv}S}\).

The same lower **midpoint** angle \(t=\pi/4\) yields a width bound without importing the sharper three-point-width theorem. Let \(H\le1\) be the vertical span and \([l,r]\) the horizontal projection of \(S\). At the midpoint frame \(u=(1,1)/\sqrt2\), \(v=(-1,1)/\sqrt2\), testing the two support depths against actual rightmost and leftmost points gives for every \(p=(x,y)\in S\)
\[
h_S(u)-p\cdot u\ge (r-x-H)/\sqrt2,
\quad
h_S(v)-p\cdot v\ge (x-l-H)/\sqrt2.
\]
Whichever canonical inner wall protects \(p\) must have depth at most one, so
\[
x\ge r-(H+\sqrt2)\quad\text{or}\quad
x\le l+(H+\sqrt2).
\]
Connectedness makes the horizontal projection the whole interval; a gap between the displayed permitted subintervals is impossible. Therefore
\[
\boxed{r-l\le2(H+\sqrt2)\le2+2\sqrt2<5.}
\tag{OS.6}
\]
After translating the horizontal center to zero and the lowest vertical ordinate to zero, every sofa of area \(>\sqrt2\) has
\[
\boxed{\operatorname{conv}S\subseteq
B=[-5/2,5/2]\times[0,1].}\tag{OS.7}
\]
No full-quarter completion or additional numerical area bound was used.

Let \(\mathcal K_B\) be the nonempty compact convex subsets of \(B\). It is a **Minkowski-convex** domain. The two terminal angles range independently over the compact square \([\pi/4,\pi/2]^2\).

## 3. The exact equivalence with the original unrestricted supremum

**Theorem OS1 (signed convex-domain original-motion value).**
\[
\boxed{
V_{\rm amb}
=
\sup_{\substack{K\in\mathcal K_B\\
\pi/4\le\alpha,\gamma\le\pi/2}}
\mathscr V(K,\alpha,\gamma).
}\tag{OS.8}
\]

**Proof of the lower bound.** Because \(V_{\rm amb}\ge M>\sqrt2\), for every sufficiently near-optimal body \(S\) we may assume \(|S|>\sqrt2\). The genuine-motion proper-angle reduction and the midpoint width bound of Section 2 place \(K=\operatorname{conv}S\) in \(\mathcal K_B\) and supply \(\alpha,\gamma\in[\pi/4,\pi/2]\) with both actual terminal strips.

Canonical support tightening gives
\(S\subseteq E_{\alpha,\gamma}(K)\). The x-projection of \(S\) is an interval and equals \(I_K\), since \(S\) is connected. Thus every envelope fiber over \(I_K\) is nonempty and
\(\ell_{K;\alpha,\gamma}(x)\ge0\) everywhere. Equation OS.5 yields
\[
|S|\le |E_{\alpha,\gamma}(K)|
=\mathscr V(K,\alpha,\gamma).
\]
Taking the supremum over bodies of area approaching \(V_{\rm amb}\) proves \(V_{\rm amb}\le\sup\mathscr V\).

**Proof of the upper bound.** Take *arbitrary* \(K\in\mathcal K_B\) and \(\alpha,\gamma\in[\pi/4,\pi/2]\); \(K\) is **not required to be a feasible sofa hull**. By OS.5,
\[
\mathscr V(K,\alpha,\gamma)\le |E_{\alpha,\gamma}(K)|.
\]
If the envelope is empty, the signed value is nonpositive and there is nothing to prove, because \(V_{\rm amb}>0\).

Otherwise the envelope is compact, contained in the incoming unit strip, has **interval-or-empty vertical fibers**, and is contained in **both complete prescribed angular intervals** and **both whole-body outgoing unit strips**. The area-preserving gap compression and vertical-fiber filling of [GC4](horizontal-gap-compression.md) turns this *possibly disconnected* envelope into a **compact connected** body \(T\), with exactly the same ordinary area and the **same two prescribed corner and terminal-strip families**. Support-depth tightening is preserved by that contraction (GC1), so the new body has actual continuous lower and upper corner rotations over those angular intervals.

At the initial frame \(t=0\), the body lies in a straight incoming unit strip; at each terminal frame it lies in the full outgoing strip normal to \(u_\alpha\) (or its vertically reflected counterpart). Holding the terminal orientation fixed and sliding along the outgoing arm provides the remainder of each physical passage. Likewise each incoming arm admits an arbitrary straight extension. The two incoming straight-arm starting positions can be aligned, since both share the same orientation and the same physical incoming unit corridor. Hence \(T\) is a **genuine unrestricted ambidextrous sofa**, without any demand that its terminal angles equal a quarter turn.

It follows that
\[
\mathscr V(K,\alpha,\gamma)
\le |E_{\alpha,\gamma}(K)|
=|T|\le V_{\rm amb}.
\]
Take the supremum over *every* convex \(K\) and both terminal angles. This proves OS.8. \(\square\)

**Exact calibration at the known feasible candidate.** Let \(K_*=\operatorname{conv}\Sigma_*\) be Romik's explicit two-handed reference hull, translated into the box \(B\). It has both complete conventional turns and a connected canonical envelope equal to the reference body. Therefore the *signed* fibers are all nonnegative and the formula yields
\[
\boxed{\mathscr V(K_*,\pi/2,\pi/2)=|\Sigma_*|
=1+4Y_*^2+\arctan(Y_*)=M.}\tag{OS.8a}
\]
So any prospective global calibration of \(\mathscr V\) has the **correct equality witness**. This is an input from the explicit reference construction, **not** evidence that no larger maximizer exists.

**Nothing has been proved about the numerical value of the right-hand supremum.** The equivalence is exact, not a hidden assertion that all partial motions can be completed to \(90^\circ\).

## 4. A monotone repair to genuinely admissible hulls, **at fixed terminal angles**

OS1 can be strengthened from an equality of suprema to a **pointwise nonlinear hull repair**. This directly resolves a potential concern about using an enlarged convex interpolation domain even when the supporting hull is not itself feasible.

**Proposition OS2 (signed-admission repair).** Fix \((\alpha,\gamma)\in[\pi/4,\pi/2]^2\) and any \(K\in\mathcal K_B\). There exists \(K^\sharp\in\mathcal K_B\), possibly of smaller horizontal width and vertical span, such that:

1. \(K^\sharp\) is the **actual hull** of a compact connected sofa following the same prescribed *partial* turning intervals **and both outgoing terminal strips**;
2. Its signed joint objective **does not decrease**:
   \[
   \boxed{\mathscr V(K^\sharp,\alpha,\gamma)\ge
   \mathscr V(K,\alpha,\gamma).}\tag{OS.10}
   \]
3. Every signed vertical fiber for \(K^\sharp\) is nonnegative, so
   \[
   \mathscr V(K^\sharp,\alpha,\gamma)=
   |E_{\alpha,\gamma}(K^\sharp)|.
   \tag{OS.11}
   \]

**Proof.** First suppose \(T=E_{\alpha,\gamma}(K)\) is nonempty. Every vertical section of \(T\) is interval or empty. It is a subset of the unit incoming strip and of the two prescribed continuous canonical hallway families and the two **whole-body** terminal strips. As in the proof of OS1, apply GC4 to obtain a compact connected body \(S^\sharp\) with **the same ordinary area as \(T\)**, satisfying the same angular intervals and terminal outgoing strips.

Let \(K^\sharp=\operatorname{conv}S^\sharp\). The horizontal gap compression can only decrease the horizontal projection length, so \(K^\sharp\) has width at most that of \(K\), which is at most five. Translate it horizontally to center its projection on zero; then \(K^\sharp\in\mathcal K_B\). The translation does not change feasibility or \(\mathscr V\). Its outgoing widths are at most one in both terminal normals because \(S^\sharp\) fits both outgoing strips.

Canonical support tightening gives \(S^\sharp\subseteq E_{\alpha,\gamma}(K^\sharp)\). Since \(S^\sharp\) is connected and has the same x-projection as its hull, **every** fiber of \(E_{\alpha,\gamma}(K^\sharp)\) is nonempty. The envelope is itself compact and connected by the interval-fiber argument, has actual hull \(K^\sharp\), and inherits the same two continuous motions and terminal strips. Consequently
\[
\begin{aligned}
\mathscr V(K^\sharp,\alpha,\gamma)
&=|E_{\alpha,\gamma}(K^\sharp)|\\
&\ge|S^\sharp|=|E_{\alpha,\gamma}(K)|\\
&\ge\mathscr V(K,\alpha,\gamma),
\end{aligned}
\]
where the last inequality is exactly the *positive-part identity* OS.5, not an unproved signed-roof bound.

If \(E_{\alpha,\gamma}(K)\) is empty, then \(\ell_{K;\alpha,\gamma}(x)<0\) at every x, so \(\mathscr V(K,\alpha,\gamma)\le0\). Take \(K^\sharp=\{(0,1/2)\}\), which is a compact connected zero-area body and fits both full turns and outgoing strips for *every* \(\alpha,\gamma\). Its projection has measure zero and \(\mathscr V(K^\sharp,\alpha,\gamma)=0\). This covers the degenerate case and proves all claims. \(\square\)

**Consequence:** For *every fixed* pair \((\alpha,\gamma)\), the supremum of the signed functional over **all** compact convex \(K\subseteq B\) equals its supremum over **actual compatible connected sofa hulls** (the latter domain is not Minkowski-convex by FH1). The price of restoring admission is a potentially nonlinear change of width, span, and four axis supports. OS2 therefore does *not* permit concavity or fixed-axis Euler equations to be transferred from one domain to the other without paying those changes.

In particular this is **not** the false claim that a Minkowski average of two feasible sofas remains feasible. The average may fail extreme-point retention or lose its full unit span, as FH1 demonstrates. OS2 replaces the averaged hull by a *different* actual hull, proves a signed-area comparison, and preserves the terminal angles of the prescribed partial motions.

## 5. Why this genuinely changes the research program

The previous full-turn signed reduction [SJ1](signed-joint-convex-domain-global-value.md) eliminated the positive-part penalty **at the level of suprema**, but explicitly left the original partial-turn problem separate. OS1 now handles **the full original motion class** by making the independent outgoing angles part of the variational domain. It does not invoke the missing two-cap interaction inequality \(G\le\Delta_U+\Delta_V\) anywhere.

Two earlier obstructions remain real, but are no longer **admission** objections to this particular formulation:

- [FH1–FH3](feasible-hull-minkowski-nonconvexity.md) shows the class of *actual feasible hulls* is not Minkowski-convex, and that fixing those hulls can lose unit span. OS1 optimizes over **all** compact convex \(K\subseteq B\) instead, whether or not they are actual hulls; connectedification supplies a true sofa when needed.
- [PM1](pinching-failure-of-global-envelope-concavity.md) disproves global concavity of the **ordinary** full-turn envelope area through a \(\varepsilon^{3/2}\) positive pinching correction. OS1 uses the **signed** objective \(\mathscr V\), leaving the positive-part correction outside the maximized expression, but equality of suprema is fully justified by the two directions of OS1.

**Open mathematical target:**
\[
\boxed{\mathscr V(K,\alpha,\gamma)
\stackrel{?}{\le}M
\quad\text{for every }K\in\mathcal K_B,\;
\alpha,\gamma\in[\pi/4,\pi/2].}
\tag{OS.9, unproved}
\]
By OS1, proving OS.9 would establish **sharp optimality for all original ambidextrous motions**, not merely complete turns. An explicit \(K,\alpha,\gamma\) with signed value \(>M\) would also yield, by GC4, a genuine **connected sofa of ordinary area \(>M\)**: it would falsify Romik's conjecture even if the raw envelope were disconnected.

A possible next *nonseparable* strategy is to find a direct joint calibration of OS.4, or establish appropriate concavity plus an independently verified global first-variation certificate at Romik's actual hull and \((\alpha,\gamma)=(\pi/2,\pi/2)\). **Neither concavity nor calibration is proved**, and arbitrary boundary and contact variations remain genuine obligations. The parameter domain's convexity alone proves nothing about the objective.

No CI, Lean/Lake compilation, manuscript build, experimental counterexample or unverified larger-sofa claim is part of this note. All earlier mathematical arguments remain research drafts requiring independent review.
