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

## 3. A globally exact nested-hull gain-versus-shadow-loss law

The previous rectangle comparison is not just a special numerical phenomenon. It has a universal and useful set-theoretic expression, independent of smoothness, contact charts or convex-hull curvature.

For a hull \(K\) and **fixed** visited proper turning-angle intervals \([0,\alpha]\), \([0,\gamma]\), let \(F_{\alpha,\gamma}(K)\) be the **union of all ambient forbidden inner regions**: both families of canonical inner-wall quadrants **and both lower-bound violations of the entire outgoing straight-arm strips**. The latter are important for genuine partial turns. We do not include the outer supporting half-plane bounds in \(F\), since every point of its own convex hull satisfies those automatically. Write
\[
E_{\alpha,\gamma}(K)=K\setminus F_{\alpha,\gamma}(K).
\]
For complete turns set \(\alpha=\gamma=\pi/2\). Axis limiting-wall conventions make no difference to the following exact set identity when all angular endpoints are included.

**Lemma OH2 (nested forbidden shadows).** If \(K_0\subseteq K_1\) are two nonempty compact convex bodies in the common incoming horizontal strip, and the **terminal angles are the same** for both, then
\[
\boxed{F_{\alpha,\gamma}(K_0)\subseteq F_{\alpha,\gamma}(K_1).}\tag{OH.13}
\]
Consequently
\[
\boxed{E_{\alpha,\gamma}(K_1)\cap K_0
\subseteq E_{\alpha,\gamma}(K_0).}\tag{OH.14}
\]

**Proof.** For every unit normal \(n\), \(h_{K_0}(n)\le h_{K_1}(n)\). Each inner quadrant is defined by a conjunction of strict inequalities \(p\cdot u<h_K(u)-1\), \(p\cdot v<h_K(v)-1\), so it grows under the support increase. The outgoing-strip *inner* violation \(p\cdot u_\alpha<h_K(u_\alpha)-1\) grows likewise, as does its correctly reflected counterpart. Taking unions over all visited angles preserves inclusion. If \(p\in E(K_1)\cap K_0\), it avoids the larger forbidden union, hence the smaller, and so survives \(K_0\). \(\square\)

**Theorem OH3 (exact ordinary-area outer-gain minus old-material loss).** For the same nested hulls and fixed turning endpoints,
\[
\boxed{\begin{aligned}
|E_{\alpha,\gamma}(K_1)|-|E_{\alpha,\gamma}(K_0)|
={}&\left|(K_1\setminus K_0)\setminus F_{\alpha,\gamma}(K_1)\right|\\
&-\left|E_{\alpha,\gamma}(K_0)
   \cap\big(F_{\alpha,\gamma}(K_1)\setminus
           F_{\alpha,\gamma}(K_0)\big)\right|.
\end{aligned}}\tag{OH.15}
\]
The first term counts **genuinely surviving newly added outer-hull material**; the second counts **previously surviving material rendered forbidden by the enlarged hull's shifted inner walls**.

**Proof.** By OH.14 the new survivor's portion inside the old hull is a subset of the old survivor. Decompose the new survivor disjointly into its portion inside \(K_0\) and outside \(K_0\), and subtract the old survivor's area. The inside difference is exactly the old survivor intersected with the enlarged forbidden set. Because the old survivor avoids \(F(K_0)\), this equals the second displayed region. The outside portion is exactly the first displayed region. All sets are measurable, with no assumption that either survivor is connected or has nonempty fibers. This is ordinary set-area accounting, not a signed-niche approximation. \(\square\)

**What would make this an optimality proof?** To show that a given candidate hull \(K_*\) cannot be improved by *every inclusion-enlargement* \(K\supseteq K_*\), it would suffice to construct a **global charge/injection** proving that the old-material shadow-loss term in OH.15 always dominates the newly surviving outer mass:
\[
\left|E(K_*)\cap(F(K)\setminus F(K_*))\right|
\ge\left|(K\setminus K_*)\setminus F(K)\right|.
\tag{OH.16, unproved}
\]
Even that inequality, if true, would settle only **inclusion-comparable outer enlargements**, not arbitrary competing hulls which intersect or lie partly inside \(K_*\). A global sharp comparison would need a broader transport or an integration along deformations whose area change is controlled; no such theorem is claimed.

The advantage of OH.15 as a research language is that the difficult mixed-niche credit \(G\) does not appear at all: newly forbidden lower and upper regions are **one union**, so overlap is automatically charged once. The distinction between old and newly attached material also prevents treating an outer hull increase as a sofa area increase. This is a strictly exact, universally valid gain/loss identity; by itself it is not stronger than the unsolved global area bound.

**Both signs actually occur.** For nested concentric disks \(K_{1/8}\subset K_{1/4}\) centered at height \(1/2\), both complete motions are feasible throughout the larger disk because its diameter is below one. Thus \(F(K_{1/4})\cap K_{1/4}=\varnothing\): the shadow-loss term is zero and OH.15 gives the strictly **positive** gain
\[
|E(K_{1/4})|-|E(K_{1/8})|
=\pi[(1/4)^2-(1/8)^2]=3\pi/64>0.
\]
By contrast, for the nested pair \(K_*\subset K_3\) of OH.9 the **net** change is strictly negative. Hence no bare inclusion principle \(|E(K_0)|\le|E(K_1)|\), or its reverse, can be valid on all convex hulls. A sharp reference comparison must use the *quantitative geometry* of the exact positive and negative terms of OH.15.

## 4. A correct self-consistent hull-first procedure

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

## 5. A genuine paid-shadow comparison for the reference's horizontal enlargement

The outer-minus-inner accounting is **not merely diagnostic** in every direction. The already established near-reference [NR.11–NR.12](near-reference-positive-minwidth-slack.md), based on the self-reviewed regular one-turn calibration, gives a **sharp ordinary-area comparison** for a one-parameter family of true full-turn envelopes.

Take the actual Romik reference hull \(K_*\) of vertical span one and, for \(0<\delta\le1/16\), form
\[
K_\delta=K_*+[-\delta/2,\delta/2]e_x.
\tag{OH.17}
\]
The area of the **outer convex hull** increases by exactly \(\delta\): every nonempty horizontal section is extended by a segment of length \(\delta\), and the y-projection has length one. Thus
\[
\boxed{|K_\delta|-|K_*|=\delta.}\tag{OH.18}
\]
But the fully canonically carved full-two-turn envelopes obey the already proved (subject to its cited regular-calibration dependencies)
\[
\boxed{|E(K_\delta)|\le M-\frac9{20}\delta^2<M
=|E(K_*)|.}\tag{OH.19}
\]
Define the **ordinary removed-inner-sweep area within the hull**
\(\mathcal R(K)=|K|-|E(K)|\); it counts the actual union of the two forbidden sweeps inside the hull and handles their overlap *once*. Subtract OH.18 and OH.19 to obtain the exact lower **payment**:
\[
\boxed{
\mathcal R(K_\delta)-\mathcal R(K_*)
\ge\delta+\frac9{20}\delta^2.
}\tag{OH.20}
\]
So every unit of new hull area is paid by **at least** one unit of newly removed inner-sweep area, with an additional explicit quadratic loss. This is a rigorous instance of the proposed hull-first proof mechanism at an actual analytic candidate, not a claim that the payment holds for *all* outward perturbations or arbitrary hulls.

In terms of the exact nested-shadow identity OH.15, the change in surviving ordinary area is at most \(-9\delta^2/20\); therefore the **old safe material made newly unsafe** outweighs the genuinely surviving new outer material by at least that amount. Extending this *sign* to all nested enlargements, and then to nonnested competitor hulls, remains an independent global research task.

## 6. The precise remaining optimality obligation

The geometric sequence **outer hull → canonical inner niches → ordinary area → support retightening** is correct and globally covers complete conventional turns. The true target is not
\(\max |K|\), but rather the *coupled* functional OH.11. A sharp proof would require a universal comparison showing
\[
|E(K)|\le M\quad\text{for every normalized convex }K,
\]
or a different joint calibration of the signed version. This is still **open**; the direct support-based outer/inner boundary first variations produce Romik's contact equations locally, but local stationarity alone does not prove global optimality.

The original unrestricted problem also permits proper **partial** terminal turning angles. The exact [OS1–OS2](original-motion-signed-convex-domain.md) formulation covers them by adding two independent terminal angles and both outgoing-strip constraints. Thus a truly unrestricted sharp theorem must either bound that larger objective or validly eliminate the partial-turn branch.

The result of this note is a clear *hull-first proof architecture* and an exact outer-only obstruction, **not** a claim that the missing globally sharp comparison has been supplied. No CI, Lean/Lake build, numerical optimizer or new global area certificate was run.
