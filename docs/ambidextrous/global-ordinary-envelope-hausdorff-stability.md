# Global ordinary-envelope stability: a uniform Hausdorff-to-area certificate

**October 9, 2026.** This theorem covers **all** planar compact convex hulls inside one normalized incoming width-one horizontal strip, including arbitrary opposite-end top/bottom faces, disconnected canonical envelopes, all moving sharp-corner switches, nonsmooth or atomic curvature, and non-reference contact geometry. It controls the **total ordinary area of the complete two-handed canonical envelope**, not the signed functional. It does **not** prove the sharp Romik value; it provides a rigorous global *perturbation/certification* inequality that a future finite global area certificate may exploit.

## 1. Statement

Fix a rectangle \(R=[l,r]\times[0,1]\), \(W=r-l\), and two nonempty compact convex sets \(K,K'\subset R\), each of horizontal projection \([l,r]\) (the proof actually does not need exact full projection). Let \(E(K)\) mean the intersection of \(K\) with **all** lower and upper complete conventional quarter-turn canonical supporting-L-hallway constraints \(t\in[0,L]\), \(L=\pi/2\). The envelope need not be connected or have hull K. Let
\[
\varepsilon=d_{\rm H}(K,K')=\|h_K-h_{K'}\|_{\infty(\mathbb S^1)}.
\]

Define \(B(W,\tau)\), \(0<\tau<L/2\), by the explicit **all-hull** endpoint-deletion estimate [EC2](actual-startup-carving-and-cubic-endpoint-saving.md):
\[
\begin{gathered}
 V=(W-1)_+,\quad Z=\tan\tau,\quad k=\sec\tau-1,\quad
 \lambda(\tau)=\tan(\tau/2)-\tau/2,\\
 B(W,\tau)=2\lambda(\tau)+\frac Z2
 \left[V^2-\frac{(V-k)_+^2}{1+Z^2}\right].
\end{gathered}
\tag{GS.1}
\]

**Theorem GS1 (global ordinary-area perturbation modulus).** For every such \(K,K'\), every \(0<\tau<\pi/4\), and every \(\varepsilon\ge0\),
\[
\boxed{
\bigl||E(K)|-|E(K')|\bigr|
\le 4(W+1)\varepsilon+2\pi\varepsilon^2+
\frac{2W\varepsilon}{\sin\tau}+8B(W,\tau).
}
\tag{GS.2}
\]
The same bound holds for the **symmetric difference**
\[
\boxed{|E(K)\triangle E(K')|
\le4(W+1)\varepsilon+2\pi\varepsilon^2+
\frac{2W\varepsilon}{\sin\tau}+8B(W,\tau).}
\tag{GS.3}
\]

In particular for fixed \(W\), because \(B(W,\tau)=O_W(\tau^3)\), choosing \(\tau=\varepsilon^{1/4}\) for sufficiently small \(\varepsilon>0\) gives
\[
\boxed{|E(K)\triangle E(K')|=O_W(\varepsilon^{3/4}).}
\tag{GS.4}
\]
This is a **uniform, contact-free modulus** on the full normalized hull domain, not a mere qualitative semicontinuity claim. The exponent is an upper estimate, not asserted optimal.

## 2. Ordinary clipping is handled exactly

For \(t\in(0,L)\), define \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\). At any abscissa \(x\), the actual **lower forbidden quadrant** is the vertical half-line
\[
y<T_K(t,x):=\min\left\{
\frac{h_K(u_t)-1-x\cos t}{\sin t},\
\frac{h_K(v_t)-1+x\sin t}{\cos t}\right\}.
\tag{GS.5}
\]
Here \(T_K\) may be negative, and no positivity truncation is made before comparing envelopes. Define the interior-angle lower roof
\[
n_K^\tau(x)=\max_{\tau\le t\le L-\tau}T_K(t,x).
\]
The upper-handed half-line is the vertical reflection of the same expression for \(\rho K=\{(x,1-y):(x,y)\in K\}\). The exact interior-angle canonical mask is the vertical strip between these two roofs:
\[
M_K^\tau=\{(x,y)\in R:\ y\ge n_K^\tau(x),\
 y\le1-n_{\rho K}^\tau(x)\},
\qquad E^\tau(K)=K\cap M_K^\tau .
\tag{GS.6}
\]
This equality holds even if the two thresholds cross (then the fiber is empty), and even if the forbidden niche lies **outside** the hull. It explicitly retains actual ordinary clipping.

Because \(|h_K(n)-h_{K'}(n)|\le\varepsilon\) for every unit normal,
each wall threshold in GS.5 changes by at most
\[
\varepsilon/\min(\sin t,\cos t)\le\varepsilon/\sin\tau.
\]
The minimum of two real quantities and maximum over all \(t\) are both 1-Lipschitz in their uniform norms. Thus
\[
\boxed{\|n_K^\tau-n_{K'}^\tau\|_{L^\infty(I)}
\le\varepsilon/\sin\tau,}
\tag{GS.7}
\]
and the same holds for the reflected upper roof. It follows by vertical Fubini that
\[
\boxed{|(M_K^\tau\triangle M_{K'}^\tau)\cap R|
\le2W\varepsilon/\sin\tau.}
\tag{GS.8}
\]
No active-ray label, corner-x monotonicity, or regularity of the maximizer angle is used.

For the outer-hull symmetric difference, the Hausdorff inclusions
\(K\subseteq K'+\varepsilon B_2\) and \(K'\subseteq K+\varepsilon B_2\)
give
\[
|K\triangle K'|
\le |(K+\varepsilon B_2)\setminus K|
 + |(K'+\varepsilon B_2)\setminus K'|.
\tag{GS.9}
\]
Steiner's exact planar convex parallel-body formula bounds each difference by \(\varepsilon P+\pi\varepsilon^2\), and **every convex subset of R** has perimeter at most \(P(R)=2(W+1)\) (by Cauchy's perimeter projection formula or the convex-body perimeter monotonicity). Hence
\[
\boxed{|K\triangle K'|\le4(W+1)\varepsilon+2\pi\varepsilon^2.}
\tag{GS.10}
\]

Now use
\[
(K\cap M_K^\tau)\triangle(K'\cap M_{K'}^\tau)
\subseteq (K\triangle K')\cup(M_K^\tau\triangle M_{K'}^\tau).
\]
Equations GS.8 and GS.10 give
\[
\boxed{|E^\tau(K)\triangle E^\tau(K')|
\le4(W+1)\varepsilon+2\pi\varepsilon^2+
 2W\varepsilon/\sin\tau.}
\tag{GS.11}
\]

## 3. Restore **all four** angular endpoint intervals

The full \(E(K)\subseteq E^\tau(K)\) differs from it only by the intervals \([0,\tau)\) and \((L-\tau,L]\) for each of the two hands. The [EC2 whole-hull endpoint bound](actual-startup-carving-and-cubic-endpoint-saving.md), valid even after intersecting an arbitrary fixed collection of other constraints, implies
\[
\boxed{|E^\tau(K)\setminus E(K)|\le4B(W,\tau)}
\tag{GS.12}
\]
and likewise for K'. Thus
\[
E(K)\triangle E(K')
\subseteq
[E^\tau(K)\triangle E^\tau(K')]
\cup[E^\tau(K)\setminus E(K)]
\cup[E^\tau(K')\setminus E(K')],
\]
and GS.11–GS.12 prove GS.3. The area difference is bounded by symmetric difference, proving GS.2.

For \(0<\varepsilon<(\pi/4)^4\), take \(\tau=\varepsilon^{1/4}\), use
\(\sin\tau\asymp\tau\), \(B(W,\tau)=O_W(\tau^3)\), and obtain GS.4. At \(\varepsilon=0\), the stronger trivial identity \(E(K)=E(K')\) holds; GS.2 can be made arbitrarily small by letting \(\tau\downarrow0\).

## 4. Why this advances the global proof program without pretending to close it

For a **finite epsilon-net of arbitrary normalized hulls** (after discretization of their support functions and choosing polygonal outer hull representatives), GS.2 converts each certified exact or interval area bound at a net hull into a uniform **whole-cell ordinary-area upper bound**. This directly includes the non-Romik, opposite-end-face configurations whose supremum is known to equal the full-turn supremum.

The theorem is independent of the need for **actual-hull admission** of the net representatives: \(E(K)\) is defined for any convex hull, even if its full envelope is disconnected or its extreme vertices are carved. For every actual full-turn sofa S, \(S\subseteq E(\operatorname{conv}S)\), so a bound on all envelope areas is safely stronger than a bound on actual sofas. One must nevertheless **not** infer that the supremum of these unrestricted envelope areas is M: infeasible hulls might generate extraneous disconnected envelopes and require a more selective net/certificate.

One also must not mistake GS.2 for an area-value upper bound: its right-hand side vanishes only when the two hulls agree and \(\tau\to0\), and does not compare either area to Romik without a global certificate. It does not treat genuinely partial turning intervals with correct outgoing straight-arm constraints; those remain independent.

There are **no computer tests claimed for GS1**. The argument is an explicit elementary proof assembled from exact Fubini slicing, Hausdorff support continuity, convex perimeter monotonicity, Steiner's area formula, and the earlier proved whole-hull cubic endpoint relaxation EC2. Neither CI nor Lean/Lake was run.
