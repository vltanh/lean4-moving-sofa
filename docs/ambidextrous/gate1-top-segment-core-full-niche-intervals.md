# Gate 1: exact global top-segment core and **whole-inner-ray interval transport**

**October 9, 2026.** An all-cap, all-angle geometric identity for the **one active Gate 1 spatial objective** [SD.2](gate1-spatial-dual-height-width-compactness.md). No curvature bound, reference neighborhood, symmetry, contact chart, or finite angle sampling is used. It reduces *every* positive-top-face cap to a downward convex point-top core plus one horizontal-segment parameter and expresses the **complete swept inner-wall area** through a moving union of one-dimensional intervals. Because any point-top cap is a Hausdorff limit of positive-top-face caps obtained by adding arbitrarily short horizontal segments, the resulting global value problem is **equivalent** to the active score supremum.

**THE SHARP INEQUALITY REMAINS OPEN.** This is a reduction of the global input geometry, not a numerical improvement to the unrestricted sofa bound, not a way of discarding changing interval overlaps, and not a proof of Romik optimality. The no-overcounting requirement is explicit throughout.

## 1. Exact Minkowski decomposition, without optimizer assumptions

Let \(U\subset\mathbb R\times[0,1]\) be a nonempty compact **downward-closed convex** cap of *height exactly one*, with horizontal projection \(I=[l,r]\), width \(W=r-l>0\) and a nondegenerate top exposed horizontal face
\[
F=[a,b]\times\{1\},\qquad T=b-a>0.
\]
For each \(0\le y\le1\), its horizontal section is a closed interval
\[
U_y=[L(y),R(y)].
\]
Since every top-face point \((x,1)\), \(a\le x\le b\), belongs to U and U is downward closed,
\[
\boxed{[a,b]\subseteq U_y\quad\text{for every }0\le y\le1.}\tag{HT.1}
\]
Thus every horizontal section has length at least T. Define the erosion/core
\[
\boxed{
V=U\ominus([0,T]e_x)
=U\cap(U-Te_x).
}\tag{HT.2}
\]
The equality holds because a segment fits into a convex set at p precisely when both segment endpoints fit. The core is compact, convex, downward closed, still of height one, and has sections
\[
\boxed{V_y=[L(y),R(y)-T].}\tag{HT.3}
\]
In particular, its top face is the **single point** \((a,1)\), and its width is \(w=W-T\ge0\). Adding the horizontal segment restores U section-by-section:
\[
\boxed{U=V+[0,T]e_x.}\tag{HT.4}
\]
This uses no maximizing property; the similar rectangular core [HF2](one-turn-half-width-top-face.md) was previously proved for a *weighted optimizer after vertical extrusion*. Here horizontal erosion is valid for **all** positive-top-face caps, including those of subunit vertical height after the active Gate 1 score's own vertical extrusion.

If U has a **point** top face, put \(U_\varepsilon=U+[0,\varepsilon]e_x\). These are downward height-one caps with positive top-face length \(\varepsilon\) and \(U_\varepsilon\to U\) in Hausdorff distance. By [SD3](gate1-spatial-dual-height-width-compactness.md), the complete spatial score \(\mathcal P\) is continuous on the relevant bounded cap domain. Consequently
\[
\boxed{
\sup_{\text{all downward caps}}\mathcal P
=
\sup_{\substack{V\text{ downward, height one, point top}\\T>0}}\mathcal P(V+[0,T]e_x).
}\tag{HT.5}
\]
The reference cap belongs to this family, so there is no loss of the target equality witness. This is a supremum identity, **not** an assertion that an area-maximizing cap necessarily has a positive top face.

## 2. The full two-ray forbidden intervals shift in one coordinate by exactly T

For the **point-top core** V, abbreviate its two true upper supporting values
\[
f_V(t)=h_V(\cos t,\sin t),\qquad
g_V(t)=h_V(-\sin t,\cos t),\qquad0<t<L=\pi/2.
\]
The Minkowski sum HT.4 gives the exact support identities
\[
\boxed{
f_U(t)=f_V(t)+T\cos t,\qquad
g_U(t)=g_V(t).
}\tag{HT.6}
\]
The full one-angle downward forbidden quadrant of U is described at height \(y\ge0\) by
\[
\boxed{\begin{aligned}
x&> a_t^V(y):=\frac{1-g_V(t)+y\cos t}{\sin t},\\
x&< b_t^V(y)+T,\qquad
b_t^V(y):=\frac{f_V(t)-1-y\sin t}{\cos t}.
\end{aligned}}\tag{HT.7}
\]
Both endpoints depend on the actual **outer support** of V; no assumed corner-height unimodality or selected exposed wall is present.

Thus the **entire** horizontal section of the continuous moving two-inner-ray niche of U, at every \(y>0\), is exactly
\[
\boxed{
N_y(U)
=\bigcup_{0<t<\pi/2}
\bigl(a_t^V(y),\,b_t^V(y)+T\bigr),
}\tag{HT.8}
\]
where an interval is interpreted as empty if its left endpoint is not smaller than its right endpoint. It is permissible for the union to be disconnected, to have any countable number of components, and for its active angular parameters to change many times with y and T. The formula is a **union**, never a sum of its separate interval lengths.

Because each interval's right endpoint shifts by **exactly** T while its left endpoint stays fixed, we also have the global set containment
\[
\boxed{
N_y(U)\supseteq N_y(V)+[0,T]\qquad(y>0).
}\tag{HT.9}
\]
Proof: for each fixed t, \((a_t,b_t)+[0,T]=(a_t,b_t+T)\) and the latter is an angle-t forbidden interval of U; take the union. This is also the direct support-depth observation that Minkowski addition of a **horizontal segment** increases the first inner-wall depth by \((T-\delta)\cos t\ge0\) and the second by \(\delta\sin t\ge0\) at a translated forbidden point \(p+\delta e_x\).

One exact consequence, useful for screening overly optimistic niche-reduction transformations, follows from the one-dimensional Brunn–Minkowski inequality: for every y with nonempty positive niche section of V,
\[
|N_y(U)|\ge|N_y(V)|+T.
\]
Let \(H_N(V)=\sup\{y>0:N_y(V)\ne\varnothing\}\) (zero for empty niche). The downward-closed nature of every quadrant means those nonempty levels occupy the interval \((0,H_N(V))\), up to endpoints. Integrating yields the **global ordinary-area inequality**
\[
\boxed{|N(U)|\ge|N(V)|+T\,H_N(V).}\tag{HT.10}
\]
This is not claimed sharp at Romik; the niche of a point-top core can have zero positive height even though adding T creates a substantial new niche. It does **not** prove the sharp Gate 1 spatial bound.

## 3. Exact **one-dimensional Gate 1** formula, without clipping mistakes

Let the point-top core V have horizontal projection \([l,l+w]\), height one, and sections \(V_y=[L(y),R(y)]\). The cap \(U_T=V+[0,T]e_x\) has width \(W=w+T\), projection \([l,l+w+T]\) and moving central middle-half interval
\[
J_T=[j_-,j_+],\quad
j_-=l+\frac{w+T}{4},\quad
j_+=l+\frac{3(w+T)}4.
\tag{HT.11}
\]

At physical height \(0\le y\le1\), the *actual outer cap material in the charged left and right wings* is exactly
\[
\boxed{
E_{V,T}(y)=
\bigl(\min\{j_-,R(y)+T\}-L(y)\bigr)_+
+\bigl(R(y)+T-\max\{j_+,L(y)\}\bigr)_+.
}\tag{HT.12}
\]
This is the ordinary intersection length of \(V_y+[0,T]\) with the two **outer** quarters \([l,j_-]\cup[j_+,l+w+T]\); it is never a signed graph approximation.

At each \(y>0\), the charged *entire moving two-ray niche* section is
\[
\boxed{
C_{V,T}(y)
=\left|
J_T\cap
\bigcup_{0<t<\pi/2}
\bigl(a_t^V(y),b_t^V(y)+T\bigr)
\right|.
}\tag{HT.13}
\]
The exact spatial Gate 1 score therefore has the **Fubini identity**
\[
\boxed{
\mathcal P(U_T)=\int_0^1 E_{V,T}(y)\,dy
-\int_0^\infty C_{V,T}(y)\,dy.
}\tag{HT.14}
\]
This remains valid if \(N_y\) has several disconnected intervals, if the active corner path folds, if the cap has support atoms, or if the original two-handed common-hull envelope would be disconnected. It uses the scalar score from SD.2, not an invented ordinary two-handed area formula.

**Exact restatement of the still-unproved sharp scalar Gate 1 target:**
\[
\boxed{
\int_0^1 E_{V,T}(y)\,dy
-\int_0^\infty C_{V,T}(y)\,dy
\ \stackrel{?}{\le}\ M/2
\quad\text{for every point-top downward convex V and }T>0.
}\tag{HT.15 — OPEN}
\]
There is no known proof of HT.15, and HT.10 alone is far too weak to establish it. HT.15 is a true one-dimensional interval-*union* formulation equivalent to [SD.3] at the level of suprema; it does not replace the separate real physical two-handed clipping loss by a bogus sum.

**Global Gate 1 status unchanged: ACTIVE, NOT PASSED.** If HT.15 is established it yields SD.3, which via [SD1](gate1-spatial-dual-height-width-compactness.md) proves the complete-turn sharp upper bound. Independently handling the actual two partial angles remains Gate 2. No numerical upper bound has improved, no above-M sofa was verified, no CI or Lean was run. The note is a written mathematical derivation requiring external scrutiny.
