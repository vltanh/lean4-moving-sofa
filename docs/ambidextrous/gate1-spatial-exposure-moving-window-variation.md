# Gate 1 spatial maximizer: exact finite exposure balance and **moving-window endpoint pressures**

**Date October 9, 2026. Status:** A global-domain **necessary variational condition for finite angular polygonal maximizers** of the *one active* Gate 1 spatial score, not a proof of its sharp value. It does not prescribe a Romik contact chart, bound curvature by one, assume convexity of the spatial functional, or claim genuine feasible two-handed sofas are closed under arbitrary cap variations.

This note fixes a crucial difference from the branch's existing weighted one-turn maximizer proof: the moving spatial interval \(J=[l+W/4,r-W/4]\) generates **nonconstant end-face pressures involving both the outer roof and the true niche** at J's moving endpoints. Replacing them by the old width-penalty coefficient \(1/2\) is wrong away from Romik. Every displayed variational formula here is exact for a **finite-angle** cap polygon. A separate uniform passage to the complete angular continuum is still required before using them to characterize any global continuum maximizer. Gate 1 remains **ACTIVE and UNPROVED**.

The new [MID2 global chord reduction](gate1-global-middle-chord-canonicalization.md) independently guarantees that the active scalar value can be realized by a height-one cap with a **single affine central half-width roof**. The calculations here concern the two arbitrary exterior wings of selected finite polygons and do not convert this affine roof into an assumed horizontal top facet.

## 1. Finite-polygon spatial objective; keep the center interval moving

Let \(L=\pi/2\), \(I=[l,r]\), \(W=r-l>0\), and
\[
j_-=l+W/4=\tfrac34 l+\tfrac14r,\qquad
j_+=r-W/4=\tfrac14 l+\tfrac34r.
\tag{FE.1}
\]
Take a convex downward polygon \(U\) of height at most one, defined as intersection of \(y\ge0\) with finitely many supporting halfplanes, including the horizontal normal \(e_y\), both vertical sides \(x=l,r\), and a grid of upper support normals
\(\theta_j=j\pi/(2n)\), \(j=0,\ldots,2n\). The outer upper roof \(A(x)\) is concave and continuous at both interior abscissae \(j_\pm\).

Use *only* the finite physical turning angles \(t_j=j\pi/(2n)\), \(j=1,\ldots,n-1\), and denote their entire **two-ray positive forbidden roof** by
\[
n_n(x)=\left[\max_{1\le j<n}
\min\left(\frac{h_U(u_{t_j})-1-x\cos t_j}{\sin t_j},
\frac{h_U(v_{t_j})-1+x\sin t_j}{\cos t_j}\right)\right]_+ .
\tag{FE.2}
\]
The finite spatial score is
\[
\boxed{P_n(U)=\int_l^{j_-}A\,dx+
\int_{j_+}^r A\,dx-
\int_{j_-}^{j_+}n_n\,dx.}\tag{FE.3}
\]
All three integrals use true ordinary vertical heights; no signed-curve formula, candidate contact phases, or sampled-angle area assumption enters FE.3.

For a non-top source normal \(\theta_j\), \(j\notin\{0,n,2n\}\), let
- \(\ell^{\rm wing}_j\) be the total **actual outer facet arclength** lying over the charged exterior quarters \(I\setminus J\);
- \(\tau^{\rm middle}_j\) be the arclength of positive-height **exposed inner-wall boundary pieces** of the full finite union, supported by the inner wall of that source normal and having horizontal abscissa within \(J\).

Boundary points at J's endpoints and at ray intersections do not contribute arclength ambiguities. If the outer facet is absent, set \(\ell^{\rm wing}_j=0\).

Let \(e_R=A(r)\), \(e_L=A(l)\) be the lengths of the **right/left vertical end facets** (possibly zero), and abbreviate
\[
q_-=A(j_-)+n_n(j_-),\qquad
q_+=A(j_+)+n_n(j_+).
\tag{FE.4}
\]

## 2. Move a single floating facet outward: the **charged** exposure inequality

Fix a non-top, non-axis grid source normal \(\theta_j\) and move *only* its supporting line outward by \(\varepsilon>0\), preserving every other grid side, the floor, the top height constraint, and both horizontal axis supports. For small \(\varepsilon\), the new polygon has the **same W and same middle J**, and the support at \(\theta_j\) grows by exactly \(\varepsilon\) when the old facet has positive length. All other sampled supports remain unchanged because their old attaining points stay in the enlarged body and their original halfplanes remain.

Moving the outer facet gains an area strip of first-order area \(\varepsilon\ell^{\rm wing}_j\) over the **exterior wings**. The finite union of inner forbidden quadrants changes by moving **one inner line** of the unique corresponding t_j angle; its newly swept, unmasked **positive-height boundary pieces inside J** contribute exactly \(\varepsilon\tau^{\rm middle}_j\). All intersections of distinct nonparallel source lines, the floor, or the fixed window endpoints contribute only \(O(\varepsilon^2)\) ordinary area. Thus
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{\varepsilon=0+}
=\ell^{\rm wing}_j-\tau^{\rm middle}_j
\quad\text{when the facet is positive length.}
}\tag{FE.5}
\]
A zero-length facet has \(\ell^{\rm wing}_j=0\), and needs no differentiability claim. In particular *the weighted one-turn exposure measure is not the right one here*: it counts the **entire** niche and the **entire** outer facet, while FE.5 counts only the two **charged spatial portions**.

## 3. Move the rightmost vertical wall: an **exact moving-J boundary term**

Move only the side \(x\le r\) to \(x\le r+\varepsilon\), retaining **all** non-axis grid halfplanes. The finite niche function \(n_n(x)\) remains **identically unchanged at every fixed x**, since none of its source supporting normals is an axis normal. The old polygon is retained, and the added rightmost sliver has area \(\varepsilon e_R+O(\varepsilon^2)\).

But W increases by \(\varepsilon\), so both endpoints of the **middle** window move:
\[
j_-(\varepsilon)=j_-+\varepsilon/4,\qquad
j_+(\varepsilon)=j_++3\varepsilon/4.
\]
Differentiate FE.3 using continuity of A and \(n_n\) at the moving window endpoints:
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{0+}
=e_R+\frac14q_- -\frac34q_+.
}\tag{FE.6}
\]
The terms \(q_\pm\) are **A+n**, not A-n. The + sign on n is forced by subtracting the integral over the moving central interval.

Similarly moving only the **left** side \(x\ge l\) to \(x\ge l-\varepsilon\) yields
\[
j_-(\varepsilon)=j_--3\varepsilon/4,\qquad
j_+(\varepsilon)=j_+-\varepsilon/4,
\]
and therefore
\[
\boxed{
\left.\frac{d}{d\varepsilon}P_n(U_\varepsilon)
\right|_{0+}
=e_L-\frac34q_-+\frac14q_+.
}\tag{FE.7}
\]
These are actual derivatives of a finite polygonal ordinary-area score, including the **width-dependent moving J**. They hold without symmetry and whether or not the full niche is connected at any horizontal level.

## 4. First-order constraints at a globally selected finite maximizer

To state a clean theorem, fix an artificial broad box \([-R,R]\times[0,1]\), with all sides of U strictly inside its vertical walls, and maximize
\[
P_n(U)-\eta_n\sum_{j=0}^{2n}w_j[h_U(\theta_j)-h_{*,j}]^2
\tag{FE.8}
\]
over upper-grid convex polygons, where \(\eta_n\ge0\), \(w_j\ge0\), and \(\sum w_j\le1\). All samples use the **same** actual support function; the penalty is not inserted into the geometric area definition.

At a maximizer, a permitted outward variation has nonpositive objective derivative. If all support values are bounded by \(B\), the absolute penalty derivative at j is at most \(4B\eta_nw_j\). Therefore FE.5–FE.7 imply:

**Theorem FE1 (global finite-polygon spatial pressure constraints).** Put \(b_{n,j}=4B\eta_nw_j\ge0\). Then
\[
\boxed{\begin{aligned}
\ell^{\rm wing}_j&\le\tau^{\rm middle}_j+b_{n,j}
&& (j\notin\{0,n,2n\}),\\
e_R&\le\frac34q_+-\frac14q_-+b_{n,0},\\
e_L&\le\frac34q_--\frac14q_++b_{n,2n}.
\end{aligned}}\tag{FE.9}
\]
Consequently
\[
\boxed{
e_R+e_L\le\frac12(q_-+q_+)+b_{n,0}+b_{n,2n}.
}\tag{FE.10}
\]

**Proof.** Outward variations are available for sufficiently small \(\varepsilon\) when the artificial box sides are inactive. Positive-length facet source supports change in exactly one penalized coordinate. At zero length, the first inequality is trivial. The two axis variations change only their own sampled support coordinates, since every other halfplane is kept. The explicit derivative formulas FE.5–FE.7 and the bounded penalty derivatives give the inequalities. Add the last two for FE.10. \(\square\)

**Sharp reference calibration:** Romik's cap has right and left end heights \(e_R=e_L=1/2\), and at the central-half face endpoints \(A(j_\pm)=1\), \(n(j_\pm)=0\). The limiting (unpenalized) axis formulas therefore read \(1/2=3/4-1/4\) at both ends. This is the precise replacement for the old constant \(1/2\) weighted-one-turn endpoint condition, but **only at the reference** do its two moving-window pressures collapse to that constant.

## 5. The finite outer/inner **projection budget** and the exact limit warning

A polygon upper facet with normal \(\theta_j\) has horizontal projected length \(\ell_j\sin\theta_j\); its charged exterior contribution is \(\ell^{\rm wing}_j\sin\theta_j\). Let \(T_{\rm wing}\) be the total horizontal length of any **horizontal top-face segment lying outside J**. Horizontal projection of all upper exterior graph pieces gives the **exact identity**
\[
\boxed{
\sum_{j\notin\{0,n,2n\}}
\ell^{\rm wing}_j\sin\theta_j
=\frac W2-T_{\rm wing}.
}\tag{FE.11}
\]
The first- and second-wall exposed positive niche graph pieces have horizontal projections \(\tau^{\rm middle}_j\sin\theta_j\). Each exposed ray line has horizontal projection **strictly monotone** with x, and the upper boundary of the finite niche over J is a single graph. There are no positive-length source-line coincidences between distinct sampled angles. Consequently
\[
\boxed{
\sum_{j\notin\{0,n,2n\}}
\tau^{\rm middle}_j\sin\theta_j
=\left|\{x\in J:n_n(x)>0\}\right|.
}\tag{FE.12}
\]
Multiply the first inequality of FE.9 by \(\sin\theta_j\), sum, and use \(\sum b_{n,j}\le4B\eta_n\):
\[
\boxed{
\left|\{x\in J:n_n(x)=0\}\right|
\le T_{\rm wing}+4B\eta_n.
}\tag{FE.13}
\]
This is a nontrivial **whole-upper-profile, whole-finite-niche projection restriction** at every selected finite maximizing polygon; it is not an assumption of positive middle niche support or a candidate contact phase.

**Mandatory limit warning:** It is **invalid** to pass FE.13 to the angular continuum by merely using uniform convergence of niche roofs. The indicator of \(\{n_n=0\}\) is not continuous under uniform convergence; arbitrarily shallow positive roofs can converge uniformly to a roof that is zero on a long interval. The weighted half-face proof [HF](one-turn-half-width-top-face.md) needed a separate endpoint support-derivative estimate to control precisely this loss of niche projection. Such a theorem for the **different** spatial P maximizer has *not* yet been proved here. Thus FE.13 is a rigorously proved **finite** structural condition, **not** a claim that an actual infinite-angle maximizer has a fully exposed central niche.

A viable Gate 1 proof must extract uniform geometry/curvature control from FE.9, justify an exact limiting exposure balance on the **spatially charged** portions, and then prove the global sharp scalar inequality. **None of those missing steps is silently inferred from FE.13.**

## 6. Why this is part of the active global Gate 1 proof, not a separate class

FE1 applies to **every finite global maximizer** of the exact **spatial objective** over a fixed broad support grid, with no candidate-neighborhood restriction. It identifies the right contact pressure system for the *only active* G1.SD2 claim. Its most important new feature is that the two side-face pressures are functions of **actual outer and niche heights at the moving central-window endpoints**; the signed width penalty's constant half-face formula **does not transfer**.

The new global chord reduction MID2 says the true scalar maximizer can be chosen with a complete affine middle roof. In future finite selections one must retain that canonical form or prove it is inherited in the relevant limit, and carry FE.9's moving-window terms consistently. Without the full sharp \(P\le M/2\) value proof, **Gate 1 is still ACTIVE** and no improved unrestricted area upper bound is obtained.

No CI, Lean/Lake, sample-based certification, or claim of optimality. The proof is purely elementary finite polygon geometry plus exact differentiation of moving integration domains.
