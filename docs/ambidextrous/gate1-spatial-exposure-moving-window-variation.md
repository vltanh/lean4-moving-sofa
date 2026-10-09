# Gate 1 spatial maximizer: exact finite exposure balance and **moving-window endpoint pressures**

**Date October 9, 2026. Status:** A global-domain **necessary variational condition for finite angular polygonal maximizers** of the *one active* Gate 1 spatial score, not a proof of its sharp value. It does not prescribe a Romik contact chart, bound curvature by one, assume convexity of the spatial functional, or claim genuine feasible two-handed sofas are closed under arbitrary cap variations.

This note fixes a crucial difference from the branch's existing weighted one-turn maximizer proof: the moving spatial interval \(J=[l+W/4,r-W/4]\) generates **nonconstant end-face pressures involving both the outer roof and the true niche** at J's moving endpoints. Replacing them by the old width-penalty coefficient \(1/2\) is wrong away from Romik. **The October 9 endpoint audit corrects a second issue:** the isolated outward axis-wall formulas require a **positive-length end face**. A zero-length end face makes that axis constraint redundant, so relaxing it leaves the actual cap, width and window unchanged. The exact counterexamples and corrected finite laws are below. Gate 1 remains **ACTIVE and UNPROVED**.

The new [MID2 global chord reduction](gate1-global-middle-chord-canonicalization.md) independently guarantees that the active scalar value can be realized by a height-one cap with a **single affine central half-width roof**. The calculations here concern the two arbitrary exterior wings of selected finite polygons and do not convert this affine roof into an assumed horizontal top facet.

**Subsequent global consequence:** [EP1–EP3](gate1-global-endpoint-complementarity.md) combines these corrected outward laws with actual inward trimming and horizontal erosion. It proves exact continuum endpoint complementarity and the limiting exposure defect moments, while retaining the distinction between finite exposure limits and the actual positive niche graph. The sharp value remains unproved.

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

## 3. Move a positive-length vertical end face: an **exact moving-J boundary term**

**First assume \(e_R>0\).** Move only the side \(x\le r\) to \(x\le r+\varepsilon\), retaining **all** non-axis grid halfplanes. A relative-interior point of the positive vertical face has strict slack against the finitely many other nonparallel sides. Thus the actual right projection endpoint is \(r+\varepsilon\) for sufficiently small positive \(\varepsilon\). The finite niche function \(n_n(x)\) remains **identically unchanged at every fixed x**, since none of its source supporting normals is an axis normal: each old attaining point remains, and each old non-axis halfplane is retained. The added rightmost sliver has area \(\varepsilon e_R+O(\varepsilon^2)\).

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

Similarly, **when \(e_L>0\)**, moving only the **left** side \(x\ge l\) to \(x\ge l-\varepsilon\) yields
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
These are actual **outward** derivatives of a finite polygonal ordinary-area score, including the **width-dependent moving J**, under the respective positive-face hypothesis. They hold without symmetry and whether or not the finite niche is connected at any horizontal level. They are not automatically inward derivatives: an inward cut can remove the sole attaining point of another sampled support, even if the vertical face has positive length.

### 3a. Zero end faces: the axis wall does not move the body

Suppose \(e_R=0\), with U of positive area. Its last upper roof segment meets the floor at \((r,0)\), so one of the retained upper halfplanes has the form
\[
a(x-r)+b y\le0,\qquad a,b>0.
\]
Together with \(y\ge0\), this halfplane already implies \(x\le r\). Relaxing only the redundant vertical constraint therefore leaves **the entire polygon unchanged for every \(\varepsilon>0\)**. Its actual width and J are constant; the derivative is zero. Reflection gives the same conclusion when \(e_L=0\).

With \(\chi_R=1_{\{e_R>0\}}\), \(\chi_L=1_{\{e_L>0\}}\), and
\[
C_R=\tfrac34q_+-\tfrac14q_-,\qquad
C_L=\tfrac34q_--\tfrac14q_+,
\tag{FE.7a}
\]
the universally valid isolated-outward-wall derivatives are
\[
\boxed{D_R^+P_n=\chi_R(e_R-C_R),\qquad
D_L^+P_n=\chi_L(e_L-C_L).}
\tag{FE.7b}
\]
An axis-wall *parameter* is not the actual support coordinate when its constraint has become redundant.

**Exact rational-vertex counterexample to the former unconditional FE.6.** Let
\[
U=\operatorname{conv}\{(0,0),(0,1),(1,1),(2,0)\},\qquad n=2.
\]
The sole proper turning angle is \(\pi/4\); its supports are \(f=\sqrt2\), \(g=1/\sqrt2\), and its positive niche is
\[
n_2(x)=\bigl[\min(2-\sqrt2-x,\,1-\sqrt2+x)\bigr]_+.
\]
Here \(J=[1/2,3/2]\), \(e_R=0\), \(q_-=5/2-\sqrt2\), and \(q_+=1/2\). The former FE.6 would give
\[
e_R+q_-/4-3q_+/4=(1-\sqrt2)/4<0.
\]
The actual derivative is **zero**: the retained roof constraint \(x+y\le2\) and floor already imply \(x\le2\).

The omitted coefficient need not even have a fixed sign. For the \(n=3\) grid take
\[
U=\operatorname{conv}\{(0,0),(0,1),(\sqrt3,0)\}.
\]
Its upper facet normal is \(\pi/3\), and \(J=[\sqrt3/4,3\sqrt3/4]\). At \(t=\pi/6\) the two roofs are \(1-\sqrt3x\) and \(1-2/\sqrt3+x/\sqrt3\); the \(t=\pi/3\) first roof is nonpositive for \(x\ge0\). Thus \(q_-=2-2/\sqrt3\), \(q_+=1/4\), \(e_R=0\), and the formerly claimed derivative is
\[
5/16-1/(2\sqrt3)>0,
\]
whereas relaxing the redundant right wall again leaves the cap unchanged. These examples refute the **unconditional derivative claim**; neither example is asserted to be a global maximizer or a counterexample to the sharp score bound.

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
e_R&\le\chi_R(C_R+b_{n,0}),\\
e_L&\le\chi_L(C_L+b_{n,2n}).
\end{aligned}}\tag{FE.9}
\]
In particular, the two **unconditional** axis bounds are
\[
e_R\le(C_R+b_{n,0})_+,\qquad
e_L\le(C_L+b_{n,2n})_+.
\tag{FE.9a}
\]
**When both end faces have positive length**, adding the two axis bounds gives
\[
\boxed{
e_R+e_L\le\frac12(q_-+q_+)+b_{n,0}+b_{n,2n}.
}\tag{FE.10}
\]

For arbitrary end faces, the valid summed bound is instead the sum of FE.9a's two positive parts. The original FE.10 is not inferred when an end face vanishes.

**Proof.** When the artificial box sides are inactive, each positive-length floating or axis facet admits an outward variation changing exactly its own sampled support coordinate. FE.5–FE.7 and the bounded penalty derivatives give the corresponding inequalities. At zero floating length the first inequality is trivial. At zero axis length the actual polygon and every actual support stay fixed by Section 3a, so the indicator form reads \(0\le0\). This proves FE.9 and hence FE.9a. Add the two positive-face inequalities for the stated conditional FE.10. \(\square\)

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

The subsequent RG regularity theorem and [EP1–EP3](gate1-global-endpoint-complementarity.md) establish uniform wing control and exact limiting finite-exposure moments using additional arguments. Identifying the actual positive continuum niche geometry and proving the global sharp scalar inequality remain open. **Neither follows from FE.13 by uniform roof convergence.**

## 6. Why this is part of the active global Gate 1 proof, not a separate class

The corrected FE1 applies to **every finite global maximizer** of the exact **spatial objective** over a fixed broad support grid, with no candidate-neighborhood restriction. Its floating-facet inequality, used by RG2–RG3 and FE.13, is unchanged. The axis inequalities now retain the necessary positive-face indicators or positive parts. The two side-face pressures are functions of **actual outer and niche heights at the moving central-window endpoints**; the signed width penalty's constant half-face formula **does not transfer**.

The new global chord reduction MID2 says the true scalar maximizer can be chosen with a complete affine middle roof. In future finite selections one must retain that canonical form or prove it is inherited in the relevant limit, and carry FE.9's moving-window terms consistently. Without the full sharp \(P\le M/2\) value proof, **Gate 1 is still ACTIVE** and no improved unrestricted area upper bound is obtained.

No CI, Lean/Lake, sample-based certification, or claim of optimality. The proof is purely elementary finite polygon geometry plus exact differentiation of moving integration domains.
