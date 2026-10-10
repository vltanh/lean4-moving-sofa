# Gate 1.1 audited: complete physical inner-ray losses live on facets; actual polygonal full-turn hulls are area-value dense

**Date:** October 9, 2026. **Status:** A complete, self-reviewed, elementary **global-domain reduction for the actual full-conventional-two-turn problem**, not a sharp optimality inequality. Sections 1–2 independently audit the previously written [FT1–FT8 facet-triangle theorem](global-facet-triangle-niche-decomposition.md), including oblique bases and their upper-roof truncation issue. Section 3 proves a new **all-feasible-sofa area-density result for polygonal actual hulls**, without assuming that smoothing or circumscribed polygon approximation preserves physical feasibility.

**Main consequence:** To prove the complete-turn sharp area bound \(M\) (Gate 1), it is **mathematically sufficient and equivalent** to prove the exact coupled facet-sweep area inequality on **every finite polygon which is the actual hull of a compact connected full-turn sofa**. This rigorously removes a separate infinite-facet/singular-boundary **coverage** problem from the chosen proof architecture. **The needed sharp facet-area inequality itself is NOT proved**, so Gate 1 is NOT passed, the unrestricted upper bound has NOT improved, and partial-turn Gate 2 remains blocked.

No Leh/Lake, CI, infinite-angle simulation or numerical optimization is part of these proofs.

## 1. One-angle lower forbidden region on the actual hull

Let S be a compact connected planar body with **both complete conventional \(90^\circ\) supporting-hallway motion families** in the incoming strip \(0\le y\le1\), and let \(K=\operatorname{conv}S\). Its horizontal projection is \(I=[l,r]\), and its lower and upper convex-hull roofs are respectively \(B(x)\) (convex) and \(A(x)\) (concave).

For \(0<t<L=\pi/2\) set
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),
\]
\[
q_t(x)=\min\left\{
\frac{h_K(u_t)-1-x\cos t}{\sin t},
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\right\}.
\tag{PG.1}
\]
The **exact** one-angle clipped lower cut has \(x\)-section
\[
K_x\cap\{y<q_t(x)\}
=[B(x),\min(A(x),q_t(x)))\qquad
\text{if }q_t(x)>B(x),
\]
and is empty otherwise. As an arbitrary auxiliary hull could have \(q_t>A\), the minimum cannot be dropped without **actual-feasibility**.

For a true full-turn hull, however, canonical support tightening gives \(S\subseteq E_{\rm full}(K)\), and connectedness means \(S\) meets every vertical line in I. Hence for every \(x\in I\), a surviving point has \(y\ge q_t(x)\) and \(y\le A(x)\). Thus
\[
q_t(x)\le A(x)\quad\text{whenever }q_t(x)>B(x).
\tag{PG.2}
\]
The actual one-angle material removed is **exactly** a vertical interval of height \((q_t-B)_+\), with no upper clipping.

Set
\[
J_t=\{x\in I:q_t(x)>B(x)\}.
\]
The function \(q_t\) is concave because it is the minimum of two affine graphs, whereas \(-B\) is concave. Consequently \(q_t-B\) is concave, and \(J_t\) is a (possibly empty) interval.

Every extreme point of the actual K belongs to the compact S (a finite convex combination representing an extreme point must be trivial). Hence no lower-graph point \((x,B(x))\) in \(J_t\) can be extreme. At an interior projection coordinate, every non-extreme lower-graph point lies in the **relative interior of a straight exposed boundary segment**, so B is affine in a neighborhood of that x. A locally affine convex function on the connected interval \(J_t\) is affine throughout; indeed distinct slopes would require a transition point that is itself extreme, contrary to the strict cut. So
\[
B(x)=m_tx+c_t\qquad (x\in J_t).
\tag{PG.3}
\]

The end horizontal-extreme points and the endpoints of every exposed facet of K belong to S. Therefore they cannot lie **inside** the positive set \(J_t\); however, its **base zeros may coincide** with an outer projection endpoint or an exposed facet endpoint. By continuity of B (including one-sided continuity at endpoints, forced by compactness of K), the affine lower boundary extends to the two base-zero limits. The two linear pieces of \(q_t-B\) must form **a positive tent**, with the increasing second ray on the left and the decreasing first ray on the right; a single affine piece cannot be positive between two zero endpoints. No false positive distance from the base to a facet endpoint is required.

The tent's apex occurs where the physical two inner-wall rays meet, at their actual sharp corner
\[
C_t=(\xi_t,\eta_t)
=(h_K(u_t)-1)u_t+(h_K(v_t)-1)v_t.
\]
Writing \(h_t=\eta_t-(m_t\xi_t+c_t)>0\), the slopes must obey \(-\cot t<m_t<\tan t\), the two base abscissae are
\[
x_t^-=\xi_t-\frac{h_t}{\tan t-m_t},\qquad
x_t^+=\xi_t+\frac{h_t}{\cot t+m_t},
\]
and the **entire actual clipped cut is exactly the triangle**
\[
\boxed{
|K\cap Q_t|
=\frac{h_t^2}{2}
\left[\frac1{\tan t-m_t}+\frac1{\cot t+m_t}\right].
}
\tag{PG.4}
\]
Its base lies on **one actual exposed straight lower hull facet**, its sides lie on the **two attached physical inner-wall rays**, and its tip is \(C_t\). The upper-turn statement is the vertical reflection of the same argument.

The proof uses *no* curvature-density bound, connected angular superlevel assumption, fixed source contact chart or limit on the number of facets. Crucially it concerns one angle; **integrating PG.4 over angles would count overlapping material repeatedly** and is not a sharp area proof.

## 2. Exact adversarial oblique-facet instance — the horizontal-base formula is insufficient

Here is a genuinely feasible full-two-turn **nonconvex** sofa whose actual hull has an **active oblique lower facet**, so the slope denominators in PG.4 are indispensable.

Take the unit square \(K_0=[-1/2,1/2]\times[0,1]\), and let \(S_0=E_{\rm full}(K_0)\) be its entire canonical two-turn envelope. Its full lower inner-corner height is
\[
\eta_0(t)=\sin t\cos t+1-\sin t-\cos t
\le\frac32-\sqrt2<\frac12 .
\]
The max is attained at \(t=\pi/4\), and is bounded by that expression or zero on the entire quarter; its upper-turn sweep is the reflection above the midline. All x-fibers of \(S_0\) contain \(1/2\), so it is connected. At the four square corners one inner-wall directional depth is respectively \(\le\sin t\) or \(\le\cos t\) in either handed frame, hence all four corners survive. Thus \(K_0=\operatorname{conv}S_0\): this is not an auxiliary incompatible square.

Now make a single permitted inward halfplane cut:
\[
\boxed{
S=S_0\cap\{(x,y):y\ge\tfrac1{10}(x+\tfrac12)\}.
}\tag{PG.5}
\]
This is a **subset** of a genuine full-turn sofa, so it inherits both complete physical motions. Its midline survives over all \([-1/2,1/2]\) because the sloped cut lies below height \(1/10\), and every vertical fiber remains an interval. Hence S is compact connected.

The upper square vertices \((\pm1/2,1)\) and both sloped-base endpoints \((-1/2,0)\), \((1/2,1/10)\) survive the old complete turn constraints: at either extreme x, the lower niche roof is zero, as follows from the explicit two-wall roof or the unit-square support-depth tests. These four retained points span the trapezoid
\[
\boxed{
K=\operatorname{conv}S
=K_0\cap\{y\ge\tfrac1{10}(x+\tfrac12)\}.
}\tag{PG.6}
\]
Its **entire lower boundary is the genuine oblique supporting facet of slope \(m=1/10\)**. The two upper support values for positive-y normals are **unchanged** from the square because the original two upper square vertices remain. Thus at \(t=\pi/4\), its actual physical inner corner is
\[
C_t=(0,\tfrac32-\sqrt2).
\]
The gap above the oblique lower facet is
\[
h_t=\frac{29}{20}-\sqrt2>0,
\]
the last inequality following by exact squaring \((29/20)^2=841/400>2\). The whole one-angle region removed is the genuine **oblique triangle**
\[
\boxed{
|K\cap Q_{\pi/4}|=
\frac{100}{99}
\left(\frac{29}{20}-\sqrt2\right)^2>0.
}\tag{PG.7}
\]
The base abscissae lie strictly within \([-1/2,1/2]\), the corner roof is below the top roof one, and PG.4 gives the displayed area with \(m=1/10\). Applying the **horizontal** formula \(h_t^2/(2\sin t\cos t)\) would give \(h_t^2\), which is strictly **smaller** than the correct oblique area by factor \(100/99\).

This is an exact positive-area **actual-same-hull** diagnostic, not a floating sampled hallway or a candidate for greater-than-M area.

## 3. Global actual-feasible **polygonal hull value-density**, with no false feasibility-preserving smoothing

**Theorem PG1 (polyhedral value-density for full turns).** Let \(V_F\) be the supremum of ordinary areas of **all compact connected both-full-turn sofas** in the unit incoming strip. Let \(V_F^{\rm poly}\) be the supremum over those sofas whose **actual convex hull is a finite polygon**. Then
\[
\boxed{V_F=V_F^{\rm poly}.}\tag{PG.8}
\]
More strongly, for any compact connected full-turn S and every \(\varepsilon>0\) there is a compact connected full-turn sofa \(S_\varepsilon\), which is a finite union of closed axis-aligned rectangles and finitely many vertical joining segments, with **polygonal actual convex hull** and
\[
|S_\varepsilon|\ge |S|-\varepsilon.
\tag{PG.9}
\]
No assumption that the original hull K is polygonal, has bounded curvature, a finite ray-contact chart, aligned top/bottom faces, or an area-near-Romik contact pattern is used.

**Zero-area convention.** If the input sofa has area zero, the stated approximation inequality is trivial: choose a sufficiently small positive-area rectangle of Euclidean diameter less than one inside the incoming strip. It fits both complete turns by a single-wall width bound and has a polygonal actual hull. In the proof below assume the input area is positive, so the selected interior rectangles are nonempty for sufficiently fine partitions.

**Proof: Step A, saturate and obtain continuous interval roofs.** For the actual S let \(K=\operatorname{conv}S\). Canonical support tightening supplies the compact full envelope \(E=E_{\rm full}(K)\supseteq S\). By the downward/upward one-sided nature of the full turned quadrants and connected x-projection of S,
\[
E_x=[L(x),U(x)]\ne\varnothing
\qquad(x\in I_K=[l,r]).
\]
Over the projection interior, the lower and upper hull graphs are respectively continuous convex and continuous concave functions. The **complete positive all-angle ray roofs** are continuous in x: for angles \(t\) bounded away from 0 and \(\pi/2\), the minimum of the two affine wall heights is jointly continuous and the angular supremum is uniformly continuous; near the axis endpoints the *positive part* is bounded uniformly by \(C t\) or \(C(\pi/2-t)\), because \(h_K(e_y)\le1\) and the support function is Lipschitz in its normal. Taking the continuous angular maximum after extending the endpoint contributions by zero proves continuity of both full niche roofs. Therefore L and U are continuous on **every compact interior x-interval** and satisfy \(0\le L\le U\le1\). No differentiable active-angle parameter is chosen.

**Step B, approximate ordinary area by disjoint horizontal slabs of true retained material.** Fix \(0<\delta<(r-l)/4\). Discard the two projection tails of combined length \(2\delta\); their omitted sofa area is at most \(2\delta\). Uniformly partition \([l+\delta,r-\delta]\) into finitely many small closed cells \(J_i=[x_i,x_{i+1}]\). Put
\[
L_i=\sup_{x\in J_i}L(x),\qquad
U_i=\inf_{x\in J_i}U(x).
\]
If \(L_i<U_i\), retain the **entire closed rectangle** \(R_i=J_i\times[L_i,U_i]\subseteq E\); if \(L_i\ge U_i\), retain nothing on that cell. Let \(Q=\bigcup_iR_i\) and \(D=\operatorname{proj}_xQ\), a finite union of closed intervals. The rectangles have disjoint x-interiors, so their ordinary area is the sum of their areas.

Let \(\omega\) be a common modulus of continuity for L,U on the truncated projection. For any x in a cell of mesh \(\Delta\), the selected rectangle height (or zero) differs from the full E-fiber height \(U(x)-L(x)\) by at most \(2\omega(\Delta)\). Consequently
\[
|S|-|Q|
\le |E|-|Q|
\le2\delta+2(r-l)\omega(\Delta).
\tag{PG.10}
\]
Choose \(\delta\) and then \(\Delta\) to make the right side less than \(\varepsilon\). This approximates the **true entire swept-ray surviving area**, not a finite sampled-niche surrogate.

**Step C, compress only empty x-gaps, then connect by vertical fiber filling.** Write the finitely many occupied x-intervals of D in increasing order, and define the monotone 1-Lipschitz map
\[
T(x)=\int_l^x\mathbf1_D(s)ds .
\]
It maps each occupied interval to an equal-length translated interval, and collapses every gap; the images tile the whole interval \([0,|D|]\) up to shared endpoints. Thus \(\bar Q=\{(T(x),y):(x,y)\in Q\}\) is still a **finite union of rectangles**, and \(|\bar Q|=|Q|\) exactly.

The universal safe-support-depth contraction inequality [GC1](horizontal-gap-compression.md) follows directly by comparing each pair \(p,q\) under the map \((x,y)\mapsto(T(x),y)\):
\[
h_{\bar Q}(n)-F(p)\cdot n
\le\max\{h_Q(n)-p\cdot n,\ H_Q|n_y|\},
\qquad H_Q\le1.
\tag{PG.11}
\]
At every originally visited lower/upper hallway angle one of Q's two inner depths was \(\le1\), and its **corresponding transformed depth** remains \(\le1\). All outer support inequalities are automatic after retightening. The incoming/outgoing full-turn vertical unit strips also remain valid. Hence \(\bar Q\) is feasible for both continuously rotated canonical quarter-hallway families, even if it is disconnected.

Fill the vertical fiber at each x to the interval between its extrema. Since the rectangles occupy disjoint x-interiors, **all fibers were already intervals except possibly at the finitely many interface abscissae** between compressed intervals. Filling adds only finitely many **vertical line segments**, so changes ordinary area by zero. Each complete canonical lower hallway has interval vertical fibers (its inner wall alternatives are upward rays); the reflected upper hallway does too; therefore vertical filling stays inside every already support-tightened hallway, and the support function is unchanged because filling stays inside the convex hull. The resulting
\[
S_\varepsilon=\operatorname{vertical-fill}(\bar Q)
\]
is compact, has a horizontal projection equal to an interval and has interval fibers, hence is **connected**. It is fully two-turn feasible and
\[
|S_\varepsilon|=|Q|>|S|-\varepsilon.
\]
Its convex hull is the convex hull of finitely many rectangle corners and finitely many vertical-segment endpoints, therefore a **finite polygon**. This proves PG.8–PG.9. \(\square\)

**Critical quantifier distinction:** The proof does **not** say one may circumscribe an arbitrary feasible hull K by an arbitrary polygon and preserve its physical motions. Instead it takes *retained actual sofa material from inside its already feasible canonical envelope*, and compresses/joins it with a separately proved support-depth inequality. This is why the approximation is globally admissible.

## 4. Exact revised Gate 1 acceptance target on **finite genuine hull polygons**

For a finite polygonal actual hull \(K\) of a connected full-turn sofa S, the independently audited facet theorem of Section 1 applies to **every angle**, and the collection of its lower and upper facets is finite. Let \(\mathcal F_-(K)\), \(\mathcal F_+(K)\) be those finite collections, and let \(B_F\) be the affine lower graph on a lower facet F (with the reflected upper analogue). Put
\[
n_F(x)=\left[
\sup_{0<t<\pi/2}
\min\left(
\frac{h_K(u_t)-1-x\cos t}{\sin t},
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\right)-B_F(x)
\right]_+ .
\]
The **complete angular union** on F, *not the sum of the areas of separate angle cuts*, removes exactly \(\int_{I_F} n_F(x)\,dx\).

Consequently, **Gate 1 passes if and only if** the following **finite-facet sharp area charge** is proved for **every** finite polygon that is the actual hull of some compact connected complete-two-turn sofa:
\[
\boxed{
\sum_{F\in\mathcal F_-(K)}\int_{I_F}n_F(x)\,dx+
\sum_{F\in\mathcal F_+(K)}\int_{I_F}n_F^+(x)\,dx
\ \ge\ |K|-M.
}
\tag{PG.12 — STILL OPEN}
\]
Sufficiency: PG.12 implies that every such polygonal-hull sofa has area \(\le M\) by the exact disjoint ordinary niche subtraction, and PG1 passes the same value bound to all full-turn sofas. Necessity for a sharp value bound follows from the physical area identity on the canonical saturation of every admitted K. Romik's feasible construction supplies the matching lower value M, even though its own K need not be a polygon; PG1 approximates it arbitrarily closely by feasible polygonal-hull sofas.

**What we gained and what we did not.** The global proof now needs to handle **finitely many actual exposed facets at a time**, rather than a potentially singular continuous curvature boundary with countably many facets. There is **no uniform bound on the number of facets**, nor an upper bound on support curvature or complexity of their angular sweeps. The required **universal quantitative charge PG.12 is still missing**, even on finite polygons with opposite-end top/bottom faces. This is a substantive global-domain coverage reduction; it is not a new numerical upper bound, an area-improving symmetrization, a global shape classification, or a proof of optimality.

No CI, Lean/Lake formalization, external certification, or fabricated completion result is claimed.
