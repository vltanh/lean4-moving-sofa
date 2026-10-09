# Gate 1: every genuine one-angle inner-wall cut is a single triangle on one exposed hull facet

**Date:** October 9, 2026. **Status:** A universal *exact ordinary-area* structural reduction for **all actual connected full-conventional-two-turn sofas**, including asymmetric, nonsmooth, nonconvex bodies, arbitrary curvature measures, arbitrary moving-corner contact switches and disconnected angular activity sets. It is not a result only near Romik. It begins with the **outer convex hull**, its **physical moving sharp corner**, and both attached inner rays; no single-peak or prescribed contact chart is assumed.

**Main theorem (FT1):** If a compact connected body \(S\) admits both complete conventional full turns and \(K=\operatorname{conv} S\), then **each individual lower inner-wall forbidden quadrant**, intersected with \(K\), is either empty or **one genuine Euclidean triangle** whose base is contained in **one exposed straight lower face of the actual hull**, and whose apex is precisely the physical moving inner corner determined by both outer supports. The upper handed forbidden quadrant gives the vertically reflected statement with one exposed **upper** face. There are no individual cuts curved by the outer flank, clipped by an opposite outer wall, or split over distinct lower faces. The *unions* over angles can of course be highly nonconvex, have multi-peak corner heights and overlap across angular parameters.

This is an indispensable **global reduction of the direct Gate 1 loss geometry**, not a sharp inequality. The required estimate \(|K|-|E_{\rm full}(K)|\ge|K|-M\), equivalently \(|E_{\rm full}(K)|\le M\) for all feasible \(K\), remains **UNPROVED**. The theorem does not apply to an **arbitrary auxiliary hull** whose canonical envelope has empty horizontal fibers or fails to retain extreme points: the actual-hull premise is essential. By [Gate 0](original-motion-global-bridge-gate0-audit.md), it is nevertheless legitimate to optimize full-turn *values* over actual compact connected feasible hulls and then use [GC4](horizontal-gap-compression.md) to restore arbitrary auxiliary signed estimates, once a sharp actual-hull theorem is found.

## 1. Hypotheses and the physical one-angle tent

Normalize the common incoming strip to \(0\le y\le1\). Let \(S\) be a nonempty compact connected sofa with both *full* conventional quarter-turn motion families and actual outer hull \(K=\operatorname{conv}S\). Put
\[
I=[l,r]=\operatorname{proj}_xK,\quad
B(x)=\min\{y:(x,y)\in K\},\quad
A(x)=\max\{y:(x,y)\in K\}.
\]
On the interior of I, \(B\) is a convex function and \(A\) a concave function. The continuous canonical turning family exists by support tightening, independently of its originally chosen translations.

At a lower proper angle \(t\in(0,L)\), \(L=\pi/2\), put
\[
u_t=(\cos t,\sin t),\quad
v_t=(-\sin t,\cos t),\quad
f_t=h_K(u_t),\quad g_t=h_K(v_t).
\]
The actual physical sharp moving inner corner and both attached-ray roofs are
\[
\boxed{\begin{aligned}
C_t=(\xi_t,\eta_t)&=(f_t-1)u_t+(g_t-1)v_t,\\
R_t(x)&=\frac{f_t-1-x\cos t}{\sin t},\\
D_t(x)&=\frac{g_t-1+x\sin t}{\cos t},\\
q_t(x)&=\min\{R_t(x),D_t(x)\}.
\end{aligned}}\tag{FT.1}
\]
The individual open forbidden quadrant is \(Q_t=\{(x,y):y<q_t(x)\}\). Its first/second walls meet exactly at \((\xi_t,\eta_t)\). Define
\[
H_t(x)=q_t(x)-B(x),\qquad
J_t=\{x\in I:H_t(x)>0\}.
\tag{FT.2}
\]
The function \(q_t\), being the pointwise minimum of two affine functions, is concave. Hence \(H_t=q_t-B\) is also **concave** on I, without any upper curvature bound or differentiability assumption. Its strictly positive set \(J_t\) is an interval, possibly empty.

## 2. Extreme-point retention forces a **single straight supporting face**

**Lemma FT1 (facet localization, each angle).** If \(J_t\ne\varnothing\), then \(B\) is affine on the *entire interval* \(J_t\), with a single constant slope.

**Proof.** First, every extreme point \(p\in\operatorname{ext}(K)\) belongs to the original compact S. This is elementary: if p were a convex combination of finitely many S-points, extremality forces all of them equal to p. Compact planar convex hulls are true convex combinations, not merely closure limits.

At any x in \(J_t\), the lower hull point \(P_x=(x,B(x))\) lies in the **open** forbidden quadrant \(Q_t\), since \(B(x)<q_t(x)\). Consequently \(P_x\notin S\), so it **cannot be an extreme point of K**.

For an interior x of a convex body's horizontal projection, a lower boundary point is nonextreme **if and only if** it lies in the relative interior of a nontrivial nonvertical straight boundary segment. Indeed a nonextreme boundary point lies in the interior of a line segment between two K-points; any such segment must belong to the supporting face at that boundary point, and the two endpoints have distinct x-coordinates when x is interior. Thus B is affine in an open neighborhood of x.

Every x in \(J_t\) therefore admits an open neighborhood on which B is affine. Because \(J_t\) is connected, these locally affine pieces glue with the same slope throughout: \(B(x)=m_tx+c_t\) on \(J_t\). (Otherwise the first point of slope change would be an extreme hull point forbidden by the same Q_t.) \(\square\)

The extreme horizontal endpoints x=l,r also belong to S, so \(H_t(l)\le0,\ H_t(r)\le0\). Continuity inside the projection ensures that any nonempty \(J_t\) is strictly inside I, and Lemma FT1 extends its affine graph to the two zero endpoints by limits. Denote their common maximal exposed lower hull face by \(F_t\).

**Important logical point:** The proof invokes both **actual feasible hull retention** and **one-angle downward closure**. It is **false** for an arbitrary convex auxiliary hull whose canonical saturation deletes an exposed extreme point. Gate 1 allows the actual-hull reduction only because Gate 0 proved equality of the relevant area suprema after connectedification. No convexity of the nonconvex sofa itself is assumed.

## 3. Exact oblique-triangle formula; both attached rays are necessary

**Theorem FT2 (one-angle triangle).** If \(Q_t\cap K\) has positive area, then its ordinary-area closure is exactly one triangle, whose base lies on \(F_t\), whose apex is \(C_t\), and whose two sloped sides are pieces of the **two physical inner-wall rays**. Write the lower supporting face as
\[
B(x)=m x+c_0\quad (x\in J_t).
\]
Then necessarily
\[
\boxed{-\cot t<m<\tan t,\qquad \xi_t\in J_t,\qquad
h_t:=\eta_t-(m\xi_t+c_0)>0.}\tag{FT.3}
\]
The two base endpoints and the **exact ordinary area removed at this angle** are
\[
\boxed{\begin{aligned}
x_t^-&=\xi_t-\frac{h_t}{\tan t-m},\\
x_t^+&=\xi_t+\frac{h_t}{\cot t+m},\\
|K\cap Q_t|&=\frac{h_t^2}{2}\left(
\frac1{\tan t-m}+\frac1{\cot t+m}\right).
\end{aligned}}\tag{FT.4}
\]
Both base endpoints belong to the same actual exposed lower face \(F_t\).

**Proof.** The two affine roof differences on that facet are
\[
R_t(x)-B(x)=r_0-(\cot t+m)x,\qquad
D_t(x)-B(x)=d_0+(\tan t-m)x.
\]
Their minimum is \(H_t(x)\), strictly positive on one interval with both boundary endpoints at height zero. Since the actual extreme endpoints of every face belong to S and avoid Q_t, this positivity interval cannot reach an exposed face endpoint. Both affine functions therefore must slope toward a strict common interior maximum: the first is decreasing and the second increasing. That is precisely \(-\cot t<m<\tan t\). The two lines cross at the **actual sharp corner abscissa** \(\xi_t\), where their height above the supporting face is \(h_t>0\), so the interval's endpoints are the displayed zero crossings.

One further point is indispensable: the triangle might, for an *arbitrary* K, be cut off by an upper convex boundary. It is **not** truncated for our actual feasible hull. Because S is connected and has horizontal projection I, the complete canonical envelope E(K) contains S and has a **nonempty interval fiber at every x in I**. Its lower endpoint is at least \(\max(B(x),q_t(x))\); its upper endpoint is at most \(A(x)\). Therefore \(q_t(x)\le A(x)\) whenever \(x\in J_t\). The entire vertical interval \([B(x),q_t(x))\) is consequently inside K, at every x of the positive interval. No roof clipping is lost. This interval has the triangular linearly varying height in FT.3, so its area is exactly the formula in FT.4. \(\square\)

For a horizontal facet \(m=0\), the formula reduces to the familiar physical inner-corner triangle
\[
\boxed{|K\cap Q_t|=\frac{h_t^2}{2\sin t\cos t}.}\tag{FT.5}
\]
The oblique form is essential for unit-height full-turn bodies with **opposite-end horizontal faces**: their long actual carved-support faces may be *sloped*, even if the horizontal top and bottom faces shrink to arbitrarily short intervals.

### Exact rational independent check

For \(K=[0,1]^2\) (an actual full-two-turn outer hull after its connected canonical saturation), choose \((\cos t,\sin t)=(4/5,3/5)\). The supports are \(f=7/5,g=4/5\); hence \(C_t=(11/25,2/25)\), the bottom face has \(m=0\), and its two baseline intercepts are \(1/3\) and \(1/2\). The area formula yields
\[
\frac{(2/25)^2}{2}\left(\frac43+\frac34\right)=\boxed{\frac1{150}}.
\]
The fractions and positivity have been recomputed independently by exact arithmetic; no angular sampling supplies the theorem.

## 4. An exact **full continuum** face-sweep decomposition for BOTH hands

Let \(\mathcal F_-\) be the at most countable collection of maximal straight **lower hull faces** whose projections have positive length; similarly \(\mathcal F_+\) for the upper graph. Countability follows because the projections' interiors are pairwise disjoint and each contains a distinct rational. Vertical hull faces lie on projection endpoint lines and have zero planar area.

For every lower facet \(F\in\mathcal F_-\), let \(I_F\) be its horizontal projection, \(B_F(x)=m_Fx+c_F\), and form
\[
\boxed{
n_{F,-}(x)
=\left[\sup_{0<t<L}\bigl(q_t(x)-B_F(x)\bigr)\right]_+,
\quad x\in I_F .
}\tag{FT.6}
\]
Only angles with triangle bases on this facet contribute positive values; every such individual contribution has FT.4's exact physical triangular shape. Their **union**, *not the sum of their individual areas*, has ordinary area
\[
\boxed{\mathcal N_-(K)
=\sum_{F\in\mathcal F_-}\int_{I_F}n_{F,-}(x)\,dx.}\tag{FT.7}
\]
The sum is absolutely convergent because all terms are nonnegative and bounded by the finite hull area. Outside the union of the lower-face projections, the true lower niche lies at or below the actual lower hull boundary and removes no material.

For the upper turn apply the **same construction to \(\rho K\)**, where \(\rho(x,y)=(x,1-y)\), and write the resulting physical upper niche loss \(\mathcal N_+(K)\). Because S is connected and its canonical envelope includes an interval fiber at every x, the two opposite-handed cut regions are **disjoint** within K, including if their closures touch at pinches. Consequently the exact **ordinary-area** identity becomes
\[
\boxed{
\begin{aligned}
|E_{\rm full}(K)|
&=|K|-\mathcal N_-(K)-\mathcal N_+(K)\\
&=|K|-
\sum_{F\in\mathcal F_-}\int_{I_F}n_{F,-}(x)\,dx
-\sum_{F\in\mathcal F_+}\int_{I_F}n_{F,+}(x)\,dx.
\end{aligned}}\tag{FT.8}
\]
The entire moving-wall geometry is represented by **one-angle physical triangles glued into complete ordinary angular unions on exposed hull facets**, with exact clipping and no assumption of face alignment, reflection symmetry, a curvature cap, a stable exposed-contact ordering or a single connected superlevel set of corner heights.

This is a genuine global reduction of **where** niches can remove material. It does not turn an infinite union into a finite sum, and it does not assign a universal cost to the union. A proposed proof that simply sums FT.4 over t would **double-count** overlapping triangles; a global measure transport or global support-charge comparison is still needed.

## 5. Why this matters specifically for the unresolved full-turn proof

- **Romik:** both full handed niches lie over straight horizontal exposed top/bottom faces; FT.4 recovers the exact individual moving-corner tents before the full sweep is integrated.
- **Opposite-end-face value-dense configurations:** shrinking horizontal face segments do **not** eliminate the loss. Facets of nonzero *oblique* slope may carry the same physical niche mass. The theorem works on those facets and therefore does **not** falsely conclude that all positive carving vanishes when the horizontal top/bottom faces become small.
- **Curved outer flanks:** their **extreme boundary points** must survive, so a forbidden triangle cannot be based on a curved flank. Those flanks still determine \(f_t,g_t\) and hence the moving corner and how much of each exposed facet is carved. This is precisely the user's requested **outer-wall → physical inner-corner → full ray niche** chain.
- **Arbitrary auxiliary hulls:** FT1–FT8 are not asserted for them. The [Gate 0 value equivalence](original-motion-global-bridge-gate0-audit.md) allows the *global optimum's value* to be tested on actual admitted hulls without requiring that each auxiliary K itself retain all its extreme points.
- **Partial turns:** the same one-angle facet theorem applies to *actually visited* conventional angles and actual common-hull S, but extending the complete-turn sharp area bound and terminal strip cost remains Gate 2.

**Gate 1 remains ACTIVE and UNPASSED.** The missing statement is the *quantitative sharp global charge*
\[
\boxed{\mathcal N_-(K)+\mathcal N_+(K)\ge |K|-M}
\tag{FT.9, **OPEN**}
\]
for every actual connected fullturn sofa hull K (and, by Gate 0, for the global fullturn optimum). FT.8 reduces the left side to unions of explicit facet-based physical triangles, **but does not prove FT.9**. This is not reported as a new unrestricted upper bound or a completed optimality proof.

No Lean, CI, external proof, or numerical optimization certificate is claimed. This note is a self-reviewed geometric proof requiring independent mathematical assessment.
