# A sharp nonlocal ray-envelope calibration for vertical moving-corner perturbations of Romik

**Date:** October 8, 2026. **Status:** A new *strict ordinary-area upper theorem* for an **infinite-dimensional family** of **genuine full-two-turn ambidextrous sofas**, including support perturbations whose curvature becomes **greater than one** and whose actual moving corner's positive-height superlevel sets **disconnect**. This uses a **frozen exposed-reference inner-wall ray calibration**, not a supposition that the perturbed cap retains Romik's contact chart.

This is a substantial improvement of the user's proposed **outer-wall supports + actual moving corner → fully swept inner niche** strategy, but **does not prove unrestricted optimality**. It is a comparison along an explicit subspace of support variations; arbitrary changes of the corner's horizontal position, global contact ordering, nonsymmetric two-handed variations, support switches, and partial terminal angles remain unbounded by this theorem. The original candidate remains the only asserted equality witness in this family.

Inputs: Romik's exact reference upper support [RH.2](romik-horizontal-misalignment-sharp-bound.md), its standard middle exposed-wall/corner chart as proved in [PJ-COUP1](spatial-half-partition-coupled-middle-variation.md), and the strict central-face niche containment margins used in [NR](near-reference-positive-minwidth-slack.md). All new comparisons below are explicitly derived, without assuming the new shape has small \(C^2\)-distance from the reference.

## 1. One scalar moves the sharp corner *vertically*, keeping its horizontal path **exactly fixed**

Let \(K_*=\operatorname{conv}\Sigma_*\) be the horizontally and vertically reflection-symmetric Romik reference hull in \(0\le y\le1\), with projection \([-m,m]\) and common top/bottom face interval
\[
J_*=[-m/2,m/2],\qquad
m=\frac1{3\sin\beta}>1,\quad
\beta=\arctan Y,\quad 4Y^3+3Y-1=0.
\]
Put \(L=\pi/2\), \(t_0=\pi/4\), \(T=(\beta,L-\beta)\), and denote the two original upper-quarter supports by
\[
f_*(t)=h_{K_*}(\cos t,\sin t),\qquad
g_*(t)=h_{K_*}(-\sin t,\cos t),\qquad 0\le t\le L.
\]
The reference moving inner corner is \(c_*(t)=(f_*(t)-1)u_t+(g_*(t)-1)v_t=(\xi_*(t),\eta_*(t))\).

For any real \(\varphi\in C_c^2(T)\) define **simultaneously**
\[
\boxed{
f_\varphi=f_*+\varphi(t)\sin t,\qquad
g_\varphi=g_*+\varphi(t)\cos t.
}\tag{VC.1}
\]
Extend to the lower support semicircle by the same vertical reflection about \(y=1/2\) as the reference. For a horizontally reflection-symmetric body, take \(\varphi(L-t)=\varphi(t)\); the main area comparison does not need that extra symmetry.

Because
\[
\sin t\,u_t+\cos t\,v_t=(0,1),
\]
the **entire physical corner path** transforms by the exact identity
\[
\boxed{
c_\varphi(t)=c_*(t)+(0,\varphi(t)),\qquad
\xi_\varphi(t)=\xi_*(t),\quad
\eta_\varphi(t)=\eta_*(t)+\varphi(t).
}\tag{VC.2}
\]
The horizontal movement of *every* sharp inner corner in that handed quarter is **unchanged**, for arbitrarily oscillatory \(\varphi\). Both inner-wall rays at parameter \(t\) are translated **vertically by the same amount**:
\[
\boxed{w_{\varphi,t}(x)=w_{*,t}(x)+\varphi(t)}
\tag{VC.3}
\]
for every abscissa \(x\), not just at exposed corner contacts.

For the remaining arguments assume:
- \(\varphi\le0\), not identically zero, and supported on a fixed small symmetric compact interval \(J_0\Subset T\) around \(t_0\);
- its supremum norm and first-derivative norm are sufficiently small to preserve the four original corners of the central rectangle \(J_*\times[0,1]\) and the horizontal extreme midline points \((\pm m,1/2)\);
- the extension of VC.1 is the actual support of a compact convex hull \(K_\varphi\).

The second condition is a **strict finite-point support-slack test**: the reference support on the angular window \(J_0\) exceeds the scalar product with each of the six named retained reference points by a positive amount. At \(t_0\) these gaps include
\[
\boxed{
f_*(t_0)-(m,1/2)\cdot u_{t_0}
=\frac{R-m}{\sqrt2}>0,\qquad
f_*(t_0)-(m/2,1)\cdot u_{t_0}
=\frac{R-m/2-1/2}{\sqrt2}>0,
}\tag{VC.4}
\]
where \(R=\cos\beta/\sin(3\beta/2+\pi/8)\) and the strict positivity follows from the existing exact reference bounds \(R>1.28\), \(m<1.17\). Analogous inequalities for \(g_*\) and the other reference rectangle vertices follow by both reflections; after shrinking \(J_0\) they hold uniformly. Since the original reference hull contains these points and all nonchanged supports are unchanged, sufficiently small \(\|\varphi\|_\infty\) retains them in \(K_\varphi\).

## 2. The *complete* niche is still inside the common face and below the midline

Because \(\varphi\le0\), all upper support directions of \(K_\varphi\) are weakly lower than their reference values. Thus \(K_\varphi\subseteq K_*\).

At each affected lower-turn angle, VC.3 says that the **whole forbidden quadrant**, including both attached rays, is exactly the old quadrant translated downward by the nonpositive amount \(\varphi(t)\). Since that quadrant is downward closed,
\[
\boxed{W_-(K_\varphi)\subseteq W_-(K_*).}\tag{VC.5}
\]
At other angles the forbidden quadrants are unchanged. Vertically reflecting the support functions gives the corresponding upper-handed inclusion \(W_+(K_\varphi)\subseteq W_+(K_*)\).

The exact reference full-turn positive-height sweeps are disjoint and confined to
\[
\operatorname{int}J_*\times[0,1/2),
\qquad
\operatorname{int}J_*\times(1/2,1].
\]
By VC.5 the perturbed sweeps are also confined there and hence **neither can touch the central horizontal midline**. The assumed six retained reference points force the full rectangle \(J_*\times[0,1]\) and the entire midline \([-m,m]\times\{1/2\}\) into \(K_\varphi\).

The canonical envelope \(S_\varphi=E_{\rm full}(K_\varphi)\) consequently has a nonempty interval fiber over every \(x\in[-m,m]\), meeting the same horizontal midline. It is compact, connected and completes **both entire conventional \(90^\circ\) turns**, with canonical continuous corner motions. It has **exactly** the hull \(K_\varphi\): all outer-hull extreme points at abscissae outside \(\operatorname{int}J_*\) are untouched by the confined sweeps, while any point with \(x\in\operatorname{int}J_*\) is in the full rectangle and cannot be an extreme point. The four face endpoints at \(x=\pm m/2,y=0,1\) survive as in the original reference. Thus all extreme points survive and \(\operatorname{conv}S_\varphi=K_\varphi\).

Let \(n_\varphi(x)\) and \(n_*(x)\) be the entire actual **positive** lower niche roofs on \(J_*\). Since VC.3 translates each one-angle roof by \(\varphi(t)\), the full supremum gives a rigorous uniform bound
\[
\boxed{n_*(x)-\|\varphi\|_\infty
\le n_\varphi(x)\le n_*(x),\qquad x\in J_* .}\tag{VC.6}
\]
By vertical symmetry the upper niche removes the reflected same area; there is **no omitted ordinary clipping term**:
\[
\boxed{|S_\varphi|=|K_\varphi|-2N_\varphi,\quad
N_\varphi=\int_{J_*}n_\varphi(x)\,dx.}\tag{VC.7}
\]

## 3. A *frozen reference wall* gives an area lower bound on **the perturbed entire niche**

Let \(t_*(x)\) be an old *exposed* maximizing corner or single-wall parameter for the reference niche at abscissa \(x\in\operatorname{int}J_*\). The explicit reference contact chart supplies this measurable parameter except at finitely many switching abscissae (an area-zero set); no assertion is made that the **new** roof has the same maximizer.

By VC.3, the perturbed niche still contains the complete old ray height at that old parameter, now translated by \(\varphi(t_*(x))\). Therefore at every such \(x\),
\[
\boxed{
n_\varphi(x)\ge n_*(x)+\varphi(t_*(x)).
}\tag{VC.8}
\]
This inequality remains valid even if **new wall envelopes switch, fold, create different corner arcs, or have curvature density above one**: it follows by retaining just a single valid old maximizer in the new **supremum**.

The reference exposed graph decomposes into the smooth first-wall tangencies \(B\), second-wall tangencies \(D\), and one moving corner graph \(c_*\). On the middle reference angular interval, its horizontal Jacobians are
\[
\begin{aligned}
x_B'&=(\rho_f-1)\sin t,\\
x_D'&=(1-\rho_g)\cos t,\\
x_c'&=p\cos t-q\sin t,\qquad
p=f_*'-g_*+1,\quad q=g_*'+f_*-1.
\end{aligned}
\]
The first/second smooth branches and reversed corner branch occupy **disjoint** x-intervals, each with its own old maximizing parameter. Hence integrating VC.8 with the *true spatial Jacobians* over the affected source interval \(J_0\) gives
\[
\begin{aligned}
N_\varphi-N_* &\ge
\int_{J_0}\varphi(t)
\Big[(1-\rho_f)\sin t+(1-\rho_g)\cos t
        -p\cos t+q\sin t\Big]\,dt.
\end{aligned}\tag{VC.9}
\]
The explicit Romik middle phase satisfies
\[
\boxed{q=2\rho_f-1,\qquad p=1-2\rho_g.}
\tag{VC.10}
\]
This reduces the bracket in VC.9 **exactly** to \(\rho_f\sin t+\rho_g\cos t\):
\[
\boxed{
N_\varphi-N_*
\ge\int_{J_0}
(\rho_f\sin t+\rho_g\cos t)\varphi(t)\,dt.
}\tag{VC.11}
\]
**This is the key nonlocal calibration**. It includes **both stationary attached-ray fronts and the corner front**, and it is a true lower bound on the **entire new ordinary niche area**. Crucially, it uses no contact-topology or curvature premise on the *new* envelope, beyond the convexity/feasibility already verified in Section 2.

## 4. The exact outer-area variation closes the comparison

The planar support-area identity for convex bodies, applied to the vertically reflected halves, gives exactly, with no Taylor remainder,
\[
\begin{aligned}
|K_\varphi|-|K_*|
&=2\int_{J_0}[\rho_f\varphi\sin t+\rho_g\varphi\cos t]\,dt\\
&\quad+\int_{J_0}\Big[
(\varphi\sin t)^2+(\varphi\cos t)^2
-((\varphi\sin t)')^2-((\varphi\cos t)')^2
\Big]dt.
\end{aligned}\tag{VC.12}
\]
The homogeneous quadratic difference collapses because
\[
(\varphi\sin t)^2+(\varphi\cos t)^2=\varphi^2,\qquad
((\varphi\sin t)')^2+((\varphi\cos t)')^2
=\varphi'^2+\varphi^2.
\]
Therefore
\[
\boxed{
|K_\varphi|-|K_*|
=2\int_{J_0}(\rho_f\sin t+\rho_g\cos t)\varphi\,dt
-\int_{J_0}\varphi'^2\,dt.
}\tag{VC.13}
\]

Now use VC.7 for both envelopes, VC.11 for the **actual** perturbed niche area, and \(|\Sigma_*|=M\). The linear terms cancel **exactly**:
\[
\boxed{
\begin{aligned}
|S_\varphi|-M
&=(|K_\varphi|-|K_*|)-2(N_\varphi-N_*)\\
&\le-\int_{J_0}\varphi'(t)^2dt.
\end{aligned}}\tag{VC.14}
\]
This comparison is **strict** for every nonzero compactly supported \(\varphi\), even if its curvature changes by order one and its actual swept-ray contact chart is wholly different.

**Theorem VC1 (exact ordinary-area coercivity with arbitrary new contact topology).** For every nonzero \(C_c^2(J_0)\) downward nonpositive *vertical-corner displacement* \(\varphi\) for which VC.1 is the support of a convex hull and the finitely checked core geometry of Section 2 is retained,
\[
\boxed{
|E_{\rm full}(K_\varphi)|
\le M-\|\varphi'\|_{L^2(J_0)}^2<M.
}
\]
The body on the left is a **genuine connected, both-full-turn, saturated sofa with its actual convex hull**. No small-\(C^2\) or curvature-\(\le1\) hypothesis is imported from a perturbative Romik chart.

This compares outer-wall area growth to the **complete moving-corner plus inner-ray sweep** on an infinite-dimensional slice of the unrestricted geometric problem. It is not the global upper bound for arbitrary caps/supports: VC.1 imposes a nontrivial relation between the two upper source quarters, and its reference-based calibration depends on exposed Romik contacts.

## 5. A concrete **nonunimodal near-Romik family** which the calibration controls

We now show that the new area theorem is not restricted to the previous low-curvature stable chart. It applies to actual hulls whose physical moving corner's height has **two separated local peaks**, arbitrarily close in area to \(M\).

Choose a small **symmetric** closed interval \(J_0=[t_0-\delta,t_0+\delta]\Subset T\) on which
\[
\rho_f,\rho_g>67/100,\qquad
\max(\sin t,\cos t)<18/25
\tag{VC.15}
\]
and every outer supporting contact point for these normals lies strictly **outside** the core-face interval \([-m/2,m/2]\), as established by the reference support formula at \(t_0\):
\[
x_{O_f}(t_0)=3R/4>m/2,\qquad
x_{O_g}(t_0)=-3R/4<-m/2.
\]
Such a \(J_0\) exists by continuity and the RH bounds \(R>1.28\), \(m<1.17\). Take a \(C^\infty\), nonnegative, even cutoff \(\chi\) supported in \(J_0\), equal to one on a smaller central interval around \(t_0\).

For \(0<\epsilon\ll1\) define the actual **downward** moving-corner displacement
\[
\boxed{
\varphi_\epsilon(t)
=-\epsilon^2\chi(t)
\exp\!\left(-\frac{(t-t_0)^2}{\epsilon^2}\right).
}\tag{VC.16}
\]
It is even around \(t_0\), nonzero, compactly supported, and
\(\|\varphi_\epsilon\|_\infty\le\epsilon^2\),
\(\|\varphi_\epsilon'\|_\infty=O(\epsilon)\). It preserves both horizontal and vertical reflection symmetries of the actual outer hull, the unit incoming vertical span, the whole core rectangle and actual hull retention for small \(\epsilon\).

### 5a. **Convexity despite a nonvanishing positive curvature spike**

The exact curvature perturbations of the *first* and *second* quarter supports are
\[
\boxed{\begin{aligned}
(f_{\varphi_\epsilon}''+f_{\varphi_\epsilon})-\rho_f
&=\varphi_\epsilon''\sin t+2\varphi_\epsilon'\cos t,\\
(g_{\varphi_\epsilon}''+g_{\varphi_\epsilon})-\rho_g
&=\varphi_\epsilon''\cos t-2\varphi_\epsilon'\sin t.
\end{aligned}}\tag{VC.17}
\]
On the Gaussian core \(\chi=1\), with \(z=(t-t_0)/\epsilon\),
\[
\varphi_\epsilon'=2\epsilon z e^{-z^2},\qquad
\varphi_\epsilon''=2(1-2z^2)e^{-z^2}.
\]
The latter has global minimum \(-4e^{-3/2}>-9/10\), as follows from the elementary rational Taylor bound \(e^{3/2}>40/9\). Its first derivative satisfies \(|\varphi_\epsilon'|\le\epsilon\). On the cutoff transition region, which lies a fixed positive distance from \(t_0\), all Gaussian factors and their cutoff derivatives are superpolynomially small; hence **uniformly on \(J_0\)**
\[
\varphi_\epsilon''\ge-9/10-o(1),\qquad
|\varphi_\epsilon'|\le\epsilon+o(\epsilon).
\]
Thus from VC.15,
\[
\rho_{f,\epsilon},\rho_{g,\epsilon}
>\frac{67}{100}-\frac{18}{25}\left(\frac9{10}+o(1)\right)
-\frac{36}{25}\left(\epsilon+o(\epsilon)\right)>0
\]
for all sufficiently small \(\epsilon\), since \(67/100-162/250=11/500>0\). Outside \(J_0\) the support curvature is the original nonnegative reference curvature. There are no new junction atoms because \(\varphi_\epsilon\) is smooth and vanishes near the source interval endpoints. Therefore the full reflected function is a genuine compact **convex support** for a hull \(K_{\epsilon}\) in the same unit strip.

At the center, however, \(\varphi_\epsilon''(t_0)=2\), so both first/second quarter curvature densities exceed the unit hallway width on a small angular interval. This is a legal high-curvature sofa hull, **not** a curvature-\(\le1\) reference-chart perturbation.

### 5b. The same horizontal corner path acquires two height peaks

The exact reference inner-corner height on the middle phase is
\[
\eta_*(t)=R\sin(3t/2+\pi/8)+\frac12-\sin t-\cos t.
\]
At \(t=t_0=\pi/4\),
\[
\eta_*'(t_0)=0,\qquad
\eta_*''(t_0)=\sqrt2-\frac94R.
\]
By VC.2 and \(\varphi_\epsilon''(t_0)=2\),
\[
\boxed{
\eta_\epsilon'(t_0)=0,\qquad
\eta_\epsilon''(t_0)=2+\sqrt2-\frac94R>0,
}\tag{VC.18}
\]
where the last strict inequality follows just from
\(R<131/100\) and \(\sqrt2>7/5\):
\(2+7/5-9(131/100)/4>0\).

Thus the original **strict maximum** of the moving corner height at \(45^\circ\) becomes a strict **local minimum**, with strictly higher values immediately on both sides. Since
\(\eta_\epsilon(t_0)=H_*-\epsilon^2>0\) for small \(\epsilon\), choose a positive threshold between the new central minimum and the two adjacent higher values. The angular superlevel set
\[
\boxed{\{t\in(0,\pi/2):\eta_\epsilon(t)>y_\epsilon\}}
\tag{VC.19}
\]
has **at least two disconnected components**. Yet by VC.2 the entire **horizontal corner trajectory \(\xi_\epsilon(t)=\xi_*(t)\) is identical to Romik's**.

### 5c. The full actual sofa has area strictly below and tending to \(M\)

Apply VC1 directly to this family:
\[
\boxed{
|E_{\rm full}(K_\epsilon)|
\le M-\int_{J_0}\varphi_\epsilon'^2dt<M.
}\tag{VC.20}
\]
There is no use of a falsely stable new contact chart: the inequality holds by the full old-ray comparison VC.8. In fact, on the Gaussian core,
\[
\int_{J_0}\varphi_\epsilon'^2dt
=\bigl(\sqrt{\pi/2}+o(1)\bigr)\epsilon^3>0.
\tag{VC.21}
\]
The coefficient follows by \(z=(t-t_0)/\epsilon\) and
\(\int_{\mathbb R}4z^2e^{-2z^2}dz=\sqrt{\pi/2}\); cutoff effects vanish exponentially.

Finally \(h_{K_\epsilon}\to h_{K_*}\) uniformly at rate \(O(\epsilon^2)\), so convex hull areas converge, and the complete niche roof comparison VC.6 gives a uniform \(O(\epsilon^2)\) difference in the entire **actual** ordinary niche per hand. Therefore
\[
\boxed{|E_{\rm full}(K_\epsilon)|\longrightarrow M
\quad(\epsilon\downarrow0).}\tag{VC.22}
\]

**Theorem VC2 (near-\(M\), exact-unit-span, two-full-turn nonunimodal corner paths).** There exist compact connected, **canonically saturated**, **both-reflection-symmetric** ambidextrous sofas \(S_\epsilon\), each with its **actual convex hull**, incoming vertical span **exactly one**, and both entire conventional quarter turns, such that
\[
\boxed{
|S_\epsilon|<M,\qquad
|S_\epsilon|\to M,\qquad
\{\text{angles where the genuine lower corner height}>y_\epsilon\}
\text{ is disconnected at some }y_\epsilon>0.
}
\]
Their physical lower-corner **horizontal** path agrees *pointwise* with Romik's, while their corner-height profile has a strict local minimum at the old reference maximum.

This disproves **any high-but-subcritical-area threshold**, even together with vertical and horizontal symmetry, unit-height span, actual hull retention, full-turn feasibility and canonical saturation, as a justification for replacing the actual complete moving-corner ray sweep by a **single angular peak/front**. It does not rule out a one-peak theorem specifically for a hypothetical **global maximizer or area \(>M\)**; it is a sharp near-reference negative control, not an unrestricted sharp-value theorem.

## 6. What changes in the global optimality proof

VC1 is stronger than a local second-variation calculation: it is a true **ordinary-area** comparison for a whole infinite-dimensional vertical-corner perturbation class, including O(1) **curvature spikes** and radical changes of the new niche's active contacts. The proof succeeds by **calibrating the complete new swept rays from fixed reference rays** (VC.8–VC.11), while the exact quadratic outer-area penalty \(\|\varphi'\|_2^2\) pays for any deviation. This is directly aligned with the user's outer-wall-plus-moving-corner-first approach and avoids the old pairwise clipping-deficit inequality.

But the proposed global theorem still lacks a comparison for arbitrary pairs of independent corner paths, especially **horizontal corner displacements**, moved support endpoints/top faces, separated opposite face arrangements, and actual partial terminal angles. A complete proof must construct a calibration that remains valid without Romik's *fixed reference exposed wall chart* as an anchor. VC1–VC2 alone neither yield \(|S|\le M\) unrestricted nor characterize all equality bodies.

No CI, Lean/Lake compilation or independent referee check is claimed. The new results are written proofs, subject to independent mathematical review.
