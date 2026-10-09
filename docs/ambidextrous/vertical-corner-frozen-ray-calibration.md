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

## 6. Stronger: **independent two-source support perturbations**, only \(C^1\)-small, with unrestricted new curvature

The vertical-corner direction VC.1 is not the full scope of the frozen-ray method. Here is a stronger result which permits **independent changes of the two upper source quarters**—and therefore both horizontal and vertical displacements of the moving inner corner—while retaining a strict **actual ordinary-area** inequality. In contrast to the older [PJ-COUP1](spatial-half-partition-coupled-middle-variation.md), the **new** support need *not* be \(C^2\)-close to Romik, have curvature density bounded by one, or retain Romik's stationary-wall exposure pattern.

Fix any sufficiently small compact middle interval \(J_0=[a,b]\Subset T=(\beta,L-\beta)\), containing \(t_0=\pi/4\), on which all three original reference pieces (first-wall stationary, second-wall stationary, and standard moving corner) are **strictly exposed**, with
\[
p_*<0<q_*,\quad0<\rho_{f,*},\rho_{g,*}<1,\quad
x_{c,*}'<0
\]
uniformly. The old exposed x-images of the three branch families are pairwise disjoint, and the unmodified reference exposes the rest of its niche outside these images.

For arbitrary
\(\phi,\psi\in C_c^2(\operatorname{int}J_0)\), independently replace
\[
\boxed{f=f_*+\phi,\qquad g=g_*+\psi,}\tag{VC.23}
\]
and extend to the lower support semicircle by reflection about \(y=1/2\). Assume only that the resulting full support is convex and
\[
\|\phi\|_{C^1}+\|\psi\|_{C^1}<\varepsilon_0
\tag{VC.24}
\]
for a sufficiently small **fixed** positive constant depending on \(J_0\) and the strict reference outer/niche margins. There is **no condition** on \(\|\phi''\|_\infty,\|\psi''\|_\infty\) except convexity of the resulting hull. The perturbations may have **either sign** and need not preserve left-right reflection symmetry.

The finite strict reference margins and the \(C^1\) bound guarantee that the new outer hull \(K_{\phi,\psi}\) retains the core rectangle and horizontal extreme midline points, while the positive swept niches remain strictly inside its central face window, separated above/below \(y=1/2\). Its canonical full-turn envelope is again a genuine compact connected ambidextrous sofa with **actual hull** \(K_{\phi,\psi}\), by the same interval-fiber and extreme-point arguments as in Section 2. In particular
\[
|E(K_{\phi,\psi})|=|K_{\phi,\psi}|-2N_{\phi,\psi}.
\]

### 6a. The new corner still supplies a valid roof lower bound when its old x-graph moves

At any reference corner angle t, the perturbation of its **physical** position is
\[
\boxed{
\delta c(t)=\phi(t)u_t+\psi(t)v_t,\quad
\delta x_c=\phi\cos t-\psi\sin t,\quad
\delta y_c=\phi\sin t+\psi\cos t.
}\tag{VC.25}
\]
The reference corner x-velocity is uniformly strictly negative on \(J_0\). By VC.24, the **new** corner x-velocity also remains negative everywhere on \(J_0\). Because \(\phi,\psi\) vanish near its endpoints, the old and new corner x-graphs have **exactly the same x-projection interval**.

For every x in that interval, let \(t_{\rm new}(x)\) be the unique angle with \(x_{c,\rm new}(t_{\rm new})=x\). The two inner rays meet there; therefore the **new actual niche** has height at least \(y_{c,\rm new}(t_{\rm new}(x))\), whether or not the **new** corner arc is globally exposed. The contribution to the new niche area is bounded **below** by
\[
\int_{J_0}(y_{c,*}+\delta y_c)
(-x_{c,*}'-\delta x_c')\,dt.
\]
Subtracting the old *actual exposed* corner-area contribution, the exact linear part is
\[
\int_{J_0}(q_*\phi-p_*\psi)\,dt,
\]
by integrating the compactly supported terms by parts. The **exact quadratic contribution to this lower bound** is
\[
\begin{aligned}
Q_{\rm corner}(\phi,\psi)
&=-\int_{J_0}(\phi\sin t+\psi\cos t)
(\phi'\cos t-\phi\sin t-\psi'\sin t-\psi\cos t)\,dt\\
&=\boxed{
\frac12\int_{J_0}(\phi^2+\psi^2)\,dt
+\int_{J_0}\phi\psi'\,dt.
}
\end{aligned}\tag{VC.26}
\]
The last identity follows by integration by parts, with **no missing boundary terms** because of compact support. The sign of the oriented cross term \(\int\phi\psi'\) is essential.

### 6b. Both stationary inner-ray flanks retain rigorous **frozen-reference** lower bounds

At the original strictly exposed first-wall stationary abscissa \(x_{Z_f,*}(t)\) for \(t\in J_0\), the reference companion wall lies strictly above the first wall. Its gap has a **positive minimum on \(J_0\)**. By the small \(C^0\) bound in VC.24, that same first wall remains the *smaller* of the two walls at the **old** abscissa and **old** parameter, even if the true new global maximizing angle changes. Therefore the new niche roof at the old stationary x is at least
\[
n_*(x)+\frac{\phi(t)}{\sin t}.
\]
Since \(x_{Z_f,*}'=(1-\rho_{f,*})\sin t>0\), integrating over its fixed x-image gives a **linear lower contribution** \(\int_{J_0}(1-\rho_{f,*})\phi\,dt\).

Likewise, on the old strictly exposed second-wall stationary x-image the new roof is bounded below by the old height plus \(\psi(t)/\cos t\), giving the linear contribution \(\int_{J_0}(1-\rho_{g,*})\psi\,dt\). These two x-images are disjoint from one another and from the moving-corner x-image; elsewhere, an unmodified reference angle still attains the old roof, so \(n_{\phi,\psi}\ge n_*\).

Add the stationary and newly parametrized moving-corner **lower bounds**. The exact result is
\[
\begin{aligned}
N_{\phi,\psi}-N_*
&\ge\int_{J_0}\bigl[
(1-\rho_{f,*}+q_*)\phi+
(1-\rho_{g,*}-p_*)\psi\bigr]dt+
Q_{\rm corner}(\phi,\psi)\\
&=\boxed{
\int_{J_0}(\rho_{f,*}\phi+\rho_{g,*}\psi)\,dt
+Q_{\rm corner}(\phi,\psi),
}
\end{aligned}\tag{VC.27}
\]
where the second equality uses the **explicit** Romik identities \(q_*=2\rho_{f,*}-1,\ p_*=1-2\rho_{g,*}\).

The proof compares with **actual complete swept niche roofs**. It never replaces them by a signed formula with unknown clipping, assumes an inner ray of the new hull is exposed, or assumes its new support curvature is \(\le1\). The only corner orientation condition is \(C^1\)-stable monotonicity of **that one original moving-corner chart**, which is a strict property of the reference and of the perturbation's first derivatives.

### 6c. The outer area cancels all linear costs; a strictly coercive quadratic remains

The **exact** planar convex-support area polarization, accounting for both vertically reflected support halves, gives
\[
\boxed{
\begin{aligned}
|K_{\phi,\psi}|-|K_*|
={}&2\int_{J_0}(\rho_{f,*}\phi+\rho_{g,*}\psi)dt\\
&+\int_{J_0}(\phi^2+\psi^2-\phi'^2-\psi'^2)dt .
\end{aligned}}\tag{VC.28}
\]
Subtract twice the niche lower bound VC.27. The linear terms cancel, leaving
\[
\boxed{
\begin{aligned}
|E(K_{\phi,\psi})|-M
&\le-\int_{J_0}\bigl(\phi'^2+\psi'^2+2\phi\psi'\bigr)dt\\
&\le-\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}(\phi'^2+\psi'^2)dt.
\end{aligned}}\tag{VC.29}
\]
For the second inequality the Dirichlet Poincaré inequality on the support interval, of length \(\ell=|J_0|\), says
\(\|\phi\|_2\le(\ell/\pi)\|\phi'\|_2\). Thus
\[
2\left|\int_{J_0}\phi\psi'\right|
\le2\ell/\pi\,\|\phi'\|_2\|\psi'\|_2
\le(\ell/\pi)(\|\phi'\|_2^2+\|\psi'\|_2^2).
\]
Because \(J_0\subset(0,\pi/2)\), the coercivity factor is **strictly greater than \(1/2\)**.

**Theorem VC3 (two independent middle-support arcs: ordinary-area strong maximality without a new curvature cap).** Under the explicit hypotheses VC.23–VC.24, the *actual full-two-turn ordinary area* obeys
\[
\boxed{
|E(K_{\phi,\psi})|
\le M-\left(1-\frac{|J_0|}{\pi}\right)
\bigl(\|\phi'\|_2^2+\|\psi'\|_2^2\bigr)<M
}
\]
for any nonzero perturbation pair. The genuine sofa may be nonsymmetric left–right, have source curvature greater than one, and possess arbitrarily complicated **new** stationary inner-ray exposure charts.

This strengthens the previous **\(C^2\)-small exact-branch** two-arc result [PJ-COUP1](spatial-half-partition-coupled-middle-variation.md): the quantitative constant is weaker, but this inequality controls a **much larger class** of actual convex-support perturbations, including curvature spikes which invalidate the old chart's stability. It also includes the vertical-corner family VC1 as the special case \((\phi,\psi)=(\varphi\sin t,\varphi\cos t)\), for which the quadratic form simplifies *exactly* to \(\int\varphi'^2\).

**The precise remaining global obstruction:** This does not cover supports modified near the reference switching angles or axis normals, changes of the actual incoming top/bottom face or horizontal projection, arbitrary far-away support charts, or partial terminal angles. It uses the **reference** global exposure decomposition only to supply the initial frozen-ray comparison. A universal sharp proof requires a calibration that replaces that reference chart with a global principle valid for *every* possible candidate hull and both independently turning motions.

## 7. From **\(C^1\)-small** to **Hausdorff-small** — and curvature atoms

The hypothesis that the two source perturbations be small in their **first derivatives** is not an independent constraint on a *genuine convex support function* sufficiently close to the smooth reference. Convexity itself upgrades local uniform support closeness to first-derivative closeness, even with atoms in the support curvature. This extends VC3 to a natural **Hausdorff topology**, rather than the substantially stronger \(C^1\)-topology, on its stated compact middle-source support subspace.

**Lemma VC4 (uniform derivative control from convex support, including jumps).** Let \(J_0\Subset J_1\Subset T\), and let \(h_*\) denote the \(C^2\) Romik upper support on \(J_1\). Let \(h\) be **any** planar convex-body support function (possibly nonsmooth, with support-curvature atoms) satisfying
\[
\|h-h_*\|_{L^\infty(J_1)}\le\varepsilon,
\qquad h''+h\ge0\quad\text{in the distribution sense}.
\]
Put \(w=h-h_*\) and \(C_0=\sup_{J_1}(h_*''+h_*)+\varepsilon\). Then \(w''\ge-C_0\,dt\) on \(J_1\). If \(r>0\) is less than the distance from \(J_0\) to the complement of \(J_1\), the one-sided angular derivatives (which exist because \(w\) is semiconvex) satisfy
\[
\boxed{
-\,\frac{2\varepsilon}{r}-\frac{C_0r}{2}
\ \le\ w'_-(t)\le w'_+(t)\
\le\frac{2\varepsilon}{r}+\frac{C_0r}{2},
\quad t\in J_0.
}\tag{VC.30}
\]
In particular, for sufficiently small \(\varepsilon\) choose \(r=2\sqrt{\varepsilon/C_0}\) and obtain the **uniform** estimate
\[
\boxed{
\|w'_\pm\|_{L^\infty(J_0)}\le2\sqrt{C_0\varepsilon}
=O(\sqrt\varepsilon).
}\tag{VC.31}
\]

**Proof.** The support-curvature positivity gives \(h''\ge-h\) as distributions, hence
\(w''\ge-h-h_*''=-(h_*''+h_*+w)\ge-C_0\). Therefore
\[
G(t)=w(t)+\tfrac12C_0t^2
\]
is convex on \(J_1\). Its one-sided derivatives are bounded above by its forward chord slope over length \(r\), and below by its backward chord slope, exactly as for every one-dimensional convex function:
\[
G'_+(t)\le\frac{G(t+r)-G(t)}r,\qquad
G'_-(t)\ge\frac{G(t)-G(t-r)}r.
\]
Subtract \(C_0t\) and use \(|w|\le\varepsilon\) to obtain the displayed upper and lower estimates. Convexity gives \(w'_-\le w'_+\) at every point. Optimize the chord length to get VC.31. \(\square\)

**Theorem VC5 (strict Hausdorff-local maximality on independent compact middle support arcs, without curvature regularity).** Fix compact intervals \(J_0\Subset J_1\Subset(\beta,\pi/2-\beta)\) satisfying VC3's strict Romik reference contact margins. There exists \(\varepsilon_*>0\) such that **every compact convex hull** \(K\) with:
1. vertical-reflection symmetry about \(y=1/2\);
2. upper-quarter supports agreeing with Romik's outside \(J_0\);
3. uniform support distance \(\sup_{\theta}|h_K(\theta)-h_{K_*}(\theta)|<\varepsilon_*\);

has a **genuine connected, canonically saturated two-full-turn envelope** whose actual hull remains \(K\), and
\[
\boxed{
|E_{\rm full}(K)|
\le M-\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}\bigl(|(f_K-f_*)'|^2+
                |(g_K-g_*)'|^2\bigr)\,dt.
}\tag{VC.32}
\]
The angular derivatives are interpreted almost everywhere. Equality forces \(h_K=h_{K_*}\). Neither left-right symmetry nor any **upper** curvature density bound, absolute continuity of curvature, absence of exposed outer-edge atoms, or smoothness of \(h_K\) is assumed.

**Proof.** Apply Lemma VC4 separately to the first and second upper-quarter support arcs (each has strictly positive smooth Romik reference curvature on \(J_1\)). Uniform support closeness makes their derivative differences uniformly small, including the one-sided traces at every possible curvature atom; outside \(J_0\) the differences vanish. It thus supplies the *geometric* \(C^1\)-smallness premise of VC3 without requiring the new support derivatives to be continuous.

The new corner abscissa is a **Lipschitz** function of the two support values and the rotating normals, with one-sided or almost-everywhere derivative obtained from VC.25; the small derivative bound makes its x-map strictly decreasing and bi-Lipschitz on the fixed reference chart. Consequently its true one-angle corner-height lower bound may be integrated by the ordinary absolutely continuous change-of-variables formula. Both frozen stationary-wall lower bounds use only the **values** of the new support, with no differentiability requirement. The resulting corner product \(y_c(-x_c')\) is integrable and its integration by parts is valid for Lipschitz perturbations.

The planar convex support-area identity is valid for \(W^{1,\infty}\) support functions by approximation or directly by polygonal curvature measures; the exact polarization VC.28 remains valid. The same Dirichlet estimate therefore proves VC.32. All full-angle feasibility, core face retention, connectedness and actual hull retention follow from the strict contact and baseline-intercept margins by the now uniformly small \(C^0/C^1\) perturbations, exactly as in VC3.

Finally the right-hand integral vanishes only when both support differences are a.e. constant on their respective compact support intervals; since they vanish outside \(J_0\), both are identically zero, and so is their vertical-reflection extension. Hence equality forces \(K=K_*\). \(\square\)

**Scope caution:** Hausdorff-smallness here is combined with the **fixed compact source-angle support** premise. This is not the claim that *every* hull close to Romik in Hausdorff distance lies in VC5: a generic nearby hull changes supports at the reference **switches, axis normals, horizontal face endpoints and different angular pieces**. Those degrees of freedom remain the principal missing global perturbation modes. VC5 is nevertheless a genuine **ordinary-area** strict maximum in an infinite-dimensional, nonsmooth support class, not a \(C^2\)-stable contact-chart calculation.

## 8. What changes in the global optimality proof

VC1 is stronger than a local second-variation calculation: it is a true **ordinary-area** comparison for a whole infinite-dimensional vertical-corner perturbation class, including O(1) **curvature spikes** and radical changes of the new niche's active contacts. The proof succeeds by **calibrating the complete new swept rays from fixed reference rays** (VC.8–VC.11), while the exact quadratic outer-area penalty \(\|\varphi'\|_2^2\) pays for any deviation. This is directly aligned with the user's outer-wall-plus-moving-corner-first approach and avoids the old pairwise clipping-deficit inequality.

But the proposed global theorem still lacks a comparison for arbitrary pairs of independent corner paths, especially **horizontal corner displacements**, moved support endpoints/top faces, separated opposite face arrangements, and actual partial terminal angles. A complete proof must construct a calibration that remains valid without Romik's *fixed reference exposed wall chart* as an anchor. VC1–VC2 alone neither yield \(|S|\le M\) unrestricted nor characterize all equality bodies.

No CI, Lean/Lake compilation or independent referee check is claimed. The new results are written proofs, subject to independent mathematical review.
