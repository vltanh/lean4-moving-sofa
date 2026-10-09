# Gate 1: existence of a sharp-spatial-score maximizer with **regular exterior wings**

**Date October 9, 2026. Status:** An actual **global optimizer regularity theorem** for the ONE active scalar spatial score \(\mathcal P\) of [SD](gate1-spatial-dual-height-width-compactness.md), **not** a local perturbation theorem and **not** a proof that its maximum is \(M/2\). It combines (i) [MID2](gate1-global-middle-chord-canonicalization.md), the unconditional score-improving reduction to a single affine middle-half roof; (ii) [FE1](gate1-spatial-exposure-moving-window-variation.md), the exact finite maximizer inequalities for the charged outer facets and **spatially clipped** inner-ray exposures; and (iii) the elementary adjacent-moving-wall bound [WR.1](one-turn-weighted-regularity.md), which is an inequality for *any* polygon, not a weighted-optimality theorem.

**Main theorem:** Among all maximizers of the unrestricted one-cap spatial objective, **there exists one** of height exactly one and width \(8/5<W<6\) whose upper roof is **affine on the central width-half** and whose upper support-curvature measure is **absolutely continuous with an essentially bounded density at every other open-quarter normal**, except potentially the horizontal **top** normal \(\theta=\pi/2\). The only possible additional upper-half curvature atom is the **single normal of the affine middle facet**. This rules out arbitrary singular-continuous wing curvature and infinitely concentrated exterior-wing facets **at this chosen scalar optimizer**, without assuming a bound \(\rho\le1\), a finite niche contact pattern or Romik proximity.

**The sharp value remains OPEN:** The density bound is a coarse uniform \(C\), **not** the critical corridor curvature bound \(1\); neither the central facet's slope nor the top-face location/length is determined. This result passes no full-turn area gate on its own.

## 1. State the exact geometric object

For a compact downward convex cap \(U\subset\mathbb R\times[0,1]\) of width \(W>0\), let \(A_U\) be its concave upper roof and
\[
J=[l+W/4,r-W/4],\qquad
\mathcal P(U)=\int_{I\setminus J}A_U\,dx-\int_Jn_U\,dx,
\]
where \(n_U(x)\) is the **entire continuous-angle two-attached-inner-wall** positive niche roof from [SD.1](gate1-spatial-dual-height-width-compactness.md). SD2–SD3 prove height-one attainment and \(8/5<W<6\) for any value at least the reference's \(M/2\). MID2 gives a score-nondecreasing transformation of *every cap* whose output has \(A_U|_J\) affine.

Pick **one such globally maximizing canonical cap**, denoted \(U_*\), translated so its horizontal projection lies strictly inside a fixed artificial box \([-R,R]\) with \(R>7\), and write
\[
\boxed{A_*(x)=a+sx\quad(x\in J_*).}\tag{RG.1}
\]
Its affine facet has unique outward normal
\[
\boxed{n_c=\frac{(-s,1)}{\sqrt{1+s^2}},\qquad
\theta_c=\arg n_c\in(0,\pi).}\tag{RG.2}
\]
The maximal facet may extend outside J*. The height-one **top** face, if a nondegenerate horizontal segment, has normal \(e_y\), \(\theta=\pi/2\). No assertion that these two normals coincide is made.

Let \(\sigma_*=h_{U_*}+h_{U_*}''\) on the **open upper semicircle**, interpreted as the nonnegative surface-area/curvature **measure** of the actual convex cap. It counts both smooth curvature and exposed-facet atoms (but not the bottom-face atom at the downward normal).

## 2. Finite selections converge to this **particular canonical global optimizer**

Fix grid angles \(\theta_j=j\delta\), \(j=0,\ldots,2n\), \(\delta=\pi/(2n)\), with n dyadic so grids are nested. Use the finite positive niche \(n_{n,U}\) of angles \(0<t_j<L=\pi/2\), \(t_j=j\delta\), \(1\le j<n\), and
\[
\mathcal P_n(U)=\int_{I_U\setminus J(U)} A_U-\int_{J(U)}n_{n,U}.
\tag{RG.3}
\]
On the fixed compact space of all downward convex caps inside \([-R,R]\times[0,1]\), including zero-area limits, the full positive niche and every finite grid niche are jointly **uniformly continuous in cap support and abscissa**, by the endpoint truncation and angular-fraction argument of [SD3](gate1-spatial-dual-height-width-compactness.md). The finite roofs \(n_{n,U}\) monotonically increase to the complete roof \(n_U\). Hence Dini's theorem on the compact product of cap domain and x-box gives
\[
\sup_{U,x}|n_U(x)-n_{n,U}(x)|\longrightarrow0,\qquad
e_n:=\sup_U(\mathcal P_n(U)-\mathcal P(U))\longrightarrow0 .
\tag{RG.4}
\]
(The exterior-score term is identical in both, so \(e_n\ge0\).) The finite objective \(\mathcal P_n\) is continuous even though J moves with the width, by the uniform boundedness of its roof and convergence of interval endpoints.

For each n, let \(\mathcal G_n\) be the compact family of polygons cut by the floor, the upper grid halfplanes at their own supporting values, and the fixed artificial box walls. For any cap U, its grid circumscription \(C_n(U)\supseteq U\) has exactly the **same** support values at every grid normal, so the same sampled niche \(n_{n,U}\), same horizontal projection (the two horizontal axis normals are sampled), and exterior roof at least \(A_U\). Therefore
\[
\boxed{\mathcal P_n(C_n(U))\ge\mathcal P_n(U)\ge\mathcal P(U).}\tag{RG.5}
\]

Choose positive sample weights
\[
w_0=w_{2n}=1/4,\qquad
w_j=\delta/(2\pi)\quad(0<j<2n),\qquad\sum w_j\le1,
\]
and
\[
D_n(U,U_*)^2=\sum_{j=0}^{2n}w_j[h_U(\theta_j)-h_{U_*}(\theta_j)]^2,\qquad
\eta_n=\sqrt{e_n}+1/n.
\tag{RG.6}
\]
Let \(U_n\in\mathcal G_n\) maximize
\(\mathcal P_n(U)-\eta_nD_n(U,U_*)^2\).
Since \(C_n(U_*)\) has **zero penalty**, RG.5 and maximality give a penalized value at least \(\mathcal P(U_*)=\mathcal P_{\max}\). But for arbitrary \(U_n\), RG.4 gives
\[
\mathcal P_n(U_n)\le\mathcal P(U_n)+e_n
\le\mathcal P_{\max}+e_n.
\]
Thus
\[
\boxed{D_n(U_n,U_*)^2\le e_n/\eta_n\longrightarrow0.}\tag{RG.7}
\]
By Hausdorff compactness and Riemann-sum convergence of the strictly positive sample weights, every limit of \(U_n\) has identical upper-half support function to \(U_*\), hence is exactly \(U_*\). Therefore the **whole selected sequence** satisfies
\[
\boxed{U_n\longrightarrow U_*\quad\text{in Hausdorff support distance},}\tag{RG.8}
\]
including all actual upper/lower top-roof and horizontal-axis support data. As \(U_*\) lies strictly inside the artificial vertical box sides, so do \(U_n\) eventually. This permits all following outward source-facet variations.

No curvature cap, candidate phase chart, or symmetry of the selected polygons has been inserted.

## 3. Finite spatial exposure + adjacent wall geometry bounds all but the **uncharged** outer facet length

Let \(\ell_{n,j}\) be the *total* upper outer-facet arclength of \(U_n\) at normal \(\theta_j\), and let \(\ell_{n,j}^{\rm wing}\) be the portion over the charged exterior wings \(I_n\setminus J_n\). Put
\(\ell_{n,j}^{\rm mid}=\ell_{n,j}-\ell_{n,j}^{\rm wing}\ge0\).
For \(j\notin\{0,n,2n\}\), [FE.9](gate1-spatial-exposure-moving-window-variation.md) gives
\[
\ell_{n,j}^{\rm wing}\le\tau_{n,j}^{\rm middle}+b_{n,j},
\qquad
b_{n,j}=4B\eta_nw_j,\quad
B=R+1.
\tag{RG.9}
\]
Here \(\tau_{n,j}^{\rm middle}\) is the exposed length of the actual source inner wall **inside J_n**. It is nonnegative and bounded by the **full finite-niche source exposure** \(\tau_{n,j}^{\rm full}\).

The independent elementary neighboring-two-wall estimate [WR.1](one-turn-weighted-regularity.md) applies to every finite upper grid polygon and every interior source normal, in both upper quarters. It gives
\[
\boxed{
\tau_{n,j}^{\rm full}
\le(6B+4)\delta+
(2\tan(\delta/2)-\ell_{n,j})_+ .
}\tag{RG.10}
\]
It comes from intersecting the exposed ray's parameter line with the two **neighboring first** and **neighboring companion** inner walls. It does not assume maximizing the *different* weighted objective \(\Psi\), nor that any local ray is globally visible.

If \(\ell_{n,j}<2\tan(\delta/2)\), then \(\ell_{n,j}\le2\delta\).
Otherwise the positive-part term in RG.10 vanishes and
\(\ell_{n,j}=\ell_{n,j}^{\rm wing}+\ell_{n,j}^{\rm mid}\le(6B+4)\delta+b_{n,j}+\ell_{n,j}^{\rm mid}\).
In both cases,
\[
\boxed{
\ell_{n,j}\le C\delta+b_{n,j}+\ell_{n,j}^{\rm mid},
\qquad C=6B+6 .
}\tag{RG.11}
\]
The only part not controlled by an \(O(\delta)\) geometric bound is the outer facet portion over the **uncharged middle roof**.

## 4. The affine middle roof prevents any **off-facet** concentration

Let \(E\Subset(0,\pi)\setminus\{\theta_c,\pi/2\}\) be any compact set of upper supporting normal angles separated by a positive angular distance from the central affine-facet normal and the horizontal top normal.

**Lemma RG1 (uncharged noncentral facet mass disappears).**
\[
\boxed{
\lim_{n\to\infty}
\sum_{\theta_j\in E}\ell_{n,j}^{\rm mid}=0.
}\tag{RG.12}
\]

**Proof.** Since \(j_\pm^*\) are strictly interior abscissae of the limiting projection, concavity and bounded vertical height give a uniform Lipschitz constant for the roofs \(A_n\) on a fixed slightly larger compact horizontal interval containing all \(J_n\), for n large. For example a roof between zero and one on an interval whose points stay at distance \(\delta_x>0\) from its projection endpoints has one-sided slope magnitude at most \(1/\delta_x\), by comparing with endpoint values and concavity.

Hausdorff convergence RG.8 gives uniform convergence of these roofs to \(A_*=a+sx\) on that compact interval. On any strictly smaller middle interval
\([j_-^*+\varepsilon,j_+^*-\varepsilon]\), the secant-slope inequalities for concave functions imply all one-sided slopes \(A'_{n,\pm}\) converge **uniformly** to the constant s. Hence for large n, every outer facet over that strict middle interval has outward normal in a small fixed neighborhood of \(\theta_c\), disjoint from E. (At a corner, all normals are between the adjacent one-sided slope normals and obey the same bound.)

Only the two boundary strips of horizontal width \(O(\varepsilon)+o_n(1)\) near \(j_\pm^*\) remain. Their *total* upper-boundary arclength is at most
\((1+L_x)\times\text{total horizontal width}\), using the uniform Lipschitz constant \(L_x\). Thus the sum on the left of RG.12 has limsup at most \(4(1+L_x)\varepsilon\), independently of E. Let \(\varepsilon\downarrow0\). \(\square\)

This argument uses the **entire affine central facet** furnished by MID2. Merely having a nonsmooth cap or Hausdorff convergence would not rule out concentration of curvature on an arbitrary middle arc; the global chord canonicalization is what makes RG.12 true.

## 5. The global-exterior-wing curvature density theorem

For each finite convex polygon, the upper surface-area measure is exactly its facet-normal length measure
\(\sigma_n=\sum_{j=0}^{2n}\ell_{n,j}\,\delta_{\theta_j}\).
Uniform convergence of the convex support functions, their distributional identity \(\sigma_n=h_n+h_n''\), and bounded total perimeter imply weak convergence
\[
\sigma_n\rightharpoonup\sigma_* \quad\text{on the upper semicircle}.
\tag{RG.13}
\]

Take any compact E as above, and sum RG.11 over grid indices \(\theta_j\in E\):
\[
\begin{aligned}
\sigma_n(E)
&\le C\bigl(|\mathrm{conv}(E)|+2\delta\bigr)
+\sum_j b_{n,j}
+\sum_{\theta_j\in E}\ell_{n,j}^{\rm mid}
\end{aligned}
\]
for an interval E, and by additivity for finite unions of intervals. The penalty mass satisfies \(\sum_j b_{n,j}\le4B\eta_n\to0\), and the middle term vanishes by RG.12. By testing against continuous nonnegative functions supported away from \(\{\theta_c,\pi/2\}\), or using the weak-convergence open-set inequality on finite unions of intervals, obtain
\[
\boxed{
\sigma_*(E)\le C\,|E|
\quad\text{for all Borel }E\subset(0,\pi)\setminus\{\theta_c,\pi/2\}.
}\tag{RG.14}
\]

**Theorem RG2 (global one-cap spatial maximizer: all arbitrary wing singularities removed).**
There exists a global maximizer \(U_*\) of the scalar spatial score \(\mathcal P\), with exactly unit height and width \(8/5<W<6\), whose roof is affine on J and whose upper curvature measure decomposes as
\[
\boxed{
\sigma_*|_{(0,\pi)}
=\rho(\theta)\,d\theta+
a_c\,\delta_{\theta_c}
+a_t\,\delta_{\pi/2},
\qquad
0\le\rho(\theta)\le6(R+1)+6\quad\text{a.e.},
}\tag{RG.15}
\]
where \(a_c,a_t\ge0\) represent at most **two** permitted facet atoms. When \(\theta_c=\pi/2\), combine them into a single top-face atom; a normal with no facet has zero atom. No singular-continuous upper curvature remains at any interior upper normal, and no other interior curvature atoms are present.

**Proof.** Choose a score maximizer, canonize it by MID2 to make its middle roof affine while keeping its score maximal, and use RG.7–RG.14. The bound on the absolutely continuous density follows from absolute measure domination on the complement of the two angles. All remaining nonnegative measure supported on those two singleton normals consists of atoms. \(\square\)

The result is **existential**: an uncanonicalized score maximizer could have gratuitous interior roof curvature which does not change the charged objective, so there is no claim that *every* maximizer shares RG.15. No upper unit-curvature domination \(\rho\le1\), endpoint balance equality, signed roof formula, or candidate contact chart has been inferred.

## 5b. A *sharp-form* nonlinear bound on the wing densities

The coarse absolute bound RG.15 can be strengthened to exactly the **velocity-dependent geometric upper function** appearing in the independently established one-turn neighboring-wall inequality, *without assuming this spatial maximizer also maximizes the different weighted objective*.

On the two upper normal quarters, put
\[
f(t)=h_{U_*}(u_t),\quad g(t)=h_{U_*}(v_t),\quad
p(t)=f'(t)-g(t)+1,\quad q(t)=g'(t)+f(t)-1.
\]
The selected canonical cap is \(W^{2,\infty}\) on compact subintervals of the open quarters away from the **one central-facet atom** (and from their axis endpoints); thus \(p,q\) and the curvature densities
\[
\rho_f=f+f'',\qquad\rho_g=g+g''
\]
are defined almost everywhere, with possible point jumps of derivatives only at the explicitly allowed facet normals.

Write
\[
\boxed{\kappa(z)=\max\left\{|z|,\frac{1+|z|}{2}\right\}.}\tag{RG.16}
\]

**Theorem RG3 (universal wing source-curvature constraint at a global P maximizer).** At almost every open-quarter angle whose corresponding exposed outer normal is not the central facet normal,
\[
\boxed{
0\le\rho_f(t)\le\kappa(q(t)),\qquad
0\le\rho_g(t)\le\kappa(p(t)).
}\tag{RG.17}
\]
There are no singular-continuous source curvatures on those same intervals; RG.17 is a **pointwise necessary condition of a global score optimizer**, not an extra assumed smoothness or corridor curvature domination.

**Proof.** For the first quarter, use [WR, Section 4](one-turn-weighted-regularity.md) solely as a **polygonal geometric inequality**. Every grid facet of every selected U_n obeys
\[
\tau^{\rm full}_{n,j}\le
\tan\delta\bigl(|q^+_{n,j}|+\tan(\delta/2)\bigr)
+\bigl(2\tan(\delta/2)-\ell_{n,j}\bigr)_+,
\tag{RG.18}
\]
where \(q^+_{n,j}=h_n(\theta_j)+
[h_n(\theta_{j+n+1})-\cos\delta\,h_n(\theta_{j+n})]/\sin\delta-1\).
This is the neighboring *companion* wall bound for the first source, not a stationary-flux equality.

Combine RG.18 with the **spatial** finite maximality inequality
\(
\ell_{n,j}\le \tau^{\rm middle}_{n,j}+b_{n,j}
+\ell^{\rm mid}_{n,j}
\)
and \(\tau^{\rm middle}\le\tau^{\rm full}\).
If \(\ell_{n,j}\ge 2\tan(\delta/2)\), the positive part vanishes and the result is
\[
\ell_{n,j}\le\ell^{\rm mid}_{n,j}
+\delta|q^+_{n,j}|+O(\delta^2)+b_{n,j}.
\]
If \(\ell_{n,j}<2\tan(\delta/2)\), move its \(-\ell_{n,j}\) from the positive-part expression to the left to obtain
\[
2\ell_{n,j}\le\ell^{\rm mid}_{n,j}
+\delta(1+|q^+_{n,j}|)+O(\delta^2)+b_{n,j}.
\]
The two cases combine, with the larger harmless middle term, to give the exact uniform inequality
\[
\boxed{
\ell_{n,j}\le
\kappa(q^+_{n,j})\delta+C_1\delta^2
+b_{n,j}+\ell^{\rm mid}_{n,j}.
}\tag{RG.19}
\]
The \(O(\delta^2)\) coefficient \(C_1\) is independent of n,j because all U_n lie in the fixed artificial R-box and all their supports are uniformly bounded and Lipschitz.

On a compact source-angle interval avoiding \(\theta_c\) and the top normal, RG1 proves the sum of the \(\ell^{\rm mid}\) contributions vanishes. The penalty sum also tends to zero. The companion one-sided grid derivatives \(q^+_{n,j}\) converge in \(L^1_{\rm loc}\) to \(q(t)\): for convex supports, uniform convergence implies their a.e. first derivatives converge at all differentiability points; uniform boundedness gives dominated \(L^1\) convergence. The function \(\kappa\) is 1-Lipschitz, so Riemann summation of RG.19 over any such source interval yields the measure inequality
\[
\sigma_f(E)\le\int_E\kappa(q(t))\,dt
\quad\text{for every interval }E
\text{ avoiding the exceptional normals}.
\]
RG2 has already proved absolute continuity there, giving its pointwise density bound.

For the second quarter, reverse horizontal x and interchange the two source normal families in the same elementary neighboring-wall argument. Its geometric companion velocity is \(p\), yielding \(\rho_g\le\kappa(p)\). Countably many compact intervals exhaust the nonexceptional portions of both quarters. \(\square\)

**The sharp-wall threshold remains missing:** \(\kappa(z)\le1\) if \(|z|\le1\), but \(\kappa(z)>1\) when \(|z|>1\). RG3 does **not** establish \(|p|,|q|\le1\) for the global spatial maximizer. The previous weighted \(\Psi\) proof obtained such control using a **different** global balance and a niche-height bound; those facts do not automatically transfer to the spatial P objective. In particular the permitted central affine facet may have a genuine jump in source velocity, changing the matching/flux equations. This is now the explicit **remaining global value theorem** to attack.

## 6. Why Gate 1 is **not** yet passed

The curvature bound \(6(R+1)+6\) is only a compactness/regularity bound, **not the sharp physical corridor bound one**. To prove \(\mathcal P_{\max}=M/2\), one still must:

1. Derive and pass to the limit the **correct charged exterior/niche exposure balance** (not the differently weighted \(\Psi\) balance), including the moving central J endpoint pressures [FE.9](gate1-spatial-exposure-moving-window-variation.md).
2. Show that all global spatial-score maximizing supports meet sufficiently strong contact/curvature and top-face conditions to admit an **actual global sharp analytic value comparison**, or find a more direct one-cap area inequality. RG2's weak density upper bound alone does not justify replacing the full physical niche by the Romik contact quadratic.
3. Retain the possibility of a **tilted central affine facet** and a separate horizontal top facet. Prove any further normalization rather than assuming that the top face equals J or that niche zero sets converge in measure.
4. Handle the original two-handed coupled loss if the stronger one-cap inequality fails, and independently handle partial terminal angles after the full-turn value is established.

RG2 is a genuine global maximizer-domain simplification **within the single active Gate 1 scalar proof strategy**, not another named near-reference subcase. It does **not** improve the numerical unrestricted upper bound and does **not** establish \(\mathcal P\le M/2\).

No CI, Lean/Lake build, numerical optimization as proof, or claim of Romik optimality. All estimates are mathematical support/convexity arguments from the listed globally quantified components, subject to independent review.
