# Gate 1: endpoint complementarity and the remaining exposure defect

**October 9, 2026. Written proof, independently checked within this research session; not externally refereed or Lean-verified.** This repairs an indispensable variational dependency of the active spatial one-cap problem and proves its exact limiting endpoint and exposure laws. It does **not** prove the sharp value \(\mathcal P\le M/2\), and **Gate 1 remains ACTIVE**.

The former unconditional outward-axis derivatives in [FE.6–FE.7](gate1-spatial-exposure-moving-window-variation.md) were false when an end face had zero length: moving a redundant vertical constraint does not move the actual cap or its middle window. FE now contains the correction and two exact counterexamples. The replacement below uses **actual inward trimming and horizontal erosion**, support monotonicity, and the valid floating-facet inequalities. It requires no positive end faces, positive top-face length, niche zero-set convergence, or candidate contact chart.

## 1. Exact global conclusions and their scope

Let U be a height-one global maximizer of the [SD.2 spatial score](gate1-spatial-dual-height-width-compactness.md), with projection \(I=[l,r]\), width W, roof A, full continuous-angle positive niche n, and
\[
j_-=(3l+r)/4,\qquad j_+=(l+3r)/4,\qquad J=[j_-,j_+].
\]
The global existence and width theorem SD3 gives \(8/5<W<6\). Define the **boundary values**, not the source-angle velocities,
\[
q_\pm=A(j_\pm)+n(j_\pm),\qquad
C_R=(3q_+-q_-)/4,\quad C_L=(3q_--q_+)/4,
\]
\[
e_R=A(r),\qquad e_L=A(l),\qquad z_+=\max(z,0).
\tag{EP.1}
\]

**Theorem EP1 (global endpoint complementarity).**
\[
\boxed{e_R=(C_R)_+,\qquad e_L=(C_L)_+.}
\tag{EP.2}
\]
In particular, a zero end face permits a **negative** corresponding pressure; it must not be assigned the positive-face stationary equation. Since \(C_R+C_L=(q_-+q_+)/2>0\), at least one end face is positive.

There is also an exact exposure statement. Use the selected finite polygons below, and let \(\nu_R,\nu_L\) be any joint weak limits of their positive middle-window inner-wall exposure measures. Let \(\omega_R,\omega_L\) be the corresponding limits of their charged outer-wing facet measures, omitting axes and the horizontal top normal. Then:

**Theorem EP2 (the remaining limiting exposure defect).** These measures have bounded densities, \(\nu_Q\ge\omega_Q\) for \(Q=R,L\), and
\[
\boxed{
\int_{[0,\pi/2]}\cos\theta\,d(\nu_R-\omega_R)=(-C_R)_+,\qquad
\int_{[\pi/2,\pi]}(-\cos\theta)\,d(\nu_L-\omega_L)=(-C_L)_+.
}
\tag{EP.3}
\]
Consequently \(C_Q\ge0\) forces \(\nu_Q=\omega_Q\) on that entire source quarter. At least one quarter has equality. An unmatched limiting exposure can occur only on a side with **zero end height and negative pressure**, with the moment in EP.3 fixed exactly.

For the MID2-canonical maximizer, \(\omega\) is the actual outer-wing normal measure with the top face omitted. **We do not identify \(\nu\) with the arclength measure of the limiting positive niche graph.** Arbitrarily shallow finite niche pieces can disappear at height zero while their exposure measures retain mass. EP2 is a statement about their precisely defined limits, not an assumed continuity theorem for niche zero sets.

## 2. Finite selection and the valid outward inequalities

Translate the prescribed maximizer strictly inside \([-R,R]\times[0,1]\), with \(R>7\), and use the dyadic upper grids and penalized selections of [RG, Section 2](gate1-spatial-maximizer-wing-curvature-regularity.md):
\[
\theta_j=j\delta_n,\quad\delta_n=\pi/(2n),\qquad
F_n(V)=P_n(V)-\eta_n\sum_{j=0}^{2n}w_j
       [h_V(\theta_j)-h_U(\theta_j)]^2.
\tag{EP.4}
\]
Here \(\sum_jw_j\le1\), \(\eta_n\to0\), all absolute supports are bounded by \(B=R+1\), and U_n maximizes F_n over the upper-grid polygon class. The selection proof gives
\[
U_n\longrightarrow U\quad\text{in Hausdorff distance},\qquad W_n\ge1
\quad\text{eventually}.
\tag{EP.5}
\]
To recall why the selection is legitimate: finite niches converge uniformly on the bounded cap-and-abscissa domain by SD3 and Dini's theorem. If \(a_n=\sup(P_n-P)\to0\), choose \(\eta_n=\sqrt{a_n}+1/n\). Grid circumscription of U has the same sampled supports, zero penalty, and at least its score. Maximality then bounds the selected squared support distance by \(a_n/\eta_n\to0\), proving EP.5. This argument targets any prescribed global maximizer; affinity of its middle roof is not needed for EP1.

Write \(q_{n,\pm},C_{n,R},C_{n,L},e_{n,R},e_{n,L}\) for the finite counterparts of EP.1. The corrected [FE.9a](gate1-spatial-exposure-moving-window-variation.md) gives
\[
e_{n,R}\le(C_{n,R}+b_{n,0})_+,\qquad
e_{n,L}\le(C_{n,L}+b_{n,2n})_+,
\quad b_{n,j}=4B\eta_nw_j.
\tag{EP.6}
\]
Indeed, a positive end face admits an outward move with derivative \(e-C\) and only its own sampled support changes. A zero face gives no outward constraint: the retained last sloping roof halfplane and the floor already imply the old horizontal endpoint. This is exactly why the positive parts are necessary.

For non-axis, non-top normals, the unchanged floating-facet inequality is
\[
\ell^{\rm wing}_{n,j}\le\tau_{n,j}+b_{n,j},\qquad
\beta_n:=\sum_jb_{n,j}\le4B\eta_n\longrightarrow0.
\tag{EP.7}
\]
Here \(\tau_{n,j}\) is exposed positive inner-wall arclength **inside J_n**. Only EP.7, not the former axis formulas, is used in the regularity estimates below.

## 3. Actual inward trimming gives the opposite pressure inequality

For any downward cap of height at most one, put
\[
U^-_\varepsilon=U\cap\{x\le r-\varepsilon\},\qquad0<\varepsilon<W.
\]
Its projection is exactly \([l,r-\varepsilon]\) and its roof agrees with A there. Every support decreases, so its finite or full positive niche is pointwise at most the old niche.

There is a uniform geometric estimate even when the end face vanishes:
\[
\boxed{d_H(U^-_\varepsilon,U)
\le\varepsilon\sqrt{1+(W-\varepsilon)^{-2}}.}
\tag{EP.8}
\]
For a removed point \((x,y)\), compare with \((r-\varepsilon,\min(y,A(r-\varepsilon)))\). If a vertical displacement is needed, concavity bounds the increasing secant slope by
\[
\frac{A(x)-A(r-\varepsilon)}{x-r+\varepsilon}
\le\frac{A(r-\varepsilon)-A(l)}{W-\varepsilon}
\le\frac1{W-\varepsilon}.
\]
This proves EP.8. For \(W\ge1\), \(\varepsilon\le1/2\), the bound is \(\sqrt5\varepsilon\).

Keep the old niche on the new window as an upper comparison for the trimmed niche. The actual roof is unchanged on the retained interval, while the window endpoints move by \(-\varepsilon/4,-3\varepsilon/4\). Ordinary integration at these endpoints gives
\[
P_n(U^-_\varepsilon)-P_n(U)
\ge\varepsilon(C_R-e_R)+o(\varepsilon).
\tag{EP.9}
\]
For each fixed n this uses continuity at the interior window endpoints and one-sided continuity of A at r. It does **not** freeze the actual sampled supports under an inward cut. The same argument works directly for the full niche.

Trimming preserves the finite grid-polygon class. Some old bounds may become redundant, but replacing them by the new polygon's actual sampled supports gives the same intersection. The squared-support penalty changes in absolute value by at most \(4B\eta_n d_H\), since its total weight is at most one. Penalized maximality, EP.8 and \(\varepsilon\downarrow0\) therefore yield
\[
e_{n,R}\ge C_{n,R}-d_n,\qquad
e_{n,L}\ge C_{n,L}-d_n,
\qquad d_n=4\sqrt5 B\eta_n.
\tag{EP.10}
\]
Reflection supplies the left inequality. Combining nonnegativity, EP.6 and EP.10 gives the finite approximate complementarity
\[
\boxed{
-d_n\le e_{n,R}-(C_{n,R})_+\le b_{n,0},\qquad
-d_n\le e_{n,L}-(C_{n,L})_+\le b_{n,2n}.}
\tag{EP.11}
\]
At an unpenalized finite maximizer these are exact equalities. No positive-face hypothesis is left in EP.11.

## 4. End-face convergence and the proof of EP1

Hausdorff convergence alone does not imply end-face length convergence: nearby floating facets might accumulate into an axis atom. The required exclusion follows from the valid floating-facet estimates.

Every point of J_n is at distance at least \(W_n/4\ge1/4\) from both ends. Concavity and \(0\le A_n\le1\) bound its one-sided slopes between -4 and 4. Hence for any fixed \(0<a<\arctan(1/4)\), facets with normals in \((0,a)\) or \((\pi-a,\pi)\) have **zero middle length**. The neighboring-wall estimate [WR.1](one-turn-weighted-regularity.md), combined with EP.7 as in RG.11, gives
\[
\sum_{0<\theta_j<a}\ell_{n,j}\le C(a+\delta_n)+\beta_n,
\qquad
\sum_{\pi-a<\theta_j<\pi}\ell_{n,j}\le C(a+\delta_n)+\beta_n,
\quad C=6B+6.
\tag{EP.12}
\]

Let \(\sigma_n\rightharpoonup\sigma\) be the full circular surface-area measures, whose weak convergence follows from uniform support convergence and \(\sigma=h+h''\). Downward caps have no curvature mass in the open lower quarters; their bottom-face atom is away from the two horizontal axis normals. Thus
\[
\sigma_n(\{0\})=e_{n,R},\qquad
\sigma_n((-a,a))\le e_{n,R}+C(a+\delta_n)+\beta_n.
\]
Portmanteau on the closed singleton gives \(\limsup e_{n,R}\le e_R\). On the open arc, EP.12 gives
\[
e_R\le\sigma((-a,a))\le\liminf_n\sigma_n((-a,a))
\le\liminf_ne_{n,R}+Ca.
\]
Let a decrease to zero. This proves \(e_{n,R}\to e_R\); reflection gives \(e_{n,L}\to e_L\).

The roofs converge uniformly near the interior J endpoints by concavity and Hausdorff convergence. The selected finite niches converge uniformly to the full niche by the uniform finite-angle approximation and SD3. The moving window endpoints also converge, so
\[
q_{n,\pm}\to q_\pm,\qquad C_{n,Q}\to C_Q.
\tag{EP.13}
\]
Pass to the limit in EP.11 to obtain EP.2. This proof uses no axis pressure in EP.12 and has no circular dependence on the statement being proved. Since A is strictly positive at both interior J endpoints for a positive-area cap, \(q_-+q_+>0\), proving the stated positive-end consequence.

## 5. Horizontal erosion supplies the missing exposure moments

Define the right erosion of any downward convex cap by
\[
E^R_\varepsilon=U\cap(U-\varepsilon e_x),\qquad0<\varepsilon<W.
\tag{EP.14}
\]
Its projection and roof are exactly
\[
[l,r-\varepsilon],\qquad A^R_\varepsilon(x)=\min(A(x),A(x+\varepsilon)).
\]
It remains a downward convex cap even when its old top face is a point. For every unit normal v,
\[
h_{E^R_\varepsilon}(v)\le h_U(v)-\varepsilon(v_x)_+.
\tag{EP.15}
\]
This is an **inequality**; equality is not assumed when horizontal sections disappear.

Erosion also has uniform linear Hausdorff control. Put \(\lambda=\varepsilon/W\). For any \(p\in U\), the two points
\[
z=(1-\lambda)p+\lambda(l,0),\qquad
z+\varepsilon e_x=(1-\lambda)p+\lambda(r,0)
\]
belong to U. Thus z belongs to the erosion, and
\[
d_H(E^R_\varepsilon,U)\le(\operatorname{diam}U/W)\varepsilon.
\tag{EP.16}
\]
The reflected left erosion has projection \([l+\varepsilon,r]\), roof \(\min(A(x),A(x-\varepsilon))\), and the analogous support and distance bounds. Grid polygons remain grid polygons because the intersection only tightens parallel grid halfplanes.

For a fixed selected polygon define the **virtual** support values
\[
\widehat h_j=h_{U_n}(\theta_j)-\varepsilon(\cos\theta_j)_+.
\]
They need not be the supports of a body. Nonetheless their finite max/min niche dominates the actual eroded niche by EP.15. Only the first-quarter inner walls move in this virtual family. On the fixed old window, their finite union-area derivative is
\[
\int_{J_n}\widehat n_{n,\varepsilon}
=\int_{J_n}n_n-\varepsilon\sum_{0<j<n}\tau_{n,j}\cos\theta_j+o(\varepsilon).
\tag{EP.17}
\]
Each exposed relative edge interior contributes its arclength times inward normal displacement. Distinct source lines are nonparallel unless they are the same source. Their finitely many intersections, floor contacts and window endpoints contribute only \(O(\varepsilon^2)\); a zero-height tent birth has the same order. This is a **finite** polygonal area derivative, with \(\varepsilon\to0\) before \(n\to\infty\), not a differentiability assertion for the complete niche.

At almost every fixed x the eroded outer-roof derivative is \(\min(0,A_n'(x))\). Thus its integral over the charged exterior is
\[
-\sum_{0<j<n}\ell^{\rm wing}_{n,j}\cos\theta_j.
\]
Include the removed right sliver and both moving-J boundary terms. With
\[
D_{n,R}=\sum_{0<j<n}(\tau_{n,j}-\ell^{\rm wing}_{n,j})\cos\theta_j,
\quad
D_{n,L}=\sum_{n<j<2n}(\tau_{n,j}-\ell^{\rm wing}_{n,j})(-\cos\theta_j),
\tag{EP.18}
\]
the two actual erosions satisfy
\[
P_n(E^Q_\varepsilon)-P_n(U_n)
\ge\varepsilon(D_{n,Q}-e_{n,Q}+C_{n,Q})+o(\varepsilon),\quad Q=R,L.
\tag{EP.19}
\]
The penalty error is at most \(4B\eta_n d_H\). For a fixed diameter bound D_0, EP.7, EP.16 and maximality yield
\[
\boxed{-\beta_n\le D_{n,Q}
\le e_{n,Q}-C_{n,Q}+4BD_0\eta_n.}
\tag{EP.20}
\]
No top-face length or end-face positivity has been used.

## 6. Translation identifies both defects exactly

The finite cap and niche roofs are continuous piecewise-linear graphs. Integrating their slopes gives
\[
\sum_j\tau_{n,j}\cos\theta_j=n_n(j_{n,-})-n_n(j_{n,+}),
\]
\[
\sum_j\ell^{\rm wing}_{n,j}\cos\theta_j
=e_{n,L}-e_{n,R}+A_n(j_{n,+})-A_n(j_{n,-}).
\]
The sums omit axes and the top normal; top pieces have zero cosine. All positive niche components are included, and their zero-height endpoints cancel. Subtracting gives the exact identity
\[
\boxed{D_{n,R}-D_{n,L}
=(e_{n,R}-C_{n,R})-(e_{n,L}-C_{n,L}).}
\tag{EP.21}
\]

The neighboring-wall bound also gives, for **every** non-axis, non-top index,
\[
0\le\tau_{n,j}\le(6B+4)\delta_n+
(2\tan(\delta_n/2)-\ell_{n,j})_+
\le(6B+6)\delta_n.
\tag{EP.22}
\]
Hence the measures
\[
\nu_{n,R}=\sum_{0<j<n}\tau_{n,j}\delta_{\theta_j},\quad
\omega_{n,R}=\sum_{0<j<n}\ell^{\rm wing}_{n,j}\delta_{\theta_j}
\]
and their second-quarter counterparts have joint weak subsequences. EP.7 and EP.22 imply that every limit obeys
\[
0\le\omega_Q\le\nu_Q\le(6B+6)\,d\theta.
\tag{EP.23}
\]
In particular there are no endpoint atoms where the cosine weights vanish.

Let \(D_R,D_L\) be the corresponding cosine-weighted nonnegative defect moments. Pass to the limit in EP.20 and EP.21 using EP1:
\[
0\le D_Q\le(-C_Q)_+,
\qquad D_R-D_L=(-C_R)_+-(-C_L)_+.
\tag{EP.24}
\]
At least one pressure is positive since their sum is positive. Its upper bound in EP.24 is zero. The difference identity then forces equality in the other bound too, proving EP.3. If \(C_Q\ge0\), a nonnegative measure with zero strictly positive interior cosine moment must vanish; EP.23 excludes an atom at the remaining top endpoint. Thus \(\nu_Q=\omega_Q\).

For completeness, identify \(\omega\) with the actual charged outer-wing normal measure by testing against a continuous angular function supported away from the axes and top normal. On interior spatial intervals, concave roofs converge uniformly and their slopes converge almost everywhere. The integrand
\(\varphi(\arg(-A_n',1))\sqrt{1+(A_n')^2}\)
is uniformly bounded: the angular cutoff removes arbitrarily steep slopes. Dominated convergence therefore applies, and shrinking spatial strips at the moving projection endpoints contribute nothing. Strips beside the moving J endpoints have uniformly bounded slopes as well. This identifies the measure off the omitted normals. EP.7 and EP.22 exclude any floating wing mass at those omitted normals in the limit. For the canonical cap, TF3 additionally puts any tilted central facet entirely over J, so it has no charged wing atom. This argument makes no analogous identification for the nonconvex niche graph.

### 6a. The possible negative-pressure side is localized further

The [TF4 global top-insertion theorem](gate1-spatial-tilted-facet-pinning.md) says that every maximizer's top face meets J. For a MID2-canonical height-one maximizer, the horizontal-middle case therefore has \(A(j_-)=A(j_+)=1\); in the tilted case its higher endpoint has height one.

**Corollary EP3.** A side whose J endpoint has height one has **strictly positive pressure**. Hence both quarter exposure equalities hold in the horizontal-middle global-maximizer case. In the tilted case, any nonpositive pressure is confined to the side of the lower middle endpoint; that side has zero end-face height and \(q_{\rm low}\le1/2\).

**Proof.** Suppose \(A(j_+)=1\), so \(q_+\ge1\). If \(C_R\le0\), then \(q_-\ge3q_+\). EP1 would force
\[
e_L=C_L=(3q_--q_+)/4\ge2q_+\ge2,
\]
contradicting \(e_L\le1\). Thus \(C_R>0\); reflection handles the other endpoint. If the lower side has \(C_L\le0\), then \(q_+\ge3q_-\), and
\[
1\ge e_R=C_R=(3q_+-q_-)/4\ge2q_-.
\]
So \(q_-\le1/2\), while EP1 gives \(e_L=0\). The reflected case is identical. If the pressure is strictly negative then \(q_{\rm low}<1/2\). \(\square\)

This corollary uses the endpoint law and the height bound, **not** a new numerical width exclusion. It does not exclude the remaining tilted alternative or prove the value in the horizontal case.

## 7. What this changes, and the remaining Gate 1 obstruction

The old unconditional endpoint equations have been replaced by a proved **global complementarity law**, and horizontal erosion gives the exact defect budget for the selected finite exposure limits. This closes a specific moving-window variational dependency. The [TF4 top-insertion map](gate1-spatial-tilted-facet-pinning.md) also proves that a canonical tilted maximizer reaches height one at its higher J endpoint.

The sharp value is still missing. A completion must establish the remaining global geometric payment, for example by controlling the negative-pressure defect in EP.3 on the low side specified by EP3 and obtaining a sharp visibility/velocity/value estimate from the full niche. Even when both pressures are nonnegative and both limiting measures match, that equality does **not** imply \(|p(t)|,|q(t)|\le1\), unit source curvature, convergence of niche zero sets, or the Romik contact chart. The possible tilted central facet with two pinned corners remains. No exact cap with \(\mathcal P>M/2\) was produced.

No unrelated width-bound refinement, numerical screen, Lean source, or CI change is included. **Gate 1 is not passed; Gate 2 remains blocked.**
