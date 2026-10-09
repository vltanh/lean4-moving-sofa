# Gate 1.2: an exact **whole-angle polygonal niche oracle** — finite outer-contact, ray-tangency and physical-corner charts

**October 9, 2026 · Status: globally quantified calculation theorem, NOT the sharp Gate 1.2 area inequality.** This note proves that for any finite **rational convex polygon** in the unit incoming strip, the complete lower and upper inner-wall swept regions, their ordinary clipped union, any empty-fiber correction, and the true full-turn canonical envelope area can all be represented by **finitely many explicitly described algebraic curves** and evaluated using **elementary integrals**. No angular sampling, unimodality, curvature bound or Romik-contact chart is used. The result is a direct prerequisite for any exact finite-facet certificate of [G1.5 / PG.12](SHARP-OPTIMALITY-EXECUTION-PLAN.md).

The theorem complements [PG1](gate1-facet-audit-and-feasible-polygon-density.md): the latter says **actual finite-polygonal full-turn hulls are area-value dense**, while the present statement makes **the entire continuum-angle carved area of any one such hull exactly calculable**. The latter is a **pointwise hull computation**, not a *uniform inequality over all polygon vertex configurations and unbounded facet counts*. **Gate 1.2 remains ACTIVE and UNPROVED.**

## 1. Rational support sectors: at most \(2N+1\) pieces

Let \(K=\operatorname{conv}\{P_1,\ldots,P_N\}\subset\mathbb R\times[0,1]\) be a nondegenerate convex polygon with rational vertices \(P_i=(a_i,b_i)\). Set \(L=\pi/2\), \(c=\cos t>0\), \(s=\sin t>0\), and let
\[
u_t=(c,s),\qquad v_t=(-s,c).
\]
The outer support values are
\[
f(t)=\max_i(a_i c+b_i s),\qquad
g(t)=\max_j(-a_j s+b_j c).
\tag{EO.1}
\]
Each vertex of a convex polygon maximizes a linear functional on one connected normal cone. As each normal \(u_t,v_t\) rotates through a quarter-circle, it changes its maximizing vertex at most \(N\) times. The union of these finitely many changes partitions \([0,L]\) into at most \(2N+1\) intervals \(J\), each of which has fixed maximizing vertices \(P_i,P_j\) in its interior. Support ties at the finitely many endpoints cause no ambiguity in the numerical support value.

Every switching normal is perpendicular to an edge difference with rational coordinates, so its unit components \(c,s\) are **real algebraic**, found by normalizing the corresponding rational vector. In particular its half-angle tangent \(q=\tan(t/2)\) is algebraic.

## 2. Every maximal physical ray roof has one of **three** types of source angle

On a fixed support sector \(J\) whose first and second outer support vertices are \(P_i=(a_i,b_i)\), \(P_j=(a_j,b_j)\), respectively, the two **actual attached inner-ray roofs** at horizontal coordinate \(x\) are
\[
\boxed{
\begin{aligned}
R_i(t,x)&=b_i+(a_i-x)\cot t-\csc t,\\
D_j(t,x)&=b_j+(x-a_j)\tan t-\sec t,\\
q_{ij}(t,x)&=\min\{R_i(t,x),D_j(t,x)\}.
\end{aligned}}\tag{EO.2}
\]
Here \(q_{ij}\) is **not** the half-angle parameter \(q=\tan(t/2)\). It is the complete *physical two-wall* forbidden roof.

**Theorem EO1 (finite contact-parameter characterization).** For each fixed real \(x\), the nonnegative *complete* full-turn inner-ray roof
\[
n_K(x)=\max\{0,\sup_{0<t<L}q_{K,t}(x)\}
\]
is the **maximum of the finitely many actual q-values** at the following source parameters across every support sector J:

1. its two angular support-switch endpoints, whenever they are interior to \((0,L)\);
2. each source parameter satisfying the **first inner-wall stationary equation**
   \(\cos t=a_i-x\) inside J;
3. each source parameter satisfying the **second inner-wall stationary equation**
   \(\sin t=x-a_j\) inside J;
4. every **physical sharp-inner-corner tie** with \(x=\xi_{ij}(t)\) inside J, where
   \[
   \boxed{\begin{aligned}
   \xi_{ij}(t)&=a_i c^2+a_j s^2+(b_i-b_j)sc-c+s,\\
   \eta_{ij}(t)&=(a_i-a_j)sc+b_i s^2+b_j c^2-s-c.
   \end{aligned}}\tag{EO.3}
   \]

There are at most **eight candidate parameters per support sector**, and at most \(8(2N+1)\) over all sectors, excluding duplicates and the zero baseline. This candidate count is independent of x and makes **no assertion** that the same candidate or contact chart persists as x moves.

**Proof.** On a support sector, each of the two functions \(R_i,D_j\) is differentiable in t, and
\[
\boxed{
\partial_tR_i=\frac{x-a_i+\cos t}{\sin^2t},
\qquad
\partial_tD_j=\frac{x-a_j-\sin t}{\cos^2t}.
}\tag{EO.4}
\]
If \(q_{ij}(t,x)\) attains an interior positive maximum at a parameter with \(R_i<D_j\), its derivative is \(\partial_t R_i=0\), giving case 2. When \(D_j<R_i\), case 3 applies. If \(D_j=R_i\), their common value is attained at the **actual physical moving corner** \((\xi_{ij},\eta_{ij})\), giving case 4. At an angular support switch the value of h, hence of the roof, is continuous; those endpoints are case 1.

The two stationarity equations have **at most one** solution each on the open quarter since cos decreases and sin increases. The tie equation has at most four distinct solutions by the polynomial calculation below. The angular limits \(t\downarrow0,t\uparrow L\) cannot supply a strictly positive missing maximum: at the start the second roof has limiting upper bound \(h_K(e_y)-1\le0\), and at the end the first roof has the same limiting upper bound. Thus every positive global maximum is attained at one of the listed *interior* parameters, and adjoining zero accounts for an empty positive niche. The maximum of actual values at that finite list is the exact complete all-angle supremum. \(\square\)

### Explicit **quartic**, valid even for reverse or multiply exposed corners

Put \(z=\tan(t/2)\in(0,1)\), \(c=(1-z^2)/(1+z^2)\), \(s=2z/(1+z^2)\). The tie identity has the precise algebraic form
\[
R_i-D_j=\frac{\xi_{ij}(t)-x}{sc}.
\tag{EO.5}
\]
After clearing denominators, the equation \(\xi_{ij}(t)=x\) is
\[
\boxed{
\begin{aligned}
0={}&(a_i-x-1)
+2(b_i-b_j+1)z\\
&+(-2a_i+4a_j-2x)z^2
+2(b_j-b_i+1)z^3\\
&+(a_i-x+1)z^4.
\end{aligned}}\tag{EO.6}
\]
The quartic is **never the zero polynomial**: its constant and degree-four coefficients differ by exactly two. Thus there are at most four real roots in \(0<z<1\), whether the corner abscissa is monotone, folded, or visits x repeatedly.

At a stationary first-wall candidate, the roof value on the active first-wall branch is the **unit-circle tangent**
\[
\boxed{R_i=b_i-\sin t
=b_i-\sqrt{1-(a_i-x)^2}.}\tag{EO.7}
\]
At a stationary second-wall candidate the corresponding active value is
\[
\boxed{D_j=b_j-\cos t
=b_j-\sqrt{1-(x-a_j)^2}.}\tag{EO.8}
\]
If the stationary wall is *not* the smaller one at that parameter, it is not an active maximizer of the complete two-wall roof. A safe implementation either checks the inequality between both walls or evaluates their **actual minimum**, rather than incorrectly treating every unit-circle tangent as active. At a tie, the actual value is \(\eta_{ij}(t)\). At a fixed support-switch endpoint, it is the min of **two affine functions in x**. These are exactly the graph types in the theorem.

## 3. True whole-angle **ordinary** area is a finite elementary integral, not a sampled envelope

Write the actual convex polygon's lower/upper piecewise-affine fiber endpoints as \(B_K(x),A_K(x)\) on its projection \(I=[l,r]\). Apply EO1 to K and to its vertical reflection \(\rho K=\{(x,1-y):(x,y)\in K\}\); denote their two complete nonnegative positive niche roofs \(n_-(x)\), \(n_+(x)=n_{\rho K}(x)\).

For **any** rational polygon K, including one which is *not* a feasible full-turn hull, the true full canonical two-turn envelope has ordinary fibers
\[
\boxed{
\ell_K(x)=\min\{A_K(x),1-n_+(x)\}
-\max\{B_K(x),n_-(x)\},
\qquad
|E_{\rm full}(K)|=\int_I(\ell_K(x))_+dx.
}\tag{EO.9}
\]
The positive part is **essential** for an incompatible polygon with empty central fibers. No full-niche subtraction without clipping or empty-fiber correction is used.

**Theorem EO2 (finite exact polygonal full-turn area).** For every finite rational convex polygon K, the four graph functions \(A_K,B_K,n_-,n_+\) are **piecewise semialgebraic over the algebraic real numbers**, with a finite effective decomposition into candidate graph branches of only the following kinds:

- affine lines from the polygon outer boundary and from stationary **source-sector endpoints**;
- unit-circle arcs from EO.7–EO.8;
- rationally trigonometric moving-corner curves \((x,y)=(\xi_{ij}(t),\eta_{ij}(t))\).

Their finite arrangement, including every contact tie, inner/outer boundary switch, fold, and pinch, can be partitioned into **finitely many disjoint x-intervals with algebraic endpoints**, on each of which the active lower and upper fiber graphs in EO.9 are fixed. Every such interval has a finite elementary area primitive. Consequently the *exact ordinary area* \(|E_{\rm full}(K)|\), the exact **signed** fiber area, and the two **actual K-clipped ordinary niche areas** are explicitly computable by finitely many arithmetic/algebraic root operations and elementary trigonometric antiderivatives. They belong to the class of finite sums of real algebraic numbers and real algebraic multiples of \(\arctan\) of real algebraic arguments, allowing rational multiples of \(\pi\).

**Proof.** For rational K, the support phase boundaries have algebraic direction cosines and sines. EO.6 describes each possible corner contact at fixed x by a polynomial with rational coefficients; EO.4 gives each stationary angle by algebraic relations. Graph membership, sector bounds, positive part, comparisons and switching inequalities are all first-order semialgebraic formulas in variables \((x,y,c,s)\) satisfying \(c^2+s^2=1,\ c,s\ge0\). Real-algebraic elimination and one-dimensional semialgebraic cell decomposition therefore give a finite exact partition into algebraic-endpoint intervals with fixed active graph branches. This is **not** a finite sampling assertion; it is an exact finite arrangement of the entire real angular continuum.

For each affine branch, integration is elementary polynomial arithmetic. For each unit-circle branch, integrate
\(b_i-\sqrt{1-(a_i-x)^2}\) or
\(b_j-\sqrt{1-(x-a_j)^2}\), producing algebraic endpoint evaluations and \(\arcsin\) of algebraic arguments; each arcsin is an arctan of an algebraic argument, possibly with a rational multiple of \(\pi\). For each corner branch, break further at its finitely many x-turning points and integrate with the actual angle t as parameter:
\[
\boxed{\int y\,dx
=\int_{t_{\rm in}}^{t_{\rm out}}
\eta_{ij}(t)\,\xi_{ij}'(t)\,dt.}\tag{EO.10}
\]
By EO.3 both \(\eta_{ij}\) and \(\xi_{ij}'\) are finite trigonometric polynomials in t (with frequencies at most 2), so their product has frequencies at most 4. Its antiderivative is a finite trigonometric polynomial plus a constant multiple of t. The interval endpoint normal pairs \((c,s)\) are algebraic, and \(t=2\arctan(s/(1+c))\), with the usual elementary boundary convention. Hence these primitive values are algebraic plus algebraic multiples of arctan of algebraic arguments. The positive-part and lower/upper clipping in EO.9 choose among those same branches, introducing no new types. Summing finitely many cell integrals proves the claim. \(\square\)

**Exact sanity check at a genuine full-turn sofa hull.** For the rational unit square \(K=[-1/2,1/2]\times[0,1]\), its moving corner is globally active in the reverse-corner regime \(p=1-\sin t>0>q=\cos t-1\), with
\[
\xi(t)=\frac12\cos 2t-\cos t+\sin t,\qquad
\eta(t)=\sin t\cos t+1-\sin t-\cos t.
\]
Its horizontal corner coordinate increases from \(-1/2\) to \(1/2\). Its full lower niche area therefore equals
\[
\int_0^{\pi/2}\eta(t)\xi'(t)\,dt
=\boxed{2-\frac{5\pi}{8}},
\]
and the upper niche is its vertical reflection, disjoint from the lower. Its actual compact connected full-turn survivor retains all four square vertices, has nonempty interval fibers and **ordinary** area
\[
\boxed{|E_{\rm full}(K)|=1-2\left(2-\frac{5\pi}{8}\right)
=\frac{5\pi}{4}-3.}\tag{EO.11}
\]
This independent symbolic test exercises the complete reverse-moving-corner branch, not only Romik's reference middle chart.

## 4. Strengthening PG1: **rational feasible polygonal** full-turn sofas are area-value dense

**Theorem EO3 (countable rational-facet coverage).** Let \(V_F\) be the supremum of ordinary areas of all connected full-conventional-two-turn sofas in a unit incoming strip. Then the same value is attained as a **supremum over actual connected two-turn sofas which are finite unions of closed rectangles with rational vertices and finitely many rational vertical connectors**. In particular their **actual convex hulls** are convex polygons with rational vertices.

**Proof.** Start with any genuine connected full-turn S and its compact canonical saturation E. Its vertical interval endpoints L(x),U(x) are continuous on the interior of its horizontal projection by the roof-continuity argument of [PG1](gate1-facet-audit-and-feasible-polygon-density.md). All area of E is captured by its interior-positive vertical fibers: the two boundary graphs and the two projection endpoint lines have planar measure zero. Uniform continuity on compact interior subintervals permits approximation from inside by **finite disjoint rational x-intervals and closed rational y-interval rectangles** \(R_i\subseteq E\) whose total area exceeds \(|E|-\varepsilon\). Choose each y-interval strictly between the uniform minimum of U and maximum of L on its x-interval, so its rational endpoints exist and the rectangle is genuinely contained in E. Discarding very thin x-cells around pinches and extreme projection endpoints costs arbitrarily little ordinary area.

The finite union Q of these rational rectangles fits **all** original complete supporting hallway positions, by containment in E. Collapse its finitely many rational horizontal projection gaps with the monotone 1-Lipschitz map \(T(x)=\int_l^x\mathbf1_{\operatorname{proj}_xQ}(z)\,dz\). On each occupied rectangle, this is a rational translation; its image has rational coordinates and unchanged ordinary area. By the universal [GC1](horizontal-gap-compression.md) support-depth inequality every previously safe inner-wall constraint and each incoming/outgoing strip remains safe after this contraction. Finally fill the vertical fiber only at the finitely many newly shared rational interface abscissae. Each added connector is a rational vertical segment; the area is unchanged and every full-turn hallway's vertical sections are intervals, so the filled body remains feasible. The resulting compact body has interval horizontal projection and interval fibers, hence is connected.

It is the finite union of rational rectangles and rational joining segments, with area arbitrarily close to \(|E|\ge|S|\) from below and convex hull the convex polygon generated by its finitely many rational corners. The zero-area case is immediate. Thus rational feasible polygonal hulls carry the **entire** full-turn supremum. \(\square\)

## 5. Exact limitation — the **sharp finite-facet global charge is STILL OPEN**

For an actual genuine polygonal full-turn hull, [PG1](gate1-facet-audit-and-feasible-polygon-density.md) also identifies the K-clipped one-angle cuts as oblique triangles based on exposed lower/upper facets. Theorem EO2 now supplies a complete *finite exact calculation* of the **entire union over angles** on each facet, with no additive overcount. EO3 says the rational finite-hull domain already carries the exact global supremum.

The remaining Gate 1.2 acceptance condition is therefore the following **one quantified inequality** over *all finite rational, actually feasible polygonal hulls*, with no bound on their number of vertices:
\[
\boxed{
\sum_{F\in\mathcal F_-(K)}\!\int_{I_F}\!n_{F,-}(x)\,dx
+\sum_{F\in\mathcal F_+(K)}\!\int_{I_F}\!n_{F,+}(x)\,dx
\ge |K|-M.
}\tag{EO.12 — UNPROVED}
\]
Each left-side integral can now be evaluated *exactly for a fixed input polygon* using EO1–EO2. **Nothing here supplies a common lower bound on the integral for every polygon**; enumerating them, or optimizing a fixed maximum vertex count, is not a finite proof of EO.12. The cubic Romik clipping witness, counterexamples to general signed concavity, and genuine opposite-end-face shapes remain valid adversarial controls. No above-M feasible hull, new global bound or sharp proof is claimed.

A **pass** of Gate 1.2 will require either an exact uniform inequality for all rational actual-feasible input polygons, or a mathematically justified area-value bound on the whole full-turn class. A pointwise oracle is an input to that proof, not its conclusion. Gate 2's original partial angles would remain unresolved after Gate 1.2 passed.

**Diagnostics:** EO.4–EO.6 were independently checked by symbolic trigonometric algebra. A scratch candidate enumerator comparing all switch/station/corner source parameters with full angular grids passed at 437 horizontal sections across 19 polygonal inputs (including oblique, opposite-end-face and random hulls). These finite screens are *not* substituted for the calculus, semialgebraic decomposition or real-angle proof. No CI or Lean/Lake was run.
