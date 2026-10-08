# An exact hand certificate theorem for four rational hallways

**Main result.** In O'Keefe's four \((3,4,5)\)-hallway relaxation, the area of the entire enlarged envelope over **any** eight-dimensional offset box differs from the area at the box midpoint by at most a *linear expression with exact rational coefficients*. In particular, if every offset interval has length at most \(\delta\),
\[
\boxed{0\le |C(E)|-|C(\operatorname{mid}E)|\le \frac{168}{5}\delta.}
\tag{BH.1}
\]
This is a short pen-and-paper proof that turns the measured canonical-offset speedup into a **rigorous midpoint-sampling certificate rule**, rather than another floating-point performance observation. It needs no curvature bound, candidate neighborhood, optimization of separate cap functionals, or estimated polygon-contact topology. A companion corollary shows that every **strict** upper bound above the four-hallway optimum has a finite exactly checkable midpoint certificate. It does **not** establish a new bound below the published \(353/200\), or Romik's sharp \(M\). Labels BH are local.

The geometry is self-contained, except that the optional completeness and computability corollaries cite the previously written actual-body connectedification GC and finite-to-continuum FR. Those longer proofs remain self-reviewed. All four-hallway data and the outer-window normalization are credited to O'Keefe's paper; the root-domain improvement uses our canonical-support CP1 theorem. We have not run a large optimizer, Lean, CI, or an external certificate.

## 1. Four hallway data and the exact box union

Fix \(B=[0,5]\times[0,1]\). The four upper-coordinate pairs are
\[
\begin{array}{ll}
f_1=(4x+3y)/5,&g_1=(-3x+4y)/5,\\
f_2=(3x+4y)/5,&g_2=(-4x+3y)/5,\\
f_3=(4x-3y+3)/5,&g_3=(-3x-4y+4)/5,\\
f_4=(3x-4y+4)/5,&g_4=(-4x-3y+3)/5.
\end{array}
\tag{BH.2}
\]
Every pair has orthonormal gradients, including the two reflected pairs.

With real offsets \((a_j,b_j)\), write the closed \(L\)-hallway as
\[
X_j(a_j,b_j)=
\{f_j\le a_j+1,\ g_j\le b_j+1,\
(f_j\ge a_j\ \text{or}\ g_j\ge b_j)\}.
\tag{BH.3}
\]
For an eight-dimensional offset box \(E=\prod_j([a_j^-,a_j^+]\times[b_j^-,b_j^+])\), its **enlarged whole-hallway enclosure** is
\[
\widehat X_j(E)=\bigcup_{(a_j,b_j)\in E_j}X_j(a_j,b_j)
=\{f_j\le a_j^++1,\ g_j\le b_j^++1,\
(f_j\ge a_j^-\ \text{or}\ g_j\ge b_j^-)\}.
\tag{BH.4}
\]
The last equality is elementary: for the first-arm alternative choose the lower feasible \(a_j\) and upper feasible \(b_j\), and analogously for the other arm. It is the same union identity used in the external exact checker.

Define
\[
C(E)=B\cap\bigcap_{j=1}^4\widehat X_j(E),
\qquad
C(u)=B\cap\bigcap_{j=1}^4 X_j(u_j).
\]
The midpoint \(m=\operatorname{mid}E\) belongs to \(E\), so \(C(m)\subseteq C(E)\).

## 2. The only area an offset box can add lies in eight pairs of thin strips

For one hallway, set \(m_j=(a_0,b_0)\), \(\alpha=(a_j^+-a_j^-)/2\), \(\beta=(b_j^+-b_j^-)/2\). If a point \(z\) is in \(\widehat X_j(E)\) but **not** in \(X_j(m_j)\), one of four failures must occur:

- its first outer bound fails, forcing \(a_0+1<f_j(z)\le a_0+1+\alpha\);
- its second outer bound fails, forcing \(b_0+1<g_j(z)\le b_0+1+\beta\);
- both midpoint outer bounds hold, but its first inner safe alternative fails while the enlarged first alternative succeeds, forcing \(a_0-\alpha\le f_j(z)<a_0\);
- or the analogous second inner-wall strip \(b_0-\beta\le g_j(z)<b_0\).

Thus **the newly permitted region** is contained in two disjoint-or-overlapping \(f_j\)-strips each of coordinate thickness \(\alpha\), and two \(g_j\)-strips each of thickness \(\beta\). No assumption about connected components is made. This is the entire effect of enlarging a hallway's two translation offsets.

**Elementary strip-area lemma.** If \(F(x,y)=c+p x+q y\) with \(p^2+q^2=1\), then for any real \(v\) and \(t\ge0\),
\[
\boxed{|\{(x,y)\in B:v\le F(x,y)\le v+t\}|
\le t(5|q|+|p|).}
\tag{BH.5}
\]
Indeed the coordinate transformation \((F,G)\), with \(G=-qx+py\), is an isometry and preserves area. The projection of \(B\) onto the \(G\)-axis has length \(5|q|+|p|\). Slice the indicated region at fixed \(G\); each slice has \(F\)-length at most \(t\). Fubini proves the bound.

For \(j=1,3\), one \(f_j\)-strip has area at most \((19/5)t\) and one \(g_j\)-strip at most \((23/5)t\). For \(j=2,4\), the coefficients are reversed. The sum of the two \(f_j\) and two \(g_j\) strip areas is therefore at most
\[
\begin{cases}
\frac{19}{5}(a_j^+-a_j^-)+\frac{23}{5}(b_j^+-b_j^-)&j=1,3,\\[2pt]
\frac{23}{5}(a_j^+-a_j^-)+\frac{19}{5}(b_j^+-b_j^-)&j=2,4.
\end{cases}
\tag{BH.6}
\]

## 3. Uniform exact box-enclosure theorem

For a box \(E\), list its eight coordinate widths in the source's order as \(\delta_1,\dots,\delta_8\).

**Theorem BH1 (hand-certified midpoint upper enclosure).**
\[
\boxed{
0\le|C(E)|-|C(m)|
\le\frac{19}{5}(\delta_1+\delta_4+\delta_5+\delta_8)
+\frac{23}{5}(\delta_2+\delta_3+\delta_6+\delta_7).
}
\tag{BH.7}
\]
In particular with \(\delta=\max_i\delta_i\),
\[
\boxed{|C(E)|\le|C(m)|+\frac{168}{5}\delta.}
\tag{BH.8}
\]

**Proof.** If a point belongs to \(C(E)\setminus C(m)\), it belongs to the enlarged hallway for every \(j\), but fails at least one of the corresponding four midpoint hallway constraints. Hence
\[
C(E)\setminus C(m)
\subseteq\bigcup_{j=1}^4
\bigl[B\cap(\widehat X_j(E)\setminus X_j(m_j))\bigr].
\]
The strip classification and (BH.5) bound the area of the \(j\)-th difference by (BH.6). Add the four upper bounds using subadditivity of planar measure. Four coefficients are \(19/5\), the other four \(23/5\), giving \(4(19+23)/5=168/5\). QED.

**There is no numerical-estimation step here.** The bound is a uniform exact inequality for **every real offset box**, including boxes containing degenerate touching, empty, or disconnected hallway intersections.

## 4. Fully checkable *finite-center* upper-bound certificates

Let \(G\) denote O'Keefe's maximum over **largest connected-component area** for these four hallways. CP1 proves that replacing all arbitrary placements by their normalized, support-tight component placements preserves \(G\). Their eight offsets belong to the explicit smaller canonical box
\[
\mathcal B_{\rm CP}=
[-1,18/5]\times[-1,-1/5]\times[-1,14/5]\times[-1,-2/5]
\times[-2/5,18/5]\times[-1,-1/5]\times[-1/5,14/5]\times[-1,-2/5].
\tag{BH.9}
\]

**Corollary BH2 (hand-checkable rational sampling certificate).**
Partition \(\mathcal B_{\rm CP}\) into finitely many **rational** offset boxes \(E_i\), and let \(m_i\) be each midpoint. Define the explicit rational penalty \(\mathcal R(E_i)\) as the right side of (BH.7). If
\[
\boxed{|C(m_i)|+\mathcal R(E_i)\le T
\quad\text{for every box }E_i,}
\tag{BH.10}
\]
then \(G\le T\), for every real placement of the four hallways.

**Proof.** A connected component of arbitrary original placements can be translated and tightened by CP1 to a no-smaller competitor at some \(u\in\mathcal B_{\rm CP}\). It belongs to one of the boxes \(E_i\), so its area is at most \(|C(u)|\le|C(E_i)|\). Apply BH1 and (BH.10). Taking the supremum proves the claim. QED.

At every rational midpoint, \(C(m_i)\) decomposes into at most sixteen rational convex polygons with disjoint interiors. The **total** polygonal area \(|C(m_i)|\) is exactly rational by the shoelace formula. No test of connected components or floating-point arithmetic is needed for the certificate rule (BH.10). It may be computationally inefficient compared with the paper's component-aware \(\Gamma(E)\), but it is a simpler *fully rigorous* alternative for suitable boxes.

## 5. Why such a finite proof is guaranteed for every *strict* threshold

The external checker uses the maximal-component area of inflated boxes, not necessarily the total area. Our previously proved horizontal gap-compression theorem GC4 shows something stronger **for a single actual four-hallway intersection**: its vertical sections are intervals or empty; collapsing all empty horizontal gaps, then filling vertical sections, produces a connected finite-hallway competitor with the **same total area**, possibly different horizontal offsets. The support-depth inequality GC1 preserves every one of the four hallway orientations. Therefore
\[
\boxed{
\sup_{u\in\mathbb R^8}|C(u)|
=\sup_{u\in\mathbb R^8}\lambda^*(C(u))=G,
}
\tag{BH.11}
\]
where the suprema are taken with the usual harmless horizontal translations/normalization into the \(5\times1\) window. The distinction is important: BH.11 compares **global suprema**, and does not assert that a disconnected \(C(u)\) is connected or has the same area as its own largest component.

**Corollary BH3 (completeness of strict finite-center certification).** For every **rational** threshold \(T>G\), there exists a **finite, exactly checkable rational midpoint certificate** of the form BH.10. For arbitrary real \(T>G\), choose a rational threshold strictly between \(G\) and \(T\). An exhaustive dyadic subdivision/checking procedure therefore terminates whenever the proposed upper bound is strictly greater than the actual four-angle relaxation optimum.

**Proof.** Every midpoint placement has \(|C(m)|\le G\) by BH.11. Choose a positive rational mesh width
\[
0<\delta<\frac5{168}(T-G).
\]
Subdivide each coordinate of the compact rational box BH.9 into finitely many rational intervals of length at most \(\delta\). Then \(\mathcal R(E_i)\le168\delta/5<T-G\) for each box, so BH.10 holds. No knowledge of \(G\) is needed to *run* the exhaustive algorithm: \(T>G\) ensures that at some finite subdivision the exact rational tests will all pass. QED.

This is a new rigorous **completeness and termination statement for strict upper bounds**, not just a convergence impression from a benchmark. For \(T<G\) no valid certificate can exist, and at \(T=G\) termination is not guaranteed. The theoretical number of center boxes can be enormous; practical exact whole-box geometry and CP's cheap support pruning remain essential.

## 6. A broader mathematical consequence: computability of the full-turn value

Here is a separate consequence of our pre-existing [FR](full-turn-compact-finite-reduction.md) and [D1](direction-1-critical-face-reduction.md) finite-mesh results, now interpreted as a **hand proof of effective computability**, not merely as an assertion that a floating grid converges.

Let \(A_F\) be the full-turn optimal area, and \(A_n\) FR's exact full-turn area relaxation at its rational angular mesh with the fixed additional \(45^\circ\) angles. FR2 gives
\[
\frac{A_n}{(1+6/n)^2}\le A_F\le A_n\le2\sqrt2-1.
\tag{BH.12}
\]
For each fixed even \(n\), the finite hallway intersections can be cut into finitely many arrangements of fixed line directions. On each parameter cell, all polygon vertices depend **affinely** on the offsets, and polygon area is a quadratic with coefficients in the explicitly ordered algebraic field \(\mathbb Q(\sqrt2)\). The parameter cells are compact polyhedra defined by finitely many linear inequalities over the same field. A quadratic polynomial on a compact polytope over \(\mathbb Q(\sqrt2)\) has a maximizer with coordinates in \(\mathbb Q(\sqrt2)\): descend to a boundary face if the maximum is attained there; otherwise solve the tangential linear stationary equations over that field. If the stationary system has a kernel, move within its affine stationary set to a lower-dimensional face; alternatively, use the density of field-valued points in the nonempty relative interior of that stationary affine set. The value is constant along stationary null directions. This gives a finite exact algorithm for each \(A_n\); in particular
\[
\boxed{A_n\in\mathbb Q(\sqrt2)\quad\text{and can be found exactly in finitely many steps}.}
\tag{BH.13}
\]
Here GC4 permits optimizing the **total** finite-envelope area without component bookkeeping; it does not assert the original finite envelope is connected.

The bracket (BH.12) has explicit width
\[
A_n-\frac{A_n}{(1+6/n)^2}
\le(2\sqrt2-1)\left[1-(1+6/n)^{-2}\right]
<\frac{24}{n}.
\tag{BH.14}
\]
Thus given any rational \(\varepsilon>0\), choose an even \(n>24/\varepsilon\), compute \(A_n\) in exact algebraic arithmetic, and output the certified interval
\[
\boxed{\left[\frac{A_n}{(1+6/n)^2},\,A_n\right]}
\]
of width less than \(\varepsilon\), containing \(A_F\).

**Corollary BH4.** The unrestricted **full conventional two-turn** optimal area \(A_F\) is a *computable real number* with an explicit certified approximation modulus, conditional only on the already written GC/FR geometric reductions. This says nothing about a practical runtime, proves neither \(A_F=M\) nor its negation, and does not automatically extend to unrestricted partial turns.

## 7. Scope and execution boundary

The new self-contained hand theorem is BH1; BH2 depends additionally on our earlier CP1 canonical-support normalization; BH3 on GC4 connectedification; and BH4 on the FR2 full-angle shrink and D1 finite critical-face classification. These historical components are **self-reviewed**, not independently refereed or Lean-checked. No computer calculation is needed to establish the analytic strip bound BH1; a separate small rational regression checks arithmetic and sampled polygons only.

**What this closes:** a precise, rigorous answer to whether the faster search can become a proof *method*: rational samples plus the explicit BH penalty can certify global four-angle area bounds, and any strict threshold above the true four-angle optimum is certifiable in finitely many steps. The full-turn value can in principle be approximated by a finite exact procedure with an explicit rate.

**What this does not close:** Romik's sharp inequality \(A_F\le M\), the absolute value of \(G\), the larger-angle reach of arbitrary partial turns just above \(M\), a practical search bound or a new certified numeric upper value below \(353/200\). Do not convert a fast floating benchmark into a numerical area theorem without an exact certificate.


## 8. Worked exact eight-dimensional certificate below \(7/4\)

The main theorem has a concrete application directly around the high-area *finite-hallway* configuration reported in O'Keefe's paper, even though the published global upper bound remains \(353/200\). This is not a near-Romik shape claim; it is a **neighborhood bound in the eight independent placement parameters**.

In the \(5\times1\) window, after the harmless horizontal translation \(x\mapsto x+3\), take the rational midpoint offsets
\[
m=\bigl(\tfrac{1263}{500},-\tfrac{543}{400},
\tfrac{9661}{5000},-\tfrac{18603}{10000},
\tfrac{1263}{500},-\tfrac{543}{400},
\tfrac{9661}{5000},-\tfrac{18603}{10000}\bigr).
\tag{BH.15}
\]
These are exactly O'Keefe's original four-angle example with the right/left offset pairs equal, translated into our common window. At this midpoint, the four-hallway intersection decomposes into seven nonempty rational convex polygon pieces with disjoint interiors, whose shoelace areas are
\[
\begin{array}{c|l}
\text{piece}&\text{exact area}\\\hline
0&8922371/10500000\\
1,2&41795297/4800000000\quad\text{each}\\
3&1885129/75000000\\
4,5&4616080201/33600000000\quad\text{each}\\
6&379449901/672000000
\end{array}
\]
Their **exact sum**, independently reconstructed by rational clipping, agrees with the source:
\[
\boxed{|C(m)|=\frac{29\,092\,957\,301}{16\,800\,000\,000}.}
\tag{BH.16}
\]
The polygon decomposition can be reproduced with the separate standard-library rational checker; it is a finite exact-arithmetic input, not a continuum optimization claim.

Let
\[
E_*=\prod_{i=1}^8[m_i-\tfrac1{4000},\,m_i+\tfrac1{4000}].
\]
Every coordinate interval has width \(\delta=1/2000\). The **hand theorem BH1** gives
\[
\begin{aligned}
|C(E_*)|
&\le \frac{29\,092\,957\,301}{16\,800\,000\,000}
 +\frac{168}{5}\cdot\frac1{2000}\\
&=\boxed{\frac{29\,375\,197\,301}{16\,800\,000\,000}}
=\frac74-\frac{24\,802\,699}{16\,800\,000\,000}
<\frac74.
\end{aligned}
\tag{BH.17}
\]
Thus **every one of the uncountably many eight-offset placements in this entire explicit rational box** has **total surviving area**, and hence largest connected-component area, strictly below \(7/4\). No subdivision or connected-component graph calculation is needed for this particular neighborhood. This is a genuine short exact box certificate at a threshold **below 1.765 on one local region**, not a new global bound.

## 9. Exact regression and verification limits

The independent [rational regression](computer-assisted/check_box_area_modulus.py) ran 32 prescribed boxes, checking their exact enlarged-versus-midpoint polygon areas, individual-width penalty, and uniform bound: **99 rational assertions passed, 28 strict enlargements**, including the exact seven-polygon witness and the complete rational box from BH.15--BH.17. All polygon coordinates and shoelace areas used Python fractions.Fraction. Under an external five-second cap, it used approximately **0.0686 seconds** internally. Executed source SHA-256:
2d1f37c2e1b88a0dd959ae46f6f6e118a7eb81d0854b9c11b39b200e93a4be3d, Git blob 4a653732d4b9e45c19cf5489fa96ba1d1754ce4a; the committed source matches the executed bytes. Its complete [record](computer-assisted/box-area-modulus-checks.json) explicitly says finite tests **do not** verify the continuum theorem or prove the global conjectured value \(M\).

The rational seven-polygon decomposition in BH.16 was independently computed with the same elementary clipping primitives after shifting the source's exact rational offsets. This checks a **single prescribed exact configuration**, not a 436-million-leaf global certificate. The universal area-overcount estimate (BH.7) and rational-space completeness corollary are hand proofs and do not rest on these finite tests.

**Outcome:** a clean analytic box-area bound, an explicit \(<7/4\) certified rational neighborhood of a hard finite witness, and an exact-in-principle way to certify every strict upper threshold for a fixed finite relaxation. None is a proof that the four-angle global optimum is \(<7/4\), and none solves Romik's sharp full-turn or partial-turn frontiers.
