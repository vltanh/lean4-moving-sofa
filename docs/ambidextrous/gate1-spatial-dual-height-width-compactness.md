# Gate 1 spatial one-cap dual, height saturation, and compactness

**Original reduction: October 9, 2026. Sharp value completed: October 10, 2026.** The [Gate 1 closure](gate1-sharp-full-turn-closure.md) now proves SD.3 and the resulting sharp complete-turn theorem. This note supplies the original whole-domain spatial partition, height extrusion, width coercivity, continuity, and attainment arguments used by that proof. External mathematical review and Lean verification remain outstanding.

**Results proved here:** (i) spatial loss assignment bounds the joint full-turn functional directly; (ii) vertical Minkowski extrusion never decreases the cap score; (iii) every competitive cap has \(8/5<W<6\); (iv) the scalar maximum is attained, including nonsmooth caps. The later closure computes that maximum as \(M/2\). **Gate 1 is passed at the written-proof level; Gate 2's independent partial turns remain unproved.**

## 1. The sharp scalar theorem and its full-turn implication

Let \(U\subset\mathbb R\times[0,1]\) be a compact convex **downward closed** cap whose horizontal projection \(I_U=[l,r]\) has width \(W=r-l>0\). Write \(A_U(x)=\max\{y:(x,y)\in U\}\). For \(0<t<L=\pi/2\), put \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\) and define the **entire attached-two-ray** forbidden roof
\[
R_t(x)=\frac{h_U(u_t)-1-x\cos t}{\sin t},\qquad
D_t(x)=\frac{h_U(v_t)-1+x\sin t}{\cos t},
\]
\[
\boxed{n_U(x)=\max\{0,\sup_{0<t<L}\min(R_t(x),D_t(x))\}.}\tag{SD.1}
\]
This is the true positive *ambient* niche roof: it is not truncated to the cap and is not the area of a single selected angle. Define the **moving middle-half window**
\[
J(U)=[l+W/4,r-W/4],\qquad |J(U)|=W/2
\]
and the scalar spatial score
\[
\boxed{\mathcal P(U)=
\int_{I_U\setminus J(U)}A_U(x)\,dx
-\int_{J(U)}n_U(x)\,dx.}\tag{SD.2}
\]
The scalar theorem, proved in [G1C1](gate1-sharp-full-turn-closure.md), is
\[
\boxed{\mathcal P(U)\le M/2
\quad\text{for every normalized height-one downward convex cap }U.}
\tag{SD.3 — PROVED}
\]
Here \(M=1+4Y^2+\arctan Y\), \(4Y^3+3Y-1=0\), \(Y>0\).

**Theorem SD1 (sharp spatial dual implies the full Gate 1 theorem).**
The completed scalar bound SD.3 implies \(|S|\le M\) for **every compact connected full-conventional-two-turn sofa**, without restrictions on vertical span, curvature, symmetry, face order, contact changes or polygon complexity.

**Proof.** For such a genuine sofa put \(K=\operatorname{conv}S\), and let \(U,V\) be its downward upper and reflected-lower convex caps. Their horizontal projections are the same I. Write \(d_U=1-A_U\), \(d_V=1-A_V\), and let \(n_U,n_V\) be their full positive niches. By the completely audited Gate 0 fiber formula, at each x
\[
\ell_K(x)=1-\max\{d_V(x),n_U(x)\}
             -\max\{d_U(x),n_V(x)\}\ge0.
\]
For x in the common middle half J, drop the outer deficits:
\(\ell_K\le1-n_U-n_V\).
For x outside J, drop the two niche terms:
\(\ell_K\le A_U+A_V-1\).
Integrate and use \(|J|=|I\setminus J|=W/2\) to cancel constants:
\[
\boxed{|S|\le|E_{\rm full}(K)|
=\int_I\ell_K
\le\mathcal P(U)+\mathcal P(V)\le M.}\tag{SD.4}
\]
No unearned subtraction of **untruncated** niches from K occurs: the two upper relaxations hold pointwise precisely because of the max operation.

The same inequalities hold for *signed* fibers of an arbitrary auxiliary convex K. Thus SD.3 also gives \(\mathscr S(K)\le M\) on the whole Gate 0 signed convex-hull domain, without applying facet triangles to incompatible hulls. \(\square\)

**Exact sharpness:** For Romik's reference cap \(U_*\), its full niche is supported in the central interval \(J(U_*)\), the upper roof is exactly one there, and the spatial upper relaxation SD.4 is **equality**. The explicit reference area identity therefore gives
\[
\boxed{\mathcal P(U_*)=M/2.}\tag{SD.5}
\]
This is the previously recognized exact equality in [SPB1](spatial-half-partition-bound.md). Its existing failure of **global Minkowski concavity** ([CN](candidate-functional-concavity-counterexample.md)) does *not* disprove the proposed global **value** bound SD.3. Do not try to prove it via that false Jensen statement.

## 2. **Global** vertical-height saturation for this exact spatial score

**Lemma SD2 (extrusion monotonicity).** Let U have actual vertical height H≤1. For every \(0\le\varepsilon\le1-H\), define
\[
U_\varepsilon=U+[0,\varepsilon]e_y.
\]
This is a downward convex cap with the same horizontal projection and width, and
\[
\boxed{\mathcal P(U_\varepsilon)\ge\mathcal P(U).}\tag{SD.6}
\]

**Proof.** The outer roof rises by precisely \(\varepsilon\) at **every x of I**. For any upward unit normal n, the support of \(U_\varepsilon\) exceeds that of U by \(\varepsilon n_y\). Hence at every lower-turn angle the first supporting inner-ray roof rises exactly by \(\varepsilon\), and so does the second:
\[
R_t^{U_\varepsilon}(x)=R_t^U(x)+\varepsilon,\qquad
D_t^{U_\varepsilon}(x)=D_t^U(x)+\varepsilon.
\]
The signed ambient angular supremum rises by \(\varepsilon\). Taking the positive part is 1-Lipschitz, so
\[
0\le n_{U_\varepsilon}(x)-n_U(x)\le\varepsilon
\quad\text{for every }x.
\]
The *exterior-half outer area* increases by exactly \(\varepsilon W/2\); the *central-half niche area* increases by at most \(\varepsilon W/2\). Subtract to get SD.6. \(\square\)

Thus any global upper value theorem restricted to actual **height one** automatically holds for *all* downward caps of height≤1, including those induced by a subunit-height common hull. There is no unsupported monotone-padding assertion for actual **two-handed sofa areas**: the operation is applied solely to the one-cap *dual score*, which obeys the exact inequality above. Known counterexamples to padding the genuine sofa therefore do not contradict SD2.

## 3. **Global** width coercivity: only \(8/5<W<6\) can beat the candidate score

Translation invariance permits centering I at zero, so \(I=[-W/2,W/2]\) and \(J=[-W/4,W/4]\). Since \(A_U(x)\le1\) and \(n_U\ge0\),
\[
\boxed{\mathcal P(U)\le W/2.}\tag{SD.7}
\]
The established exact root bound \(M>8/5\) shows that no cap with \(W\le8/5\) can attain the reference value \(M/2\).

For large W use **one real inner-wall angle with both genuine support witnesses**. At \(t=\pi/4\), support against actual points in U at horizontal extremes gives
\[
h_U(u_{\pi/4})\ge\frac{W}{2\sqrt2},
\qquad h_U(v_{\pi/4})\ge\frac{W}{2\sqrt2}.
\]
This uses only that U is contained in \(y\ge0\), not its support-contact type. The two physical ray roofs at that angle therefore satisfy
\[
R_{\pi/4}(x)\ge W/2-\sqrt2-x,\qquad
D_{\pi/4}(x)\ge W/2-\sqrt2+x.
\]
Their minimum and the full angular supremum give the **universal true-niche lower bound**
\[
\boxed{n_U(x)\ge(W/2-\sqrt2-|x|)_+.}\tag{SD.8}
\]
For \(W\ge6>4\sqrt2\), the expression inside the positive part is nonnegative throughout J. Hence
\[
\begin{aligned}
\int_Jn_U(x)dx
&\ge\int_{-W/4}^{W/4}(W/2-\sqrt2-|x|)dx\\
&=\frac{3W^2}{16}-\frac{\sqrt2 W}{2},
\\
\boxed{\mathcal P(U)}
&\le \frac{(1+\sqrt2)W}{2}-\frac{3W^2}{16}.
\end{aligned}\tag{SD.9}
\]
The final quadratic is strictly decreasing for \(W\ge6\); at six it equals \(3\sqrt2-15/4<3/4<M/2\), using only \(\sqrt2<3/2\) and \(M>8/5\). Thus **any cap attaining or exceeding** \(M/2\) has
\[
\boxed{8/5<W<6.}\tag{SD.10}
\]
These are deliberately conservative exact bounds. No uniform curvature, polygon count, positive-face length or candidate proximity is assumed.

## 4. Attainment and continuity of the spatial-score maximization

**Lemma SD3 (the one-cap scalar variational problem is compact and attained).** Define
\[
\mathcal P_{\max}=\sup\{\mathcal P(U):U\text{ downward compact convex cap of height }\le1\}.
\]
Then \(\mathcal P_{\max}\ge M/2\) and is attained by some **height-one** convex cap whose horizontal width lies strictly between \(8/5\) and 6. No regularity of its exposed curvature measure is assumed.

**Proof.** The reference U* supplies the lower bound. By SD2 and SD.10, a maximizing sequence may be taken with height exactly one and widths in the compact interval \([8/5,6]\). Translate each projection's left endpoint to zero. All caps lie in \([0,6]\times[0,1]\); by compactness of convex bodies (or uniform convergence of support functions), a subsequence converges in Hausdorff distance to a downward convex cap U of height one and nonzero width in the same compact range.

The outer-roof functions converge in L1 on [0,6]. One direct proof uses that the cap graphs define nested-from-below vertical intervals, convex-body indicator functions converge almost everywhere away from their null-area boundaries under Hausdorff convergence, and all indicators lie in the bounded fixed box; dominated convergence gives convergence of symmetric-difference area, equal to the L1 roof difference.

The **full all-angle niche roofs** also converge uniformly on the fixed box. If \(\eta=\|h_{U_j}-h_U\|_\infty\to0\), truncate the angle set to \([\delta,L-\delta]\). On this compact angular interval both physical ray denominators are at least \(\sin\delta\), so the corresponding two-ray roof and its maximum vary by at most \(\eta/\sin\delta\). At the omitted near-axis intervals, the first (near \(t=L\)) or second (near \(t=0\)) ray is at height at most \(C\delta\) **uniformly** for every cap in the fixed box: this follows from \(h_C(e_y)\le1\), the common support-function angular Lipschitz bound, and \(x\in[0,6]\). Thus
\[
\|n_{U_j}-n_U\|_{L^\infty([0,6])}
\le C'\delta+\frac{\eta}{\sin\delta}.
\]
Choosing \(\delta=\sqrt\eta\) (for small \(\eta\)) makes the right side tend to zero. Importantly this **does not assume the same maximizing angle or contact chart** in the approximating cap.

Finally the endpoints of the *moving* middle-half J(U_j) converge because their widths converge. The outer-roof L1 convergence, uniform niche convergence and uniformly bounded roof heights imply \(\mathcal P(U_j)\to\mathcal P(U)\). The limit therefore attains the maximum. Apply height extrusion if needed (it is already height one here). \(\square\)

This establishes the compact infinite-dimensional scalar problem used by the [completed Gate 1 proof](gate1-sharp-full-turn-closure.md). That proof applies canonicalization and the audited spatial source laws to a selected attained maximizer, bounds its horizontal branch, and excludes every tilted branch. It thereby computes the maximum as \(M/2\) and extends the bound to the entire cap domain by SD2.

## 5. Scope of the completed argument

- The spatial partition SD1 is **global and sharp at the reference**, not a near-reference slice bound or an averaging of finitely many angle-tents. Every cap's niche uses its **whole continuous angle** family and both attached inner rays.
- SD.3 is **strictly stronger than the actual coupled full-turn loss** G1.2. Its completed proof implies that original acceptance inequality through the pointwise partition SD1.
- The historical P_J **global concavity conjecture is false** by an exact counterexample. The completed proof uses actual cap variations and spatial source balances at a selected global maximizer; it does not use that concavity conjecture.
- The finite polygonal oracle from the previous G1.2 route is now only an **adversarial exact verification** tool. No amount of finite checking over an unbounded number of facets replaces SD.3.
- **Gate 1 is passed as a written proof.** The ordinary one-turn theorem and its existing exact Gerver enclosure are explicit dependencies. No CI, Lean/Lake build, external refereeing, or new Lean formalization is claimed. **The sharp independent-partial-turn theorem of Gate 2 remains unproved.**
