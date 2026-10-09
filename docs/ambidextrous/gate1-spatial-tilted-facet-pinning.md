# Gate 1 global scalar maximizer: a tilted middle facet must be **pinned by two corners**

**Date:** October 9, 2026. **Status:** A **global-domain necessary condition** for every maximizer of the *active* spatial one-cap score [SD.2](gate1-spatial-dual-height-width-compactness.md) after the value-preserving [MID2](gate1-global-middle-chord-canonicalization.md) normal form. This is a written hand proof for arbitrary convex downward caps, with no support curvature cap, candidate proximity, numerical sample, chosen inner-ray contact chart or polygon complexity assumption.

**Conclusion:** At a genuine global maximizer with **tilted** affine middle-half upper roof, that facet must terminate at the *two artificial middle-window endpoints* in **strict geometric corners**; it cannot extend into either charged exterior wing or even join either wing tangentially. **The global top-insertion argument in Section 3a further proves that the higher of those two endpoints has height exactly one.** It works on every cap, without an infinitesimal variation or a regularity assumption: a top face disjoint from J can be extended to the nearer J endpoint with strictly larger score and exactly the same full niche on J. A canonical spatial-score maximizer that is \(C^1\) at either middle-window endpoint must have a **horizontal** middle facet. These are restrictions on the **whole global maximizing class**, not a reference-neighborhood argument. They do **not** prove \(\mathcal P_{\max}=M/2\), and **Gate 1 remains ACTIVE**.

## 1. A whole-angle **support-inactivity neighborhood** for any tilted middle facet

Let \(U\subset\mathbb R\times[0,1]\) be a compact convex downward-closed cap of positive width \(W=r-l\), with full horizontal projection \(I=[l,r]\), height exactly one, and concave upper roof \(A\). Put
\[
j_-=l+W/4,\qquad j_+=r-W/4,\qquad J=[j_-,j_+].
\]
Suppose the whole central charged window is affine:
\[
\boxed{A(x)=a+s x\quad(x\in J),\qquad s\ne0.}\tag{TF.1}
\]
The corresponding **actual outer facet** has outward unit normal
\[
n_c=\frac{(-s,1)}{\sqrt{1+s^2}}\in\{n:n_y>0\}.
\]
Its upper supporting value is
\[
h_U(n_c)=\frac{a}{\sqrt{1+s^2}}.
\]
For every \(x\in J\), at the baseline point \(p_x=(x,0)\) the **inner-wall** inequality for this source normal would require
\(p_x\cdot n_c<h_U(n_c)-1\), but
\[
\boxed{
h_U(n_c)-1-p_x\cdot n_c
=\frac{A(x)}{\sqrt{1+s^2}}-1
\le-\delta_s,\qquad
\delta_s=1-\frac1{\sqrt{1+s^2}}>0.
}\tag{TF.2}
\]
Since \(n_{c,y}>0\), the same strict inequality against entering the *forbidden* halfplane holds for every \(y\ge0\), not only y=0:
\(
h_U(n_c)-1-(x,y)\cdot n_c\le-\delta_s
\)
for x∈J.

By uniform continuity of \(n\mapsto h_U(n)-1-(x,0)\cdot n\) on the compact unit upper semicircle times J, there is an open arc \(\Omega\Subset\{n:n_y>0\}\) around \(n_c\) such that
\[
\boxed{
h_U(n)-1-(x,y)\cdot n\le-\delta_s/2
\quad(n\in\Omega,\ x\in J,\ y\ge0).
}\tag{TF.3}
\]
The positivity of \(n_y\) is why the inequality extends to all \(y\ge0\).

**Lemma TF1 (complete niche blind spot).** If another downward convex cap \(V\) has the same horizontal projection and
\[
h_V(n)=h_U(n)\quad(n\in[0,\pi]\setminus\Omega),
\qquad
\|h_V-h_U\|_{\infty,[0,\pi]}<\delta_s/4,
\tag{TF.4}
\]
then their **entire true positive continuous-angle inner-wall niche roofs** coincide on J:
\[
\boxed{n_V(x)=n_U(x)\qquad(x\in J).}\tag{TF.5}
\]

**Proof.** Every proper lower-turn quadrant has one of the normals \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\) in the upper semicircle. If **either** of its normals belongs to \(\Omega\), TF.3 and the support perturbation bound show that this *single wall* rules out the whole **positive-height forbidden quadrant at every x∈J** for both U and V. If neither normal lies in \(\Omega\), both wall supports and thus the entire one-angle V-tents are identical for U,V. The union over all real \(t\in(0,\pi/2)\), followed by max with zero, gives TF.5. No unique contact angle, active-ray chart or absence of angular superlevel components is assumed. \(\square\)

## 2. A local *outer-wing gain* with no **inner-ray cost**

Fix \(x_0\) in the relative interior of a **charged exterior wing**
\((l,j_-)\cup(j_+,r)\), and let \(p_0=(x_0,A(x_0))\) be its actual upper boundary point. Suppose
\[
A(x_0)<1,\qquad
\boxed{N_U(p_0)\cap\{n:n_y>0\}\subset\Omega,}\tag{TF.6}
\]
where \(N_U(p_0)\) denotes the set of outward supporting normal directions at \(p_0\) (relative to the upper semicircle). This is automatically satisfied for any relative-interior point of the tilted central exposed facet, since its only upper normal is \(n_c\).

Let
\[
p_\varepsilon=p_0+\varepsilon e_y,\quad
0<\varepsilon<1-A(x_0),
\]
and define the **genuine downward convex** cap
\[
\boxed{
U_\varepsilon=\operatorname{conv}
\bigl(U\cup(\{x_0\}\times[0,A(x_0)+\varepsilon])\bigr).
}\tag{TF.7}
\]
Convexity and downward closure follow directly: any convex combination of downward vertical fibers contains all heights below it at the same abscissa, by simultaneously decreasing the contributing heights. The new cap has the **same horizontal projection I and width W**, and retains height one.

For every upper normal n, the support of the new cap is
\[
h_{U_\varepsilon}(n)=
\max\{h_U(n),p_\varepsilon\cdot n\}.
\]
The continuous function \(h_U(n)-p_0\cdot n\) is positive on the compact **complement of** \(\Omega\) in the upper semicircle by TF.6. Thus it has a positive minimum \(d>0\) there. If \(\varepsilon<d\), then
\[
h_{U_\varepsilon}(n)=h_U(n)\quad(n\notin\Omega),\qquad
0\le h_{U_\varepsilon}(n)-h_U(n)\le\varepsilon\quad(n\in\Omega).
\]
Taking also \(\varepsilon<\delta_s/4\) invokes TF1 and gives **exact equality of the entire central charged niche**:
\[
\int_J n_{U_\varepsilon}=\int_J n_U.
\tag{TF.8}
\]
On the other hand \(p_\varepsilon\) lies strictly above the old roof at the **charged** x-coordinate \(x_0\). The new concave upper roof \(A_\varepsilon\) is continuous in the interior of I; it strictly exceeds A on a positive-length neighborhood of \(x_0\) inside the wing, and does not decrease anywhere. Hence
\[
\boxed{
\mathcal P(U_\varepsilon)-\mathcal P(U)
=\int_{I\setminus J}(A_\varepsilon-A)\,dx>0.
}\tag{TF.9}
\]

**Lemma TF2 (wing-boundary source normals cannot be hidden).** No **local** or global maximizer of the full spatial score \(\mathcal P\) can have a charged upper-roof boundary point satisfying TF.6, when its central roof has a nonhorizontal affine facet TF.1. The proof is the arbitrary-small, actually convex perturbation TF.7–TF.9; **it accounts for the complete moving-corner plus both attached inner-ray envelopes**, not a single contact shadow.

## 3. The canonical middle facet must terminate in two real corners

**Theorem TF3 (two strict middle-window facet junctions).** Let U be a **global maximizer** of the score \(\mathcal P\) on all downward convex caps of height at most one, selected by the global [MID2](gate1-global-middle-chord-canonicalization.md) reduction so that its roof is affine throughout J. If that affine slope \(s\ne0\), then
\[
\boxed{
A'_-(j_-)>s>A'_+(j_+).
}\tag{TF.10}
\]
In particular the maximal affine facet of slope s has **horizontal projection exactly** \([j_-,j_+]\). A global score maximizer whose upper roof is differentiable at **either** of the two central-window endpoints necessarily has \(s=0\), hence
\[
\boxed{A(x)\equiv1\quad(x\in J).}\tag{TF.11}
\]

**Proof.** A finite concave roof is locally Lipschitz in the interior of its projection. Its one-sided derivatives satisfy the non-strict inequalities \(A'_-(j_-)\ge s\ge A'_+(j_+)\). Suppose \(A'_+(j_+)=s\). Because \(A'\) is monotone decreasing, the one-sided slope intervals (and thus *every* upper supporting normal cone) at boundary points \(p_x=(x,A(x))\) with \(x\downarrow j_+\) from the **right wing** converge to the singleton \(\{n_c\}\). Thus there exist actual wing coordinates \(x_0>j_+\), arbitrarily close to \(j_+\), with **every** upper outward normal at \(p_0\) lying inside the open inactivity arc \(\Omega\) of TF1.

We may choose \(A(x_0)<1\). Indeed if \(s<0\), values to the right decrease strictly near \(j_+\), hence are less than one. If \(s>0\), continuity with right derivative \(s>0\) would give \(A(x)>A(j_+)\) immediately to the right; the height-one bound then forces \(A(j_+)<1\). Hence TF.6 holds. Lemma TF2 contradicts maximality. The same argument at the **left** endpoint (x\uparrow j_- through the left wing) rules out \(A'_-(j_-)=s\): for \(s>0\), the roof decreases when moving left; for \(s<0\), any matching negative left derivative forces \(A(j_-)<1\) by the height-one bound. Therefore both strict inequalities hold.

Any continuation of the affine facet into either exterior wing would give the corresponding one-sided derivative equality, which is impossible. Thus the facet's maximal x-projection is exactly J. If a global maximizer were differentiable at either endpoint, both one-sided derivatives there would equal the inside slope s, contradicting TF.10 unless \(s=0\). Finally, a downward cap of exact height one with a **horizontal** upper face on J has \(A|_J\equiv1\), because a concave roof with a horizontal segment has its global maximum at the height of that segment and its global maximum is exactly one. \(\square\)

### 3a. A global top-insertion map, with exactly zero charged niche cost

**Theorem TF4 (top localization for every global spatial maximizer).** Let U be any positive-area downward compact convex cap of height \(H\le1\), with projection I and middle-half window J as above. If its top face \([a,b]\times\{H\}\) is disjoint from J, there is a downward convex cap \(\widehat U\supset U\) of the **same height and projection**, whose top face meets J, such that
\[
\boxed{n_{\widehat U}|_J=n_U|_J,\qquad
\mathcal P(\widehat U)>\mathcal P(U).}
\tag{TF.10a}
\]
Consequently the top face of **every** global maximizer meets J. For a height-one MID2-canonical maximizer with nonzero central slope,
\[
\boxed{s>0\Longrightarrow A(j_+)=1,\qquad
s<0\Longrightarrow A(j_-)=1.}
\tag{TF.10b}
\]

**Proof.** Suppose first that the top face lies to the right, so \(a>j_+\). Put
\[
p=(j_+,H),\qquad
\widehat U=\operatorname{conv}\bigl(U\cup(\{j_+\}\times[0,H])\bigr).
\tag{TF.10c}
\]
This cap has the same projection and height. For an upper unit normal \(n=(n_x,n_y)\), its support is \(\max(h_U(n),p\cdot n)\). If \(n_x\ge0\), the old top point \((a,H)\) dominates p, so the support is unchanged. If a support **does** change, then \(n_x<0\) and \(h_{\widehat U}(n)=p\cdot n\). At every \(x\in J\) and \(y\ge0\),
\[
h_{\widehat U}(n)-1-(x,y)\cdot n
=(j_+-x)n_x+(H-y)n_y-1\le0.
\tag{TF.10d}
\]
Thus this changed source wall excludes the entire positive-height forbidden quadrant over J, for both the old and new cap. Every angle whose two source supports are unchanged has exactly the same quadrant. Taking the union over **all real turning angles** proves equality of the two positive niche roofs on J.

The new roof is H on \([j_+,a]\). The old roof is strictly below H on \((j_+,a)\), by the definition of a. This interval lies in the charged right wing, and the new roof does not decrease anywhere. Hence
\[
\mathcal P(\widehat U)-\mathcal P(U)
\ge\int_{j_+}^{a}(H-A(x))\,dx>0.
\tag{TF.10e}
\]
If the old top lies left of J, reflect the construction and insert \((j_-,H)\). This proves the global map and excludes a disjoint top face at any maximizer. On a tilted affine central segment the only point that can have the global maximum height is its higher endpoint, proving TF.10b. \(\square\)

**Exact elementary check.** For \(A(x)=(x+1)/2\) on \([-1,1]\), the top point is \((1,1)\) and \(J=[-1/2,1/2]\). Inserting \((1/2,1)\) gives the roof \(2(x+1)/3\) up to \(x=1/2\), then height one. The all-angle argument just given proves the charged niche is unchanged, and direct rational integration gives
\[
\Delta\mathcal P=\frac1{48}+\frac1{16}=\frac1{12}>0.
\tag{TF.10f}
\]
This construction does not claim the cap itself is a feasible ambidextrous sofa. It is a globally score-improving map on the exact auxiliary domain of SD.3.

**Limit of the conclusion.** A tilted central facet can still have a low endpoint below one and a strict corner at each J endpoint. TF4 places its top at the higher endpoint; it does not flatten that facet or establish the sharp value.

## 4. Exact rational check on a full-width tilted facet (no angle sampling)

The simplest possible cap has the entire roof tilted:
\[
U=\operatorname{conv}\{(-1,0),(-1,1),(1,0)\},\quad
A_U(x)=\frac{1-x}{2},\qquad I=[-1,1],\ J=[-1/2,1/2].
\tag{TF.12}
\]
Its upper middle facet has slope \(s=-1/2\) and extends into **both** charged wings. For any rational
\(0<\varepsilon\le1/100\), add the real upper point
\[
p_\varepsilon=(3/4,\,1/8+\varepsilon),\qquad
U_\varepsilon=\operatorname{conv}(U\cup\{p_\varepsilon\}).
\tag{TF.13}
\]
This is again a downward-closed height-one cap with the identical projection I. Its piecewise-affine upper roof is the old roof plus
\[
A_{U_\varepsilon}(x)-A_U(x)=
\begin{cases}
\frac{4\varepsilon}{7}(x+1),&-1\le x\le3/4,\\
4\varepsilon(1-x),&3/4\le x\le1.
\end{cases}
\tag{TF.14}
\]
Thus its *charged exterior-wing area* is larger by the **exact** value
\[
\int_{[-1,-1/2]\cup[1/2,1]}
(A_{U_\varepsilon}-A_U)dx
=\left(\frac1{14}+\frac{13}{56}+\frac18\right)\varepsilon
=\frac{3\varepsilon}{7}.
\tag{TF.15}
\]

The **entire full-continuum positive niche roof on J is unchanged**. Here is an explicit angular proof: in the upper semicircle a new support point \(p_\varepsilon\) can only beat the old right tip \((1,0)\) for a positive-x normal \(n=(c,s)\) if
\[
\tan t=\frac{s}{c}>
\frac{1/4}{1/8+\varepsilon}
=\frac2{1+8\varepsilon}>\frac32 .
\tag{TF.16}
\]
For every such source normal \(u_t=(c,s)\) one has
\(c<2/\sqrt{13}\). At **every** baseline abscissa \(x\in J\), the first inner-wall support numerator
\(h_{U_\varepsilon}(u_t)-1-xc\) is negative **for each of the three possible maximizing vertices separately**:
\[
\begin{aligned}
(1-x)c-1&\le 3/\sqrt{13}-1<0,\\
s-(1+x)c-1&<0,\\
(3/4-x)c+(1/8+\varepsilon)s-1
&\le(5/2)/\sqrt{13}+27/200-1<0.
\end{aligned}\tag{TF.17}
\]
(The third comparison follows already from \(\sqrt{13}>7/2\): \(5/7+27/200<1\).)
Because both lower-turn normals have nonnegative vertical component, the inequality remains negative for every \(y\ge0\). New \(p_\varepsilon\) cannot improve the **second** upper-quarter support \(h(v_t)\) at all, since \(p_\varepsilon-(-1,1)=(7/4,-7/8+\varepsilon)\) has **negative** projection onto every \(v_t=(-\sin t,\cos t)\), \(0<t<\pi/2\).

Thus in every angle where any support has changed, the *first wall* excludes positive-height niche points throughout J; all other angles have literally identical two-ray constraints. Hence
\[
\boxed{
n_{U_\varepsilon}(x)=n_U(x)\ \text{on J},\qquad
\mathcal P(U_\varepsilon)-\mathcal P(U)
=\frac{3\varepsilon}{7}>0.
}\tag{TF.18}
\]
This is an **exact all-angle rational perturbation**, not an approximate grid or a feasibility claim about ambidextrous sofas. It independently checks the support-locality mechanism behind TF1–TF3 against a concrete tilted affine roof.

### Connection to the current Gate 1 value theorem — and strict limit

TF3 **globally** eliminates **all smooth tilted middle-facet candidates** and all tilted facets extending beyond the uncharged central half. TF4 places the top at their higher endpoint. The remaining canonical tilted alternative therefore has **two genuine roof corners pinned at the moving middle-window endpoints, with the higher endpoint at height one**. To pass Gate 1 one must still either:

- prove those pinned tilted candidates have score at most Romik's value (or are not maximizing), and control the general smooth exterior wing contact/curvature system; or
- establish directly the sharp score bound \(\mathcal P(U)\le M/2\) for all caps, including these pinned alternatives.

In particular **this note does not show that the middle facet must be horizontal** at *every* global maximizer, does not assume the general spatial functional is concave, and does not assert the separate one-turn \(\Psi\) maximizer conditions for \(\mathcal P\). The sharp scalar Gate 1 lemma SD.3, the true coupled Gate 1 area inequality and the unrestricted moving-sofa conjecture remain **UNPROVED**.

This is a *global maximizer necessary condition* for the active scalar score, rather than another local perturbation or convex-only area certificate. No CI, Lean/Lake, numerical area certificate, or claim of solved optimality.
