# Four independent middle support arcs **plus arbitrary top-normal convex cuts**: an ordinary-area no-gain theorem

**Date:** October 8, 2026. **Status:** A strict, two-handed, asymmetric **area-\(>M\) exclusion** combining the genuinely **complete moving inner-wall ray sweep calibration** [FA2](four-independent-corner-ray-local-calibration.md) with the exact **circular-tail/outer-flank pairing** [TC1–TC4](tail-paired-cut-deficit.md). This extends the local hull-support domain substantially: after independently changing all four upper/lower middle support arcs, one may **independently cut both upper and bottom caps near their vertical support normals**, allowing loss of the original horizontal top/bottom faces, changed vertical span, new polygonal facets, new curvature atoms, and arbitrary changes to the new niche's active contact chart.

The **two kinds of change are kept in separate angular contact ranges**; we pay their ordinary area losses on disjoint spatial pieces. This is not a disguised use of the missing global \(G\le\Delta_U+\Delta_V\) inequality, and the result **does not** prove the unrestricted ambidextrous sharp upper bound or deal with early-stopped partial turns. The source intervals and cap inclusion conditions are genuine restrictions; an arbitrary putative counterexample need not satisfy them.

## 1. Admissible four-arc background and independent cuts

Use Romik's explicit outer reference hull \(K_*=\operatorname{conv}\Sigma_*\) in \(0\le y\le1\), horizontal projection
\[
I=[-m,m],\quad m=\frac1{3\sin\beta},\quad
\beta=\arctan Y,\quad 4Y^3+3Y-1=0,
\]
with common horizontal face interval
\[
J_*=[a,b]=[-m/2,m/2],\qquad
|\Sigma_*|=M.
\]

Fix \(J_0\Subset J_1\Subset(\beta,\pi/2-\beta)\) sufficiently close to \(\pi/4\) to satisfy the strict reference wall-exposure and baseline containment margins from [FA1–FA2](four-independent-corner-ray-local-calibration.md). Let \(K_0\) be **any** compact convex hull in FA2's sufficiently small Hausdorff neighborhood whose **four** middle support source perturbations
\[
(\phi_U,\psi_U,\phi_V,\psi_V)
\]
are supported in \(J_0\) and are **otherwise independent**, with no reflection symmetry assumption. Its genuine upper downward cap \(U_0\) and vertically reflected lower downward cap \(V_0\) contain \(I\times[0,1/2]\), have horizontal projection \(I\), agree with Romik's cap \(U_*\) in all upper support directions **outside \(J_0\)**, and satisfy
\[
|E_{L,L}(K_0)|\le
M-\kappa\mathcal E_4,\quad
\kappa=\tfrac12(1-|J_0|/\pi)>1/4,
\quad
\mathcal E_4=\int_{J_0}(|\phi_U'|^2+|\psi_U'|^2+
|\phi_V'|^2+|\psi_V'|^2).
\tag{AC.1}
\]

Choose any \(0<\eta<\beta\) small enough that the original **terminal tail** intervals of width \(D=(\sin\eta)/2\) lie beyond the horizontal baseline influence of the middle support window \(J_0\). In fact, taking \(J_0\) very close to \(\pi/4\) leaves a strict gap to the full reference terminal circular tail windows; the exact reference midpoint inner corner has roof \(H_*-|x|\), whose positive part vanishes strictly before the tail begins. The same gap persists for K_0 by its FA1 strict support margins.

Let \(U\subseteq U_0\), \(V\subseteq V_0\) be **arbitrary compact convex downward closed cut caps** satisfying
\[
I\times[0,1/2]\subseteq U,\ V
\tag{AC.2}
\]
and whose **actual upper support functions** obey
\[
\boxed{\begin{aligned}
h_U(\theta)&=h_{U_0}(\theta),\\
h_V(\theta)&=h_{V_0}(\theta)
\end{aligned}
\quad\text{for }
\theta\in[0,L-\eta]\cup[L+\eta,\pi],\qquad L=\pi/2.
}\tag{AC.3}
\]
The cut supports **may differ arbitrarily** from the parents on \((L-\eta,L+\eta)\), subject only to convexity, inclusion, and the retained half-height rectangle. They may lower the topmost support below one, replace the top face by a point, introduce exposed facets, or change the vertical span. Crucially, the upper cut and reflected lower cut are chosen **independently**.

Define their actual shared convex hull
\[
\boxed{K=U\cap\rho V,\quad \rho(x,y)=(x,1-y).}\tag{AC.4}
\]
It is convex and has horizontal projection I because of AC.2. The actual upper and reflected lower support directions of K are precisely the corresponding upper support directions of U,V, because \(K\) contains the interval fiber \([1-a_V(x),a_U(x)]\) and retains the top/bottom roof points; downward completion does not change supports with positive vertical normal component. The equality is geometric, not an extra independence assumption.

## 2. One-hand cut payment uses the **old actual middle-perturbed cap**, not only Romik

Write \(A_0(x)\) for the upper convex roof of \(U_0\) and \(n_0(x)\) for its full ordinary positive moving-inner-ray niche roof. For the cut U, write A(x), n(x). Inclusion \(U\subseteq U_0\) gives
\[
d(x)=A_0(x)-A(x)\ge0,\qquad
e(x)=n_0(x)-n(x)\ge0
\]
pointwise on I. Both positive niche sets lie inside the central face J_* and below y=1/2, by the previous protected-margin hypothesis and support monotonicity.

**Lemma AC1 (terminal top-normal cut cannot gain one-turn surviving area).** For every U satisfying AC.2–AC.3, the following **exact ordinary-area** comparison holds:
\[
\boxed{
(|U_0|-N(U_0))-(|U|-N(U))
\ge\int_a^b(A_0-A)\,dx\ge0.
}\tag{AC.5}
\]
The same holds independently for \(V_0\to V\). The full niche \(N(\cdot)\) means the **actual union** of every continuously swept inner-wall quadrant above the baseline, not a signed contact approximation.

**Proof.** The reference terminal niche chart [TC.1](tail-paired-cut-deficit.md) gives
\[
A_0(b+z)=A_*(b+z)=\tfrac12+\sqrt{\tfrac14-z^2},\quad
n_0(b-z)=n_*(b-z)=\tfrac12-\sqrt{\tfrac14-z^2},
\tag{AC.6}
\]
for \(0<z<D\). These equalities persist for U_0 because the **middle support variations are confined to \(J_0\)**, all terminal exposed upper wall normals and their perpendicular companions are unchanged, and every perturbed middle-source ray has a **strict negative-height margin** on these tail abscissae.

Choose the old terminal ray angle
\(t=L-\arcsin(2z)\in(L-\eta,L)\).
Its **first inner-wall** height at \(x=b-z\) equals \(n_0(b-z)\), and its companion second-wall support is unchanged under the cut since its normal lies outside \((L-\eta,L+\eta)\). The support decrease
\[
u(t)=h_{U_0}(u_t)-h_U(u_t)\ge0
\]
therefore reduces that ray's permissible forbidden height by **exactly** \(u(t)/\sin t\) without making the other wall active. Thus the cut niche roof still satisfies
\[
n(b-z)\ge\max(0,n_0(b-z)-u(t)/\sin t).
\]
Consequently
\[
0\le e(b-z)\le u(t)/\sin t.
\tag{AC.7}
\]
At the paired **outer-flank** point \(x=b+z\), the very same old supporting wall is tangent to U_0 and remains a valid outer supporting inequality for the cut U. Hence
\[
A(b+z)\le A_0(b+z)-u(t)/\sin t,
\]
and
\[
\boxed{e(b-z)\le d(b+z).}\tag{AC.8}
\]
The horizontally reflected source normal handles the left tail:
\(e(a+z)\le d(a-z)\), using the other terminal interval near \(\pi/2\) (in support-normal notation this is the companion first/second upper quarter). The cuts need not themselves have any reflection symmetry.

**No other positive niche height can be saved:** outside the two inner tail windows
\[
T_{\rm in}=(a,a+D)\cup(b-D,b),
\]
every positive old niche value has an old attaining parameter outside the changed angular support range, by the exact reference tail chart and the unchanged middle-source witness directions. Its old support values remain unchanged in U by AC.3; hence \(n(x)\ge n_0(x)\), and monotonicity gives equality almost everywhere there. This remains true even if the *new* cut creates different contact switches.

Integrate the two pointwise inequalities AC.8 and its reflection, noting that the corresponding **outer** intervals \((a-D,a)\cup(b,b+D)\) are disjoint from the **central face J_***:
\[
N(U_0)-N(U)\le
\int_{a-D}^a d(x)\,dx+
\int_b^{b+D}d(x)\,dx.
\]
But \(|U_0|-|U|=\int_I d\), and all d are nonnegative. Subtract the saved niche integral to obtain AC.5. \(\square\)

The key advance over [TC2](tail-paired-cut-deficit.md) is that **the parent is an independently middle-perturbed, potentially high-curvature and asymmetric cap**, rather than exactly Romik's cap. The proof remains valid because it uses the **unchanged terminal exposed reference ray and its corresponding outer tangent**; it never needs the parent to have the complete original reference contact chart in the middle.

## 3. Two independent top/bottom cuts plus four support arcs

The actual convex hull K in AC.4 contains the entire half-height midline, and both cut full niches stay below/above it. Their ordinary removed areas are contained inside K, separated in the vertical direction. Therefore its complete two-handed canonical envelope satisfies the **exact area identity**
\[
\boxed{
|E_{L,L}(K)|=(|U|-N(U))+(|V|-N(V))-|I|.
}\tag{AC.9}
\]
The envelope is compact, has nonempty interval fibers meeting the common midline, and hence is connected and supports **two complete conventional quarter-turn motions**. **Its actual convex hull need not equal K** after a severe cut: some newly exposed top/bottom cap points may be forbidden by the opposite turn. This does not affect the area **upper comparison for any actual sofa** with proposed hull K. One must not silently assume extreme-point retention.

Combine the independent cap cut comparisons AC.5 and the fully nonsymmetric four-source area inequality FA.10 for the parent K_0.

**Theorem AC2 (four middle arcs + two arbitrary top-normal cuts).** Under the precise parent/cut hypotheses AC.1–AC.4,
\[
\boxed{
\begin{aligned}
|E_{L,L}(U\cap\rho V)|
\le M
&-\frac12\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}
 (|\phi_U'|^2+|\psi_U'|^2+
  |\phi_V'|^2+|\psi_V'|^2)\,dt\\
&-\int_a^b
 \Big[(A_{U_0}-A_U)+(A_{V_0}-A_V)\Big]dx.
\end{aligned}}\tag{AC.10}
\]
In particular **no** actual connected full-two-turn sofa whose hull has this decomposed independently perturbed-and-cut representation can have area \(>M\).

The conclusion requires **no left-right/vertical reflection symmetry of the resulting sofa**, no fixed vertical span or horizontal top/bottom face lengths, no upper support-curvature domination, no stability of the new full moving-wall exposure chart, and no outer-hull extreme-point-retention premise after the cuts. The caps may contain genuinely new exposed edges and polygonal facets. The cuts can be large subject to their specified angular support and the retained half-height strip.

**Exact scope:** This does **not** cover arbitrary convex hulls near Romik if their upper/lower support changes mix **non-monotone outward/inward moves near the vertical axis**, if their middle and top-normal variations cannot be separated as specified, if their supports change at the reference switching angles, or if their original physical motions stop early. The unproved *global* area bound remains a separate task.

## 4. Why this is not just another below-reference example

AC2 proves an *entire class* of above-\(M\) geometries is impossible, even after axis-normal cuts destroy the unit-vertical-span assumption. The estimate is a genuine **outer-area versus complete niche-sweep inequality**, with the cut's old saved tail area paired to a **disjoint** lost exterior portion of the convex cap, and with the middle perturbation's complete ray/outer-area imbalance paid by a Dirichlet energy. It applies to all relevant real angles, not a finite sample or a local stationary heuristic.

This is still only a reference-neighborhood **support decomposition theorem**, not an admissible global normal form for all competitors. A possible next extension would combine the cut budget with the outgoing-strip cost for \(\alpha,\gamma<L\) when the cuts also change the terminal strip support, or establish an **area-improving** canonicalization which moves far competitor supports into this reference-normal form. Neither statement is proved or inferred here.

No CI, Lean/Lake compilation, symbolic optimizer, artificial convex-only bound or independently verified global sharp certificate is claimed.
