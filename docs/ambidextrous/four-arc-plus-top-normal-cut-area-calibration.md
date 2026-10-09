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

## 3. **Ordinary-fiber proof** for two independent top/bottom cuts; clipping is not discarded

**Crucial correction to the initial research draft:** It is **false** that all of the cut caps' positive niches necessarily lie inside the **new** common convex hull \(K=U\cap\rho V\). Even though the niches lie below/above the common midline, the independently raised new bottom and lowered new top can **clip** them. Consequently the tempting identity
\(|E(K)|=(|U|-N(U))+(|V|-N(V))-|I|\)
is valid for the *uncut parent* but **need not hold after the cuts**. No proof may count a forbidden region outside its actual outer hull as missing sofa area.

**An exact reference counterexample to the discarded identity.** Take the unperturbed parent \(U_0=V_0=U_*\), choose a small \(\delta>0\), cut **only the upper cap** by the horizontal line \(y=1-\delta\), and leave the reflected lower cap V unchanged. This is allowed by AC.2–AC.3 for sufficiently small \(\delta\) and fixed \(\eta>0\): all changed supporting normals cluster around the vertical normal. On the old central face \(J_*\), the *cut* upper roof is \(A_U=1-\delta\), while the **uncut upper-handed niche** has height \(n_V(x)=n_*(x)\).

If one falsely subtracted that entire upper niche from the cut outer hull, it would assign top survivor height \(1-\delta-n_*(x)\). The **true** top survivor height is
\[
\min(1-\delta,1-n_*(x))
=1-\max(\delta,n_*(x)).
\]
The difference, which was previously omitted, is exactly
\[
\boxed{\min(\delta,n_*(x))>0}
\]
on every interior central-face point with positive old niche. In particular the reference circular terminal tail obeys
\(n_*(b-z)=q(z)>0\) for every \(0<z<\tfrac12\sin\beta\), so this is a **positive-area clipping correction**, not an isolated boundary artifact. It can have fractional-power size near the face endpoints. The corrected proof below handles it with the pointwise max, rather than assuming it is zero.

The correct comparison is **pointwise in the ordinary surviving vertical fibers** and pays the clipping without making any global \(G\)-estimate.

Let \(a_0^U(x),a_0^V(x)\) be the two parent's downward convex roof heights, and \(n_0^U(x),n_0^V(x)\) its complete positive lower/upper-turn niche roofs. For the cuts write
\[
a^U=a_0^U-d_U,\quad a^V=a_0^V-d_V,\qquad
n^U=n_0^U-e_U,\quad n^V=n_0^V-e_V,
\]
where \(d_U,d_V,e_U,e_V\ge0\).

On the common middle face \(J_*=[a,b]\), the *parent* has
\[
a_0^U=a_0^V=1
\]
by preserved reference face endpoints and the full core rectangle. Its ordinary canonical two-turn fiber has length
\[
\ell_0(x)=1-n_0^U(x)-n_0^V(x)\qquad(x\in J_*),
\tag{AC.9}
\]
where the two parent niches do not overlap because they lie strictly below/above the midline.

The cut's **true ordinary surviving fiber**, with both outer losses and both inner niches, has length exactly
\[
\ell(x)=
\Big[\,1-\max(d_U(x),n^V(x))
           -\max(d_V(x),n^U(x))\,\Big]_+
\quad(x\in J_*).
\tag{AC.10}
\]
Because both cut caps contain the full midline, and their new niches are subsets of the parent's strictly sub-midline niches, this fiber is actually **nonempty**: its raw length is nonnegative and the outer positive part may be dropped. In particular,
\[
\boxed{
\ell(x)\le 1-n^U(x)-n^V(x)
=\ell_0(x)+e_U(x)+e_V(x).
}\tag{AC.11}
\]
This inequality already includes **all clipping by the changed upper/lower caps**, with no fictional subtraction of niche area lying outside K.

**Outside** \(J_*\), both original and cut positive niches vanish identically by support monotonicity and the parent's central-niche enclosure. The ordinary canonical fiber is just the actual convex outer fiber, so
\[
\boxed{
\ell(x)=\ell_0(x)-d_U(x)-d_V(x)
\qquad(x\in I\setminus J_*).
}\tag{AC.12}
\]
Integrate AC.11–AC.12:
\[
\boxed{
|E_{L,L}(K)|-|E_{L,L}(K_0)|
\le\int_{J_*}(e_U+e_V)\,dx
-\int_{I\setminus J_*}(d_U+d_V)\,dx.
}\tag{AC.13}
\]

Now apply the **full-ray tail/outer-flank pairing from AC1** separately to both hands. Every positive saved-niche height occurs within \(J_*\), and the combined savings are bounded by outer flank roof losses on the explicit interval union
\[
F_{\rm out}=(a-D,a)\cup(b,b+D)\ \subseteq I\setminus J_*:
\quad
\int_{J_*}(e_U+e_V)\,dx
\le\int_{F_{\rm out}}(d_U+d_V)\,dx.
\tag{AC.14}
\]
Therefore
\[
\boxed{
|E_{L,L}(K)|
\le |E_{L,L}(K_0)|
-\int_{I\setminus(J_*\cup F_{\rm out})}
(d_U+d_V)\,dx
\le |E_{L,L}(K_0)|.
}\tag{AC.15}
\]

**Theorem AC2 (four independent middle support arcs plus two arbitrary top-normal cuts, corrected).** Under the precise parent/cut hypotheses AC.1–AC.4,
\[
\boxed{
\begin{aligned}
|E_{L,L}(U\cap\rho V)|
\le M
&-\frac12\left(1-\frac{|J_0|}{\pi}\right)
\int_{J_0}
 (|\phi_U'|^2+|\psi_U'|^2+
  |\phi_V'|^2+|\psi_V'|^2)\,dt\\
&-\int_{I\setminus(J_*\cup F_{\rm out})}
(d_U+d_V)\,dx .
\end{aligned}}\tag{AC.16}
\]
In particular no actual compact connected full-two-turn sofa whose actual hull is of this four-middle-arc-perturbed-and-two-cap-cut form can have area \(>M\).

**Proof.** Apply the exact ordinary-fiber inequality AC.13, the geometrically disjoint saved-tail payment AC.14, and the parent full-turn coercivity FA.10. **Do not invoke the false full-niche subtraction identity for the cut hull.** \(\square\)

The resulting canonical envelope is compact, has interval vertical fibers meeting the common midline, is connected and follows both complete conventional quarter turns. Its **actual convex hull need not equal** the proposed K after severe cap cuts, because some newly exposed top/bottom extreme points may be lost. This does not affect the comparison for a genuine sofa with hull K: canonical tightening gives \(S\subseteq E(K)\), and hence \(|S|\le|E(K)|\le M\).

This is a true ordinary-area accounting argument in the class considered: no formal signed deficit, globally unknown cap-interaction budget, or assumption that all swept niches lie inside the *new* hull occurs. Asymmetry and possible subunit vertical span are allowed.

## 4. Why this is not just another below-reference example

AC2 proves an *entire class* of above-\(M\) geometries is impossible, even after axis-normal cuts destroy the unit-vertical-span assumption. The estimate is a genuine **outer-area versus complete niche-sweep inequality**, with the cut's saved terminal niche area paired to a **disjoint** lost exterior portion of the convex cap, and with the middle perturbation's complete ray/outer-area imbalance paid by a Dirichlet energy. It applies to all relevant real angles, not a finite sample or a local stationary heuristic.

This is still only a reference-neighborhood **support decomposition theorem**, not an admissible global normal form for all competitors. A possible next extension would combine the cut budget with the outgoing-strip cost for \(\alpha,\gamma<L\) when the cuts also change the terminal strip support, or establish an **area-improving** canonicalization which moves far competitor supports into this reference-normal form. Neither statement is proved or inferred here.

No CI, Lean/Lake compilation, symbolic optimizer, artificial convex-only bound or independently verified global sharp certificate is claimed.
