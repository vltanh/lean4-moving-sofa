# Near-reference full-turn bodies can fail the half-height rectangle test

**Scope.** This gives a geometric negative control on the input admission assumption in the CB/CT background-transfer route. Actual **full-turn** bodies with area arbitrarily close to Romik's reference area need not contain a horizontal midline across their whole projection. The failure is present at an *extreme point of the actual convex hull*, so canonical saturation does not remove it. Applying the already established positive-opposite-face density construction produces the same phenomenon inside the restricted full-turn supremum class. This is not a sofa exceeding the reference and does not disprove competitive-only admission at area strictly greater than M. Labels NM are local.

The arguments use the explicit reference's right end-tip support cone and its neighboring regular outer arc, plus elementary vertical-fiber connectivity. No optimizer, curvature repair, or speculative geometric symmetrization is involved.

## 1. An exact supporting wedge at the reference right tip

Use the original reference coordinates from Note 14: the rightmost point is \(P=(r,1/2)=(1,1/2)\). Put \(\beta=\arctan Y\) with \(4Y^3+3Y-1=0\), and let \(K=\cot\beta=1/Y>0\). On \(0\le t\le\beta\) the upper support is
\[
h_*(t)=\cos t+\tfrac12\sin t.
\]
The reference is invariant under vertical reflection \(y\mapsto1-y\), so on \(-\beta\le t\le0\),
\[
h_*(-t)=\cos t-\tfrac12\sin t.
\]
The supporting inequalities at \(t=\pm\beta\) therefore imply, **for every point of the actual reference body**,
\[
\boxed{\tfrac12-K(r-x)\ \le y\le\
\tfrac12+K(r-x).}\tag{NM.1}
\]

The reference cap's support immediately after \(\beta\) has positive curvature and joins \(P\) with tangent \(n_{\beta+\pi/2}=(-\sin\beta,\cos\beta)\). Its actual upper flank outside the old top-face interval is retained in the reference body, because the reference's positive niches project inside that top face. Consequently, as \(d\downarrow0\),
\[
\boxed{A_*(r-d)=\tfrac12+Kd+o(d).}\tag{NM.2}
\]
This follows directly from the outer support parametrization \((h\cos t-h'\sin t,h\sin t+h'\cos t)\) and the positive smooth density just after \(\beta\); it does not assume a free boundary tangent for an unknown competitor.

## 2. A cut removing the horizontal midline near one tip

For \(\varepsilon>0\), let
\[
\ell_\varepsilon(x)=\tfrac12+\varepsilon-K(r-x),\qquad
S_\varepsilon=\Sigma\cap\{(x,y):y\ge\ell_\varepsilon(x)\}.
\tag{NM.3}
\]
This is a subset of the actual reference \(\Sigma\), so **both complete quarter-turn witnesses remain valid without any adjustment**.

Recall that \(\Sigma\) has nonempty closed vertical interval fibers \([L_*(x),A_*(x)]\), each containing \(1/2\), over its entire horizontal projection \([l,r]\). Outside its central face interval, these fibers equal \([1-A_*(x),A_*(x)]\). At \(x\le b\), with \(b=r-m/2\) the right endpoint of the central reference top face, one has
\[
\ell_\varepsilon(x)\le\tfrac12+\varepsilon-Km/2<0
\]
for all small positive \(\varepsilon\). Indeed \(m>1\) and \(Y<3/10\) imply \(Km/2>5/3\). Thus every old fiber for \(x\le b\) is retained in full.

For \(b\le x\le r\), the upper reference roof \(A_*(x)\) is continuous and nonincreasing and \(\ell_\varepsilon(x)\) is strictly increasing. The inequality \(A_*(x)\ge\ell_\varepsilon(x)\) therefore holds precisely on one closed interval \([b,r_\varepsilon]\), where \(r_\varepsilon<r\) and
\[
A_*(r_\varepsilon)=\ell_\varepsilon(r_\varepsilon).
\tag{NM.4}
\]
Every surviving fiber over the new projection \([l,r_\varepsilon]\) is again a nonempty closed vertical interval, with continuous lower/upper endpoints away from the extreme abscissae. Such a union is connected (the midpoint graph is connected and every fiber meets it). Therefore **\(S_\varepsilon\) is compact, connected and genuinely feasible for both full turns.**

Take \(d_\varepsilon=3\varepsilon/(4K)\). Equation NM.2 gives, for sufficiently small \(\varepsilon\),
\[
A_*(r-d_\varepsilon)=\tfrac12+\tfrac34\varepsilon+o(\varepsilon)
>\tfrac12+\tfrac14\varepsilon=\ell_\varepsilon(r-d_\varepsilon).
\]
Thus
\[
r_\varepsilon\ge r-d_\varepsilon>r-\varepsilon/K,
\]
and NM.4 yields
\[
\boxed{y_\varepsilon:=A_*(r_\varepsilon)
=\ell_\varepsilon(r_\varepsilon)>\tfrac12.}\tag{NM.5}
\]

At the new right extreme \(x=r_\varepsilon\), the *entire* actual fiber is the single point \((r_\varepsilon,y_\varepsilon)\). It is also the unique rightmost point of the actual convex hull \(K_\varepsilon=\operatorname{conv}(S_\varepsilon)\). The latter statement follows because no points have larger \(x\), and at \(x=r_\varepsilon\) there is only one actual point; convex combinations of points with strictly smaller \(x\) cannot create another point at that maximum.

Consequently \(K_\varepsilon\) **does not contain \((r_\varepsilon,1/2)\)**. Its reflected-lower downward cap has roof \(1-y_\varepsilon<1/2\) at the right extreme, so it cannot contain the whole half-height rectangle \(I_\varepsilon\times[0,1/2]\). Its full canonical two-turn saturation, being a subset of its own convex hull, cannot restore this missing midline point either.

## 3. Area and normalization

By NM.1, the line \(\ell_0(x)=1/2-K(r-x)\) is globally below the reference. The differences \(S\setminus S_\varepsilon\) lie in a descending strip of width \(\varepsilon\) between that supporting line and its upward translate. Since the reference is bounded and compact, their areas tend to zero, for example by dominated convergence off the supporting line (which has planar measure zero). Hence
\[
\boxed{|S_\varepsilon|\longrightarrow|\Sigma|=M.}\tag{NM.6}
\]
These areas are strictly below \(M\), since a nonempty tip region is removed.

The old top and bottom horizontal face segments remain untouched because \(\ell_\varepsilon<0\) above their entire abscissa range; the incoming vertical span is still **exactly one**. No anisotropic scaling or additional hallway angles are introduced.

**Theorem NM1.** For every \(\delta>0\) there exists a compact connected body with **both full conventional quarter-turn motions**, unit incoming span, and area in \((M-\delta,M)\), whose actual hull lacks its central horizontal midline at an extreme abscissa. The same-hull canonical saturation has that failure too.

## 4. Persistence in the positive opposite-end-face supremum class

The earlier RR/PD/PS density theorem produces unit-span full-turn bodies \(S_j\) with strictly positive opposite-end horizontal faces, converging to \(S_\varepsilon\) in Hausdorff distance after undoing vanishing rotation/translation, and then permits canonical saturation without changing their actual hulls.

For fixed \(\varepsilon>0\), the right extreme of \(K_\varepsilon\) is unique and lies strictly above the midline by NM.5. A basic compactness observation makes this strict failure **stable under sufficiently close hull perturbations**: if \(K_j\to K_\varepsilon\) in Hausdorff distance and the exposed right face of \(K_\varepsilon\) is the singleton \(P_\varepsilon\), then every sequence of rightmost points of \(K_j\) converges to \(P_\varepsilon\). If not, a subsequence would converge to a different rightmost point of \(K_\varepsilon\), contradicting uniqueness.

Here the incoming reorientations in PD tend to zero because the original top and bottom horizontal faces remain the same nondegenerate reference interval. Their one-sided vertical-normal width derivatives have opposite nonzero signs, so the safe-strip component at that normal is a singleton. Thus for large \(j\) the rightmost face of the normalized approximant, and hence of its same-hull full saturation, remains strictly above height \(1/2\).

Letting \(\varepsilon\downarrow0\) and choosing sufficiently close PD approximants therefore gives **canonically saturated positive opposite-end-face full-turn bodies**, with areas arbitrarily close to \(M\) *from at least below*, for which at least one downward hull cap fails the half-height rectangle requirement. To claim their saturated areas are *strictly below M* would require the missing global upper bound and is not asserted here. The underlying unsaturated approximants can be selected with area strictly below \(|S_\varepsilon|<M\).

**Corollary NM2 (admission barrier).** Neither full-turn feasibility, canonical saturation, positive opposite-end faces, nor arbitrarily high area approaching \(M\) from known feasible shapes implies the half-height rectangle hypothesis of CB/CT. In particular no proximity-only or fixed subcritical-area-threshold argument can provide that hypothesis globally. A competitive-only theorem with the strict premise area \(>M\), an area-aware replacement with explicit deficit, or a direct clipping inequality is not ruled out.

This is a geometric exclusion of a specific background-admission shortcut, **not** a counterexample to the conjectured sharp full-turn value.

No numerical search, CI, Lean/Lake compilation, dependency installation, manuscript build or long computation was used. All arguments are pen and paper, relative to the documented explicit reference and RR/PD/PS dependencies.

## 5. Sharp leading-order cost of destroying the midline

The tip cut in NM.3 admits an explicit leading-order area-loss calculation, which makes its lack of uniform admission slack quantitative.

The support of the reference upper-right flank immediately after \(\beta\) is the middle reference formula
\[
f_*(t)=R\cos(t/2+\pi/8)+k\cos t+\tfrac12\sin t.
\]
Its positive right-hand curvature density at the join is
\[
\rho_\beta=(f_*+f_*'')(\beta+)
=\tfrac34R\cos(\beta/2+\pi/8)>0.
\]
The actual flank is analytic on its right-hand arc, with tangent slope \(A_*'(r-)=-\cot\beta=-K\). Standard curvature of a concave roof graph gives
\[
A_*''(r-)=-\frac{(1+K^2)^{3/2}}{\rho_\beta}
=-\frac1{\rho_\beta\sin^3\beta}.
\]
Thus, putting \(c_\beta=(2\rho_\beta\sin^3\beta)^{-1}\),
\[
\boxed{A_*(r-d)=\tfrac12+Kd-c_\beta d^2+O(d^3),\quad
1-A_*(r-d)=\tfrac12-Kd+c_\beta d^2+O(d^3).}
\tag{NM.7}
\]
Both are *actual* upper and lower surviving reference roofs for sufficiently small \(d>0\), because the positive niche is confined to the central reference face and vanishes on this outer flank.

The cutting line is \(\ell_\varepsilon(r-d)=1/2+\varepsilon-Kd\). The material deleted from the fiber at \(r-d\) has height
\[
q_\varepsilon(d)=
\min\left\{2A_*(r-d)-1,\,
\bigl[\ell_\varepsilon(r-d)-(1-A_*(r-d))\bigr]_+\right\}.
\]
By NM.7, on the relevant small window its two expressions are
\[
2Kd+O(d^2),\qquad
[\varepsilon-c_\beta d^2+O(d^3)]_+.
\]
The first branch matters only for \(d=O(\varepsilon)\), whose integrated area is \(O(\varepsilon^2)\). The second remains positive up to
\(d=\sqrt{\varepsilon/c_\beta}+O(\varepsilon)\). Outside this interval the supporting cut lies below the original lower flank. Consequently
\[
\begin{aligned}
M-|S_\varepsilon|
&=\int_0^{\sqrt{\varepsilon/c_\beta}}
(\varepsilon-c_\beta d^2)\,dd+O(\varepsilon^2)\\
&=\boxed{\frac{2}{3}\sqrt{2\rho_\beta}\,
\sin^{3/2}\beta\;\varepsilon^{3/2}
+O(\varepsilon^2).}
\end{aligned}\tag{NM.8}
\]
This is an ordinary-area statement about the **actual** unsaturated cut reference, not an estimate for its possible increased full canonical saturation.

As a quick arithmetic diagnostic only, evaluating the explicit support arc gave loss/\(\varepsilon^{3/2}\) approximately \(0.133108,0.133644,0.134398,0.135458\) at \(\varepsilon=0.0005,0.001,0.002,0.004\), respectively; the exact coefficient in NM.8 is approximately \(0.131809\). All four samples have the expected convergence trend. The computation took about 0.020 seconds under an external five-second limit. No sampled number is used to prove NM.7--NM.8.

Thus even a *positive* order-\(\varepsilon\) violation of the midline requirement can cost only order \(\varepsilon^{3/2}\) in actual sofa area. A claimed linear penalty for losing that geometric admission hypothesis would be false near the reference unless it uses further properties not included in this cut family.
