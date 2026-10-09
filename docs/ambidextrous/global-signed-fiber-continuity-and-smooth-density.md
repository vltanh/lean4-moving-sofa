# Global continuity and smooth-hull density for the **exact joint moving-wall signed area**

**Status (2026-10-09): an unconditional Gate 1/2 *global-domain reduction*, not the sharp inequality.** This proves that the original-motion joint signed area functional is **continuous under Hausdorff convergence of arbitrary convex hulls and both independent terminal angles**. It follows that the global supremum in [Gate 0's exact equivalence](original-motion-global-bridge-gate0-audit.md) is **attained** in the full compact auxiliary domain and that proving the sharp area inequality on **smooth, strictly convex, everywhere positive-curvature auxiliary hulls** alone is **equivalent** to proving it for **all convex hulls**, even those with exposed edges, singular curvature atoms, opposite-end horizontal faces, empty fibers or incompatible outer hulls.

This is a genuinely **global** density statement: it imposes **no reference-neighborhood or motion-feasibility restriction** and treats partial turns and their outgoing whole-body strips. It removes singular hull support geometry from the *input class of a global upper proof*. It does **not** prove the required sharp inequality \(\mathscr V\le M\), construct an above-\(M\) sofa, show an optimizer is smooth, or imply that arbitrary support smoothing preserves actual motion feasibility. The proof operates on **auxiliary hulls**, legitimately allowed by the exact signed supremum reduction.

## 1. Uniformly bounded positive swept roofs are jointly continuous

Let
\[
B=[-R,R]\times[0,1],\qquad R=5/2,
\quad L=\pi/2,\quad
\mathcal K_B=\{K\subseteq B:\varnothing\ne K\text{ compact convex}\}.
\]
This class includes zero-area convex hulls. Put \(u_t=(\cos t,\sin t)\), \(v_t=(-\sin t,\cos t)\). For \(0<t<L\), \(|x|\le R\), define the complete physical lower inner-wall **two-ray** roof
\[
m_{K,t}(x)=\min\left\{
 \frac{h_K(u_t)-1-x\cos t}{\sin t},
 \frac{h_K(v_t)-1+x\sin t}{\cos t}
\right\}.
\tag{SD.1}
\]
Set \(r(K,x,t)=(m_{K,t}(x))_+\) for \(0<t<L\), and **define** \(r(K,x,0)=r(K,x,L)=0\). For every proper terminal angle \(\alpha\in[L/2,L]\), the true positive swept niche roof is
\[
\boxed{n_{K;\alpha}(x)=\max_{0\le t\le\alpha}r(K,x,t).}\tag{SD.2}
\]
This max is over the actual continuum of angles, and includes both attached inner rays. Introducing the harmless endpoint values zero does **not** insert forbidden material at the two axis limits.

**Lemma SD1 (uniform endpoint clearance and joint roof continuity).** The map
\[
(K,x,t)\longmapsto r(K,x,t)
\]
is **jointly continuous** on the compact domain
\(\mathcal K_B\times[-R,R]\times[0,L]\), where \(\mathcal K_B\) has the Hausdorff metric. In particular both partial-angle roofs
\[
(K,x,\alpha)\longmapsto n_{K;\alpha}(x)
\]
are jointly and therefore **uniformly continuous** on
\(\mathcal K_B\times[-R,R]\times[L/2,L]\).

**Proof.** Every \(p\in B\) has Euclidean norm strictly less than \(3\), so the support function of any K in the domain is angularly 3-Lipschitz and uniformly bounded in absolute value by 3. Also \(h_K(e_y)\le1\). For \(0<t\le1/2\), the **second** wall in SD.1 bounds the minimum:
\[
m_{K,t}(x)\le
\frac{h_K(v_t)-1+x\sin t}{\cos t}
\le \frac{3t+R t}{\cos t}
\le 11t,
\tag{SD.3}
\]
using \(|v_t-e_y|\le t\), \(\cos t>1/2\). Similarly, for \(0<L-t\le1/2\), the **first** wall gives
\[
m_{K,t}(x)\le11(L-t).
\tag{SD.4}
\]
Thus \(\sup_{K,x}r(K,x,t)\to0\) at either angular endpoint; in the interior the two support values, positive denominators, their minimum and positive part are jointly continuous under uniform support convergence. This proves the asserted joint continuity on the full compact domain, even when K degenerates, support contacts switch, or a corner-height superlevel set splits into many components.

For a varying terminal magnitude, use the **fixed** parameter interval \([0,1]\):
\[
n_{K;\alpha}(x)=\max_{z\in[0,1]}r(K,x,\alpha z).
\]
The expression under the max is jointly continuous on a compact product. An elementary supremum-difference bound,
\(
|\max_z a_z-\max_z b_z|\le\max_z|a_z-b_z|,
\)
proves joint continuity of n. The reflected upper niche \(n_{\rho K;\gamma}\), \(\rho(x,y)=(x,1-y)\), has the same property because vertical reflection is Hausdorff continuous. \(\square\)

**Optional explicit fixed-angle modulus.** Let \(K,K'\subseteq B\), \(d=d_H(K,K')\), and \(x,x'\in[-R,R]\). For \(0<\delta\le1/2\), the near-axis contributions have roofs at most \(11\delta\) by SD.3–SD.4, while on \([\delta,L-\delta]\) the two wall fractions differ by at most \(2(d+|x-x'|)/\delta\). Therefore for every fixed \(\alpha\in[L/2,L]\),
\[
\boxed{
|n_{K;\alpha}(x)-n_{K';\alpha}(x')|
\le22\delta+\frac{2(d+|x-x'|)}{\delta}.
}\tag{SD.5}
\]
When \(d+|x-x'|\le1/4\), choose
\(\delta=\sqrt{d+|x-x'|}\) to obtain a universal
\(24\sqrt{d+|x-x'|}\) bound. This is a direct *whole-angle* modulus, not a discretized or chosen-contact estimate.

## 2. Upper/lower convex-hull roofs converge at every interior projected coordinate

For \(K\in\mathcal K_B\) write
\[
I_K=[l_K,r_K],\quad W_K=r_K-l_K,\quad
K_x=[B_K(x),A_K(x)]\quad(x\in I_K).
\]
Both roof graphs are bounded between 0 and 1. Their upper/lower boundaries are respectively concave/convex functions and are continuous in the **interior** of \(I_K\), even when K is a line segment.

**Lemma SD2 (joint graph convergence inside a moving projection).** Suppose \(K_j\to K\) in Hausdorff distance, \(W_K>0\), and \(x_j\in I_{K_j}\) satisfy \(x_j\to x\in(l_K,r_K)\). Then
\[
\boxed{
A_{K_j}(x_j)\to A_K(x),\qquad
B_{K_j}(x_j)\to B_K(x).
}\tag{SD.6}
\]

**Proof.** Let \(p_j=(x_j,A_{K_j}(x_j))\in K_j\). Compactness gives subsequential limits, all in K, so every upper limit of its y-coordinate is at most \(A_K(x)\). For the other inequality, fix \(p=(x,A_K(x))\in K\) and choose points of K with abscissae \(x-\varepsilon\) and \(x+\varepsilon\), possible because x lies in the projection interior. Hausdorff convergence supplies approximations in K_j to all three points. If the middle approximation has abscissa \(x'_j\ne x_j\), combine it with the left or right approximant to hit **exactly x_j**. The coefficient on that auxiliary point tends to zero because \(x'_j-x_j\to0\), whereas the auxiliary abscissa stays separated from x. The resulting point lies in K_j by convexity and has height tending to \(A_K(x)\), proving the lower limit. The proof for B uses a lower boundary point instead. The argument covers flat facets and lower-dimensional limits; no differentiability is assumed. \(\square\)

Both horizontal extrema \(l_K,r_K\) converge under Hausdorff convergence, because they are support values at the horizontal axis normals. If \(W_K=0\), then \(W_{K_j}\to0\) instead, and the uniform height bounds make the signed area tend to zero.

## 3. The **exact** original-motion signed objective is jointly continuous

For \(\alpha,\gamma\in[L/2,L]\), recall the **true outgoing whole-body** lower barrier
\[
e_{K;\alpha}(x)=
\frac{h_K(u_\alpha)-1-x\cos\alpha}{\sin\alpha}.
\tag{SD.7}
\]
Since \(\sin\alpha\ge1/\sqrt2\), this is jointly continuous and uniformly bounded for \(K\in\mathcal K_B,\ |x|\le R,\alpha\in[L/2,L]\). Its reflected upper analogue \(e_{\rho K;\gamma}\) is too.

Let
\[
\ell_{K;\alpha,\gamma}(x)
=1-\max\{B_K(x),n_{K;\alpha}(x),e_{K;\alpha}(x)\}
-\max\{1-A_K(x),n_{\rho K;\gamma}(x),e_{\rho K;\gamma}(x)\},
\tag{SD.8}
\]
and
\[
\boxed{\mathscr V(K,\alpha,\gamma)
=\int_{l_K}^{r_K}\ell_{K;\alpha,\gamma}(x)\,dx.}
\tag{SD.9}
\]
This is **signed**, not silently positive-part ordinary area.

**Theorem SD3 (full-domain joint continuity).** If
\[
K_j\to K,\quad
\alpha_j\to\alpha,\quad\gamma_j\to\gamma,
\qquad \alpha_j,\gamma_j\in[L/2,L],
\]
then
\[
\boxed{
\mathscr V(K_j,\alpha_j,\gamma_j)
\longrightarrow\mathscr V(K,\alpha,\gamma).
}\tag{SD.10}
\]
The result includes complete turns \((\alpha,\gamma)=(L,L)\), genuinely partial turns, degenerate convex hulls, and auxiliary data with arbitrary negative signed fibers.

**Proof.** All four niche and terminal barrier terms in SD.8 are jointly continuous by SD1 and SD.7. For \(W_K>0\), set
\[
x_j(z)=l_{K_j}+zW_{K_j},\qquad
x(z)=l_K+zW_K,\qquad0\le z\le1.
\]
Then \(x_j(z)\to x(z)\) for every z, and SD2 proves convergence of both outer roofs for every z in (0,1). The two maxima and their sum in SD.8 therefore converge **pointwise** in z on (0,1). All terms are uniformly bounded in absolute value: supports are bounded by 3; positive niches are bounded by the inner-corner ordinate \(\eta(t)=(h_K(u_t)-1)\sin t+(h_K(v_t)-1)\cos t\), hence at most 8; and the outgoing barrier is bounded by \(\sqrt2(3+1+R)<10\). Thus \(|\ell|\le25\) uniformly. Change variables \(x=x_j(z)\) and apply dominated convergence to
\(
\mathscr V(K_j,\alpha_j,\gamma_j)
=W_{K_j}\int_0^1\ell_{K_j;\alpha_j,\gamma_j}(x_j(z))\,dz.
\)
Since \(W_{K_j}\to W_K\), SD.10 follows. If \(W_K=0\), then \(W_{K_j}\to0\) and the same uniform bound gives \(|\mathscr V(K_j,\alpha_j,\gamma_j)|\le25W_{K_j}\to0=\mathscr V(K,\alpha,\gamma)\). \(\square\)

**Corollary SD4 (compact attainment of the exact original-motion signed program).** The product
\(
\mathcal K_B\times[L/2,L]^2
\)
is compact (Blaschke selection for nonempty compact convex subsets of a fixed compact box, or Arzelà–Ascoli applied to their uniformly Lipschitz support functions). The continuous \(\mathscr V\) therefore **attains a global maximum**:
\[
\boxed{
\exists(K_{\max},\alpha_{\max},\gamma_{\max})
\text{ with }
\mathscr V(K_{\max},\alpha_{\max},\gamma_{\max})
=\sup_{K,\alpha,\gamma}\mathscr V.
}\tag{SD.11}
\]
By the already audited [GA.21 original-motion equivalence](original-motion-global-bridge-gate0-audit.md), the global signed maximum value equals the actual unrestricted sofa maximum. This does **not** imply K_max itself is an actual sofa hull unless an admission repair is applied; OS2 provides such a repair without preserving its geometry. No auxiliary one-turn weighted-optimality or curvature condition is imported into SD4.

## 4. Smooth positive-curvature auxiliary hulls are **value dense**

**Lemma SD5 (smooth support approximation inside the fixed box).** For every \(K\in\mathcal K_B\) there is a sequence of compact strictly convex
\(K_j\subset\operatorname{int}B\), each with a \(C^\infty\) support function satisfying
\[
\boxed{h_{K_j}+h_{K_j}''>0\quad\text{at every normal angle},\qquad
K_j\to K\text{ in Hausdorff distance}.}\tag{SD.12}
\]

**Proof.** First contract K toward the fixed interior point \(c=(0,1/2)\):
\(K^{(j)}=(1-1/j)K+(1/j)\{c\}\).
It has distance at least \(1/(2j)\) from the horizontal top and bottom of B and at least \(R/j\) from its vertical sides. Its support function is the convex-body support
\(
h^{(j)}=(1-1/j)h_K+(1/j)c\cdot u_\theta.
\)
Take a smooth nonnegative normalized approximate-identity kernel on the circle and convolve \(h^{(j)}\) in the angular variable, with kernel width so small that the resulting support function differs from \(h^{(j)}\) in sup norm by less than \(1/(8j)\).

Convolution preserves the support-function convexity measure:
distributionally,
\(
(h^{(j)}*\varphi_j)+(h^{(j)}*\varphi_j)''
=(h^{(j)}+h^{(j)''})*\varphi_j\ge0.
\)
Thus the convolution is a \(C^\infty\) genuine support function (equivalently a Minkowski average of infinitesimally rotated copies of \(K^{(j)}\)); its corresponding convex body differs in Hausdorff distance by less than \(1/(8j)\). Add a centered disk of radius \(1/(8j)\) by adding that constant to the support; its curvature density becomes **strictly positive everywhere**. The total Hausdorff perturbation from the contracted K is less than \(1/(4j)\), within the original \(1/(2j)\) box margin. The resulting strictly convex smooth K_j lies in the interior of B and tends to K. \(\square\)

**Theorem SD6 (the exact sharp theorem needs to be proved on smooth hulls ONLY).** Put
\[
\mathcal K_B^{\infty,+}
=\{K\subset\operatorname{int}B:
h_K\in C^\infty,\ h_K+h_K''>0\}.
\]
Then, **with the true original-motion two-angle objective**,
\[
\boxed{
\sup_{\substack{K\in\mathcal K_B\\
\alpha,\gamma\in[L/2,L]}}
\mathscr V(K,\alpha,\gamma)
=
\sup_{\substack{K\in\mathcal K_B^{\infty,+}\\
\alpha,\gamma\in[L/2,L]}}
\mathscr V(K,\alpha,\gamma).
}\tag{SD.13}
\]
The analogous equality holds at fixed \(\alpha=\gamma=L\) for the complete-turn signed objective \(\mathscr S(K)\). In particular:

> A sharp upper proof \(\mathscr V(K,\alpha,\gamma)\le M\) for **every smooth strictly convex auxiliary hull** \(K\in\mathcal K_B^{\infty,+}\), with all two terminal angles retained, implies the identical inequality for **every nonsmooth, degenerate or incompatible convex K in B**, and therefore for every original physical ambidextrous sofa by GA.21.

**Proof.** Inclusion gives one inequality. Given any arbitrary K, select the approximating K_j from SD5, keep \(\alpha,\gamma\) fixed, apply SD3 to obtain \(\mathscr V(K_j,\alpha,\gamma)\to\mathscr V(K,\alpha,\gamma)\), and take suprema. The same argument works for \((L,L)\) alone. \(\square\)

**Boundary:** Smooth approximants are not required to be actual hulls of feasible sofas; indeed some may acquire empty fibers or lose original extreme points after canonical deletion. That is precisely why this result is formulated for the **signed auxiliary domain** and justified by Gate 0's exact value equivalence. Applying SD6 to the **ordinary positive-part area of arbitrary K without the pinching correction** would not be the same statement.

## 5. What Gate 1 still needs

The global full-turn loss target remains
\[
\boxed{
\int_I[\max(d_V,n_-)+\max(d_U,n_+)]dx\ge W-M.
}
\]
By SD6 it is enough to prove this for **all** \(C^\infty\) strictly convex auxiliary hulls \(K\in\mathcal K_B^{\infty,+}\), with **no upper bound on their positive curvature density**. The full original-motion target with actual outgoing strips has the same smooth-hull sufficiency.

This eliminates the necessity of analyzing singular source curvature atoms/edges as *separate input cases in a global inequality proof*. It does **not** eliminate high smooth curvature spikes, changing active ray contacts, clipped niches, negative fibers or true partial terminal angles. There is **no positive-value theorem** in this note, and neither Gate 1 nor Gate 2 is marked passed.

No CI, Lean/Lake compilation, random finite-area certificate, or a claim of unrestricted Romik optimality occurs. The statements are analytic and subject to independent mathematical review.
