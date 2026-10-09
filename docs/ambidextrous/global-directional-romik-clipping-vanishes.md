# Global **first-order** Romik calibration along every unit-height Minkowski chord: the clipping credit is cubically small

**Date:** October 9, 2026. **Scope:** This is a sharp-reference, but **globally directional**, geometric theorem: the perturbation endpoint is **any** compact convex hull of vertical span exactly one in a fixed bounded box, not merely a smooth or Hausdorff-near reference hull and not merely a specified face/contact class. The positive clipping credit in the exact two-handed signed area identity is **\(O(\lambda^{3/2})\)** on the entire Minkowski chord from Romik's reference hull. There is no assumption that the interpolated hull is itself an admissible sofa hull, has nonempty fibers, or retains any of Romik's active contacts.

Combining the new unconditional clipping estimate with the branch's **self-reviewed** [WV2 sharp weighted one-cap inequality](one-turn-weighted-value.md) gives a **global one-sided first-variation inequality** for the signed *two-handed full-turn* area functional: Romik has no positive first-order direction toward **any** unit-height hull, even an asymmetric far competitor with opposite-end top/bottom faces. This is much wider in directional scope than the local frozen-ray calibration. **It is not a proof of global optimality**: first-order stationarity does not imply a global maximum without an additional comparison such as the explicitly stated **star-concavity** inequality. The existing [fixed-height signed-concavity problem](signed-joint-convex-domain-global-value.md) remains open. Original partial terminal turns also remain open.

The central geometric proof, Sections 1–4b, depends only on the reference support bounds from [RH.7](romik-horizontal-misalignment-sharp-bound.md), general support-function geometry, and Fubini. It does **not** depend on WV2's longer variational proof chain.

## 1. A Minkowski chord toward an arbitrary hull, with no support-pattern restrictions

Normalize Romik's reference hull \(K_*\subset\mathbb R\times[0,1]\) with horizontal projection \(I_*=[-m,m]\), \(m>1\), common top/bottom face
\[
F_*=[-b,b],\qquad b=m/2,
\]
and reference *downward convex upper cap* \(U_*\). Let \(n_*(x)\) be its **complete** positive lower-turn niche roof. The reference curvature and endpoint analysis in [RH.5–RH.7](romik-horizontal-misalignment-sharp-bound.md) gives the **whole-continuum** inequalities
\[
\boxed{
f_*(t)-1\le b\cos t,\qquad
g_*(t)-1\le b\sin t,
\quad 0<t<\pi/2,
}\tag{MC.1}
\]
where \(f_*(t)=h_{U_*}(\cos t,\sin t)\) and \(g_*(t)=h_{U_*}(-\sin t,\cos t)\). The first is RH.7; the second follows by horizontal reflection of \(U_*\). Moreover
\[
\boxed{0\le n_*(x)\le(b-|x|)_+,\qquad
\operatorname{supp}n_*\subseteq[-b,b].}\tag{MC.2}
\]
The absolute-value bound is literal for all real \(x\), not a claim that every individual reference forbidden roof is nonnegative.

Let \(B=[-R,R]\times[0,1]\) with \(R>b\) contain \(K_*\), and let **arbitrary** nonempty compact convex \(K\subseteq B\) have exact vertical projection \([0,1]\). It may be asymmetric, nonsmooth, have point or separated opposite-end faces, large curvature atoms, or be completely incompatible with the two turning motions. For \(0\le\lambda\le1\) put
\[
\boxed{K_\lambda=(1-\lambda)K_*+\lambda K.}\tag{MC.3}
\]
Every \(K_\lambda\) has vertical span exactly one. Write \(U,V\) for the downward upper and vertically reflected lower caps associated to \(K\). The corresponding caps of the interpolant are precisely
\[
\boxed{U_\lambda=(1-\lambda)U_*+\lambda U,\qquad
V_\lambda=(1-\lambda)U_*+\lambda V.}\tag{MC.4}
\]
To check this, observe that downward filling commutes with Minkowski interpolation for convex sets contained in \(0\le y\le1\): the upper roof of the sum is the supremum of the interpolated upper boundary heights at the corresponding interpolated abscissae, and every height below that roof is supplied by the downward-filled factors. Vertical reflection \(\rho(x,y)=(x,1-y)\) also commutes with a convex combination whose coefficients sum to one.

Denote their convex upper roofs by \(A_{U_\lambda},A_{V_\lambda}\), their **complete** niche roofs by \(n_{U_\lambda},n_{V_\lambda}\), and their common horizontal projection by \(I_\lambda\). Put \(d_{U_\lambda}=1-A_{U_\lambda}\) and \(d_{V_\lambda}=1-A_{V_\lambda}\). All these quantities are nonnegative.

## 2. A precise moving-face overlap gate: clipping is confined to \(O(\lambda)\) of the two reference face endpoints

For **any** normalized downward cap \(C\) of horizontal projection \([l_C,r_C]\) and height one, its outer support satisfies
\[
\boxed{
h_C(u_t)-1\le r_C\cos t,\qquad
h_C(v_t)-1\le-l_C\sin t
}\tag{MC.5}
\]
for \(0<t<\pi/2\). Indeed \(h_C(u_t)\le r_C\cos t+\sin t\), \(h_C(v_t)\le-l_C\sin t+\cos t\), and \(\sin t,\cos t\le1\).

Let \([l_U,r_U]\) and \([l_V,r_V]\) be the projections of U,V (both are the same interval as K, but we preserve labels to make the two independent pairings clear), and let their top faces have nonempty abscissa intervals \([a_U,b_U]\) and \([a_V,b_V]\).

Minkowski linearity of the supports, MC.1, and MC.5 give for **every real angle**
\[
\begin{aligned}
h_{U_\lambda}(u_t)-1
&\le [(1-\lambda)b+\lambda r_U]\cos t,\\
h_{U_\lambda}(v_t)-1
&\le -[(1-\lambda)(-b)+\lambda l_U]\sin t.
\end{aligned}\tag{MC.6}
\]
Any **positive-height forbidden quadrant point** \((x,y)\) has \(y\ge0\) and obeys both strict inner inequalities. From MC.6 this forces
\[
\boxed{
\operatorname{supp}_x N(U_\lambda)
\subseteq J_{U,\lambda}:=
[(1-\lambda)(-b)+\lambda l_U,\ 
 (1-\lambda)b+\lambda r_U].
}\tag{MC.7}
\]
The same bound holds for V_\lambda, with l_V,r_V. This is an exact **whole-angle** niche-projection bound valid for every K, not a statement about which moving-wall contacts are active.

On the other hand, the Minkowski sum of the exposed **top face intervals** is the exposed top face interval:
\[
\boxed{
F^{{\rm top}}(V_\lambda)
=[(1-\lambda)(-b)+\lambda a_V,\ 
  (1-\lambda)b+\lambda b_V],
}\tag{MC.8}
\]
and \(d_{V_\lambda}(x)=0\) throughout it. Thus
\[
\boxed{
\left|\{x:n_{U_\lambda}(x)>0,\
                d_{V_\lambda}(x)>0\}\right|
\le\lambda\big[(a_V-l_U)_++(r_U-b_V)_+\big].
}\tag{MC.9}
\]
Every possible x on the left occurs within \(2R\lambda\) of the **left** reference face endpoint \(-b\), and every possible x on the right within \(2R\lambda\) of \(b\). The same estimates with U,V exchanged hold for \(n_{V_\lambda}\) versus \(d_{U_\lambda}\). **No compatibility assumption on K is needed**: the statement is about the exact moving top faces and all positive inner-ray quadrants.

## 3. Universal \(O(\sqrt\lambda)\) niche-roof control near those endpoints

The bound MC.9 gives small **width** for the overlap, but an area estimate also needs to control its **height**.

Because \(U,V,K_*\subseteq B\), their support functions are uniformly Lipschitz in angular direction, with a bound depending only on R. The same holds for their Minkowski combinations. Their inner-corner ordinates
\[
\eta_C(t)=(h_C(u_t)-1)\sin t+(h_C(v_t)-1)\cos t
\]
are therefore uniformly Lipschitz in t. The exact top-height normalization gives
\[
\eta_C(0)=\eta_C(\pi/2)=0.
\]
Consequently the entire one-angle forbidden tent for t within angular distance \(\delta\) of **either endpoint** has height at most \(L_R\delta\), for a constant \(L_R\) independent of K,\lambda.

For \(\delta\le t\le\pi/2-\delta\), Minkowski linearity and the fixed box give a uniform support difference
\[
\|h_{U_\lambda}-h_{U_*}\|_\infty\le C_R\lambda,
\]
and the two rationally defined wall-height fractions have denominators at least \(\sin\delta\). Therefore their pointwise min and its angular supremum differ from the reference by at most \(C_R\lambda/\sin\delta\).

Since the complete positive roof is the maximum of zero and the interior/endpoint suprema, choosing \(\delta=\sqrt\lambda\) yields, for \(0<\lambda\) sufficiently small,
\[
\boxed{
n_{U_\lambda}(x)
\le n_*(x)+C'_R\sqrt\lambda
\quad\text{for **all** real }x.
}\tag{MC.10}
\]
The identical bound holds for V_\lambda. No claim about convergence of individual active-angle selectors is required.

On either narrow overlap strip from MC.9, MC.2 gives \(n_*(x)\le2R\lambda\). Hence
\[
\boxed{
n_{U_\lambda}(x),n_{V_\lambda}(x)
\le C''_R\sqrt\lambda
\quad\text{at every abscissa contributing to clipping.}
}\tag{MC.11}
\]

## 4. **Unconditional theorem:** the entire positive full-two-turn clipping credit is \(O(\lambda^{3/2})\)

Recall the actual positive two-cap clipping correction
\[
\boxed{
G(U_\lambda,V_\lambda)=\int_{I_\lambda}
\big[\min(n_{U_\lambda},d_{V_\lambda})
+\min(n_{V_\lambda},d_{U_\lambda})\big]dx.
}\tag{MC.12}
\]
It counts **exactly** the inner niche material that lies outside the *other* cap's roof. It is not the empty-fiber positive-part correction.

**Theorem MC1 (global-directional sublinear clipping).** There exist uniform constants \(\lambda_R>0\), \(C_R<\infty\), depending only on the containing rectangle B and the **fixed reference** K*, such that for **every** compact convex height-one K⊂B and every \(0<\lambda<\lambda_R\),
\[
\boxed{0\le G(U_\lambda,V_\lambda)\le C_R\lambda^{3/2}.}\tag{MC.13}
\]
Consequently
\[
\boxed{\lim_{\lambda\downarrow0}
G(U_\lambda,V_\lambda)/\lambda=0}
\]
**uniformly in the far endpoint K**.

**Proof.** The two integrands vanish outside the overlap sets of MC.9 and its exchanged version, whose **combined ordinary horizontal measure** is \(O_R(\lambda)\). On their support, MC.11 bounds each niche height by \(O_R(\sqrt\lambda)\). Since every integrand is nonnegative and bounded above by the corresponding niche height, Fubini gives MC.13. \(\square\)

The key geometric mechanism is **not** reference contact-pattern stability. A Minkowski interpolation from a height-one reference with a positive horizontal top face leaves an almost-full common face for the two independent cap directions, whereas any possible protrusion of the complete swept inner-wall niche past that face is at most **linearly narrow**. Its height tends to zero uniformly. This controls exactly the clipping error that invalidated naive addition of the two weighted one-turn values.

### A fully explicit uniform bound in the project's fixed search box

The argument does not rely on unspecified uniformity constants. For the [OS1 fixed hull search box](original-motion-signed-convex-domain.md)
\[
B=[-5/2,5/2]\times[0,1],\qquad b=m/2<1,
\]
the following concrete estimate is valid:
\[
\boxed{
0\le G(U_\lambda,V_\lambda)\le360\,\lambda^{3/2}
\quad\text{for every }K\subseteq B\text{ of vertical span one,
and }0<\lambda\le1/16 .
}\tag{MC.13a}
\]

Here are all constants. Every upper-cap support (including U*,U,V and their interpolations) has \(|h|\le3\) and angular Lipschitz constant at most \(3\), because every generating point lies in B and has norm less than \(3\). Consequently its inner-corner height \(\eta(t)\) is 14-Lipschitz and vanishes at both endpoints, so all endpoint-angle tents have roof at most \(14\delta\) for angles within \(\delta\) of either endpoint. The support difference from U* is at most \(6\lambda\); for angles between \(\delta\) and \(L-\delta\), with \(\sin\delta\ge\delta/2\), the change in each wall-height fraction is at most \(12\lambda/\delta\). Choose \(\delta=\sqrt\lambda\le1/4\), giving
\[
n_{U_\lambda}(x),n_{V_\lambda}(x)
\le n_*(x)+14\sqrt\lambda
\quad\text{for every real }x.
\tag{MC.13b}
\]
Each overlap term in MC.12 occupies at most \(4R\lambda=10\lambda\) of horizontal width, and lies at distance at most \((R+b)\lambda<\tfrac72\lambda\) from one of the original reference face endpoints. Thus the triangular reference bound MC.2 makes
\(n_*(x)\le\tfrac72\lambda\) on these strips. At each contributing abscissa,
\[
n_{U_\lambda},n_{V_\lambda}
\le14\sqrt\lambda+\tfrac72\lambda
\le\tfrac{35}{2}\sqrt\lambda
<18\sqrt\lambda.
\]
There are **two** possible clipping terms, of combined horizontal measure at most \(20\lambda\). Integrate their pointwise height bound to obtain \(G\le20\lambda\cdot18\sqrt\lambda=360\lambda^{3/2}\).

This is a deliberately conservative **all-angle, all-hull** geometric certificate, not a claimed sharp bound on G or the area of any sofa.

## 4b. **Strict reference curvature improves the global rate to \(O(\lambda^3)\)**

The square-root-height bound in MC.13 is deliberately generic: it uses only Lipschitz continuity of arbitrary supports. Romik's reference satisfies a **strictly stronger terminal quadratic wall-margin**. This improves the clipping credit by an entire factor \(\lambda^{3/2}\), *uniformly over every far endpoint hull*.

Set
\[
\boxed{\kappa=\frac7{400}>0.}
\]
In every smooth open quarter of the reference support the curvature densities satisfy
\[
0\le f_*+f_*''\le\frac{393}{400}=1-\kappa,\qquad
0\le g_*+g_*''\le\frac{393}{400}=1-\kappa.
\tag{MC.18}
\]
Indeed the two terminal phases have densities \(0\) or \(1/2\), while the middle phase has densities bounded by \(3R_0/4<3(131/100)/4=393/400\), by [RH.2–RH.3](romik-horizontal-misalignment-sharp-bound.md). The reference pieces join in \(C^1\) at their switching angles, so no curvature atoms are omitted.

Let
\[
e_g(t)=1+b\sin t-g_*(t),\qquad
e_f(t)=1+b\cos t-f_*(t).
\]
The exact endpoint value/derivative conditions are
\[
e_g(0)=e_g'(0)=0,\qquad
e_f(L)=e_f'(L)=0,\quad L=\pi/2.
\]
Solving the forced scalar support ODE using the strictly positive Green kernels, MC.18 gives
\[
\boxed{
\begin{aligned}
e_g(t)&=\int_0^t\sin(t-s)(1-\rho_g(s))\,ds
\ge\kappa(1-\cos t),\\
e_f(t)&=\int_t^L\sin(s-t)(1-\rho_f(s))\,ds
\ge\kappa(1-\sin t).
\end{aligned}}\tag{MC.19}
\]

**Theorem MC3 (uniform cubic clipping, all unit-height hull directions).** In the *fixed original-motion hull search box* \(B=[-5/2,5/2]\times[0,1]\), for every nonempty compact convex \(K\subseteq B\) with vertical span exactly one,
\[
\boxed{
0\le G(U_\lambda,V_\lambda)\le
500000\,\lambda^3
\qquad(0<\lambda\le 1/10000).
}\tag{MC.20}
\]
No curvature, smoothness, feasibility, horizontal-face order, or contact-chart assumption is placed on the **arbitrary target K**.

**Proof.** By MC.9, each clipping term is supported on at most two short horizontal intervals about \(x=\pm b\). Across either interval,
\[
\boxed{|x+b|\le\tfrac72\lambda\quad\text{(left)},\qquad
|x-b|\le\tfrac72\lambda\quad\text{(right)}.}
\tag{MC.21}
\]
Each clipping term has *total* horizontal support measure at most \(10\lambda\), by the root-box extent \(R=5/2\).

First take a clipping abscissa near the **left endpoint**, \(|x+b|\le 7\lambda/2\). For any one of the interpolated caps \(C_\lambda=(1-\lambda)U_*+\lambda C\), with lower endpoint \(l_C\in[-5/2,5/2]\), the arbitrary-cap rectangle support bound MC.5 and the strict reference gap MC.19 give
\[
\begin{aligned}
h_{C_\lambda}(v_t)-1+x\sin t
&\le A\sin t-k(1-\cos t),\\
A&=(1-\lambda)(x+b)+\lambda(x-l_C),\\
k&=(1-\lambda)\kappa+\lambda\ \ge\ \kappa/2=7/800,
\end{aligned}\tag{MC.22}
\]
where \(|A|\le9\lambda\) follows from \(|x+b|\le7\lambda/2\), \(|x-l_C|\le5\) and \(\lambda\le1\).

The second-wall roof is the left-hand side of MC.22 divided by \(\cos t>0\). If it is positive, then necessarily \(A>0\) and
\[
\tan(t/2)<A/k\le9\lambda/k\le \frac9{10000}\frac{800}7<\frac12.
\]
Using \(\tan t=2\tan(t/2)/(1-\tan^2(t/2))\), **every** possible positive second-wall roof at that x satisfies
\[
\frac{h_{C_\lambda}(v_t)-1+x\sin t}{\cos t}
\le A\tan t
\le\frac{8A^2}{3k}
\le\frac{216}{k}\lambda^2.
\tag{MC.23}
\]
But the *full physical inner-quadrant roof* is the **minimum** of the two wall roofs. Hence the complete **all-angle** niche height at this left clipping abscissa is bounded by \(216\lambda^2/k\).

At a clipping abscissa near the **right endpoint**, \(|x-b|\le7\lambda/2\), the symmetric calculation uses the *first* wall and the second strict reference gap:
\[
h_{C_\lambda}(u_t)-1-x\cos t
\le A'\cos t-k(1-\sin t),\qquad
A'=(1-\lambda)(b-x)+\lambda(r_C-x)\le9\lambda.
\]
If the first-wall roof is positive then
\(\tan((L-t)/2)<A'/k<1/2\), and therefore its height, after dividing by \(\sin t\), is at most \(216\lambda^2/k\) by the same calculation.

Thus on *both* clipping intervals, **each** whole-turn niche satisfies
\[
\boxed{n_{C_\lambda}(x)\le\frac{216}{k}\lambda^2}
\tag{MC.24}
\]
without tracking any maximizing angle. Each clipping integrand is bounded by that niche roof. The two clipping terms together have horizontal support measure at most \(20\lambda\). Thus
\[
G(U_\lambda,V_\lambda)
\le20\lambda\frac{216}{k}\lambda^2
\le\frac{4320\cdot800}{7}\lambda^3
<500000\lambda^3.
\]
The displayed estimate holds for every angle \(t\in(0,L)\); it does not discretize or assume any particular wall exposure. \(\square\)

**Consequences.** The positive ordinary two-turn clipping credit now vanishes to **second order as well as first order** along every unit-height Minkowski ray from Romik:
\[
\boxed{G(U_\lambda,V_\lambda)/\lambda^2\longrightarrow0}
\quad\text{uniformly over all height-one }K\subseteq B.
\tag{MC.25}
\]
Taking the branch's separately self-reviewed one-turn inequality WV2 as a dependency strengthens MC.16 to
\[
\boxed{
\mathscr S(K_\lambda)\le M+500000\,\lambda^3
\quad(0<\lambda\le1/10000).
}\tag{MC.26}
\]
This eliminates any **linear or quadratic positive area contribution from cross-handed clipping** in *arbitrary far* hull directions, even those whose top and bottom faces are at opposite ends. **It does not eliminate all such competitors globally**: the overall signed objective could still increase at finite \(\lambda\) because star-concavity MC.17 remains unproved. Nor does MC.26 alone prove that \(\mathscr S\) has an existing nonpositive second derivative, since the one-cap terms may be nonsmooth; it proves the displayed one-sided cubic **upper envelope** only.

## 4c. The cubic exponent is **optimal**, even toward a strict opposite-end-face hull

The upper estimate MC.20 cannot be strengthened to \(o(\lambda^3)\) uniformly over unit-height outer hulls. We give a **single exact convex parallelogram endpoint \(P\)** with positive two-cap clipping of order \(\lambda^3\), and with its top and bottom horizontal faces **strictly at opposite ends**. This is a *sharpness witness for the clipping bound*, **not** an ambidextrous sofa exceeding \(M\) or a proof that the interpolated hull is a feasible sofa hull.

Put \(b=m/2\) as before, and choose the rational values
\[
d=\frac32,\qquad w=\frac34,\qquad
\boxed{
P=\operatorname{conv}\{(b-w,0),(b,0),(b+d,1),(b+d-w,1)\}.
}\tag{MC.27}
\]
Its horizontal projection is \([b-w,b+d]\) of width \(w+d=9/4\), with top face \([b+d-w,b+d]\times\{1\}\) and bottom face \([b-w,b]\times\{0\}\). Since \(d-w=3/4>0\), these are strictly disjoint; each has length \(w=3/4<1\). Moreover \(b<117/200<1\) makes \(P\subset[-5/2,5/2]\times[0,1]\). Thus this far endpoint has precisely the **positive opposite-end-face geometry** relevant to the still-unproved full-turn class.

Let \(K_\lambda=(1-\lambda)K_*+\lambda P\), \(U_\lambda\) its downward upper cap and \(V_\lambda\) its vertically reflected lower cap. Consider the thin horizontal interval
\[
\boxed{b\le x\le b+\lambda d.}\tag{MC.28}
\]
This lies just **outside the right top face of \(V_\lambda\)** and **inside** the right top-face endpoint \(b+\lambda d\) of \(U_\lambda\).

### Two exact circular tails from the same terminal support directions

For \(t\) sufficiently close to \(L=\pi/2\), the rightmost top vertices of the two factor caps remain their maximizers in the \(u_t=(\cos t,\sin t)\) direction. The exact reference terminal-phase support [RH.2] is
\[
f_*(t)=b\cos t+\tfrac12\sin t+\tfrac12.
\]
The upper cap of the parallelogram has \(f_P(t)=(b+d)\cos t+\sin t\), while the reflected lower cap of the same parallelogram has
\(f_{\rho P}(t)=b\cos t+\sin t\) for \(\tan t>d\). Consequently their interpolated upper supports on a fixed terminal neighborhood of \(L\) are
\[
\boxed{
\begin{aligned}
f_{U_\lambda}(t)
&=(b+\lambda d)\cos t
 +\frac{1+\lambda}{2}\sin t+\frac{1-\lambda}{2},\\
f_{V_\lambda}(t)
&=b\cos t
 +\frac{1+\lambda}{2}\sin t+\frac{1-\lambda}{2}.
\end{aligned}}\tag{MC.29}
\]
Set
\[
r_{\rm in}=(1+\lambda)/2,\quad
r_{\rm out}=(1-\lambda)/2,\quad
q_r(z):=r-\sqrt{r^2-z^2}\quad(0\le z<r).
\]

The **true convex outer roof** of \(V_\lambda\) just to the right of its exposed top-face endpoint \(b\) is the circular arc generated by its actual supporting directions MC.29:
\[
\boxed{
d_{V_\lambda}(b+v)=1-A_{V_\lambda}(b+v)
=q_{r_{\rm out}}(v)
\quad(0\le v\le\lambda d,\ \lambda\text{ sufficiently small}).
}\tag{MC.30}
\]
Indeed the support \(f_{V_\lambda}\) has its outward contact locus
\[
(x,y)=\left(
 b+r_{\rm out}\cos t,\
 \frac{1+\lambda}{2}+r_{\rm out}\sin t
\right);
\]
as \(t\uparrow L\) this traces the entire near-top outer circular flank and has no skipped outer support directions.

For \(x=b+\lambda d-u\), \(0\le u\le\lambda d\), the **first inner-wall** roof of \(U_\lambda\) at \(t=L-\theta\) is exactly
\[
\frac{f_{U_\lambda}(t)-1-x\cos t}{\sin t}
=u\tan\theta-r_{\rm in}(\sec\theta-1).
\tag{MC.31}
\]
Choose \(\theta=\arcsin(u/r_{\rm in})\). It lies in Romik's unchanged terminal support phase for all sufficiently small \(\lambda\). At this angle the displayed first-wall roof is exactly \(q_{r_{\rm in}}(u)\). The companion second-wall roof is **strictly above** it for small \(\lambda\): uniformly over this shrinking angle/abscissa range its numerator tends to the positive reference quantity
\[
g_*(L)-1+b=m-1+b=3m/2-1>0,
\]
whereas \(q_{r_{\rm in}}(u)=O(\lambda^2)\). Therefore the *minimum of the two actual inner-wall roofs* is the first-wall value at this chosen angle, and the complete all-angle niche satisfies
\[
\boxed{
n_{U_\lambda}(b+\lambda d-u)\ge q_{r_{\rm in}}(u).
}\tag{MC.32}
\]
This is a valid **lower bound on the true union of all moving inner-wall quadrants**, not a frozen-active-contact assumption.

### Exact positive cubic clipping lower bound

Restrict the first ordinary clipping integrand in MC.12 to the interval MC.28, insert MC.30–MC.32, and substitute \(x=b+\lambda s\):
\[
\begin{aligned}
G(U_\lambda,V_\lambda)
&\ge\int_b^{b+\lambda d}
 \min(n_{U_\lambda}(x),d_{V_\lambda}(x))\,dx\\
&\ge\lambda\int_0^d
 \min\left\{
 q_{r_{\rm in}}(\lambda(d-s)),
 q_{r_{\rm out}}(\lambda s)
 \right\}ds .
\end{aligned}\tag{MC.33}
\]
For every \(s\in[0,d]\), the *exact rationalized square-root identity*
\[
q_r(z)=\frac{z^2}{r+\sqrt{r^2-z^2}}
\]
and \(r_{\rm in},r_{\rm out}\to1/2\) imply the **uniform** limits
\[
\frac{q_{r_{\rm in}}(\lambda(d-s))}{\lambda^2}
\longrightarrow(d-s)^2,\qquad
\frac{q_{r_{\rm out}}(\lambda s)}{\lambda^2}
\longrightarrow s^2.
\]
Integrate the minimum of the two continuous limits to get
\[
\boxed{
\liminf_{\lambda\downarrow0}
\frac{G(U_\lambda,V_\lambda)}{\lambda^3}
\ge\int_0^{3/2}\min\{(3/2-s)^2,s^2\}\,ds
=\frac{(3/2)^3}{12}
=\frac9{32}>0.
}\tag{MC.34}
\]
**Theorem MC4 (optimal cubic exponent in the universal height-one class).** MC3's cubic estimate is of the **best possible power** over *all* unit-height convex-hull directions, **even with the far endpoint restricted to strict positive opposite-end top/bottom faces**. No uniform \(G=o(\lambda^3)\) estimate is possible on the stated full convex search box.

The example isolates exactly how **face misalignment** creates a tiny but real positive clipping credit: one inner circular ray tail extends beyond the other cap's horizontal top face, while that other cap's circular outer flank supplies an equally quadratic obstacle. Their overlap has horizontal width \(O(\lambda)\) and two quadratic heights \(O(\lambda^2)\), producing the sharp cubic exponent.

This does **not** exhibit a sofa with area \(>M\). The far parallelogram and its interpolation are admissible as **convex outer hull inputs** to the signed objective; they are not claimed to be actual feasible common sofa hulls. Full-turn sharp optimality still requires the global finite-\(\lambda\) comparison MC.17 or another valid global calibration.

## 5. A global directional first variation — conditional on the written one-cap sharp theorem

Define the **signed** full-two-handed fiber value for arbitrary compact convex K by
\[
\mathscr S(K)=\int_{I_K}
\left[\min(A_U(x),1-n_V(x))
-\max(1-A_V(x),n_U(x))\right]dx .
\tag{MC.14}
\]
For an arbitrary interpolated K, some vertical fibers may be empty: their negative *signed lengths* are deliberately **retained**, not turned into ordinary area.

The two-cap algebra is an exact pointwise identity, irrespective of empty fibers:
\[
\boxed{
\mathscr S(K)=\Psi(U)+\Psi(V)+G(U,V),\quad
\Psi(C)=|C|-|N(C)|-\frac12|I_K|.
}\tag{MC.15}
\]
Indeed one uses \(\min(A,1-n)=A-n+\min(n,1-A)\) and \(\max(1-A,n)=(1-A)+n-\min(n,1-A)\). Neither ordinary-area connectedness nor admissibility is inserted.

The written [WV2](one-turn-weighted-value.md) claims, in a long self-reviewed dependency chain, that **every normalized full-turn downward convex cap** C satisfies
\[
\Psi(C)\le M/2,
\]
with equality at \(U_*\). The cap domain includes every U_\lambda,V_\lambda above, since their top height is one, their horizontal projection is an interval of positive width, and they are downward closed. Accepting that **separately stated** one-turn result, MC.13–MC.15 give
\[
\boxed{
\mathscr S(K_\lambda)\le M+C_R\lambda^{3/2},
\qquad
\limsup_{\lambda\downarrow0}
\frac{\mathscr S(K_\lambda)-M}{\lambda}\le0
}\tag{MC.16}
\]
for **every** unit-height convex K⊂B. This is a nonpositive **global Minkowski directional upper derivative** at Romik, without requiring the derivative to exist.

**Dependency warning:** MC1 and the structural bound MC.13 are unconditional elementary convex geometry given the exact reference construction. MC.16 is **conditional on the branch's self-reviewed WV2 sharp weighted one-cap theorem**; it is not independently refereed or kernel-checked. The new argument does not reprove WV2.

## 6. Exactly one still-open global **star-concavity** inequality would finish the full-turn value

Here is a precise global route to falsify or prove, rather than another sequence of increasingly narrow candidate-local exclusions.

**Proposition MC2 (star-concavity suffices, conditional).** Suppose, in addition to WV2, the following comparison held for every **unit-height** convex K in B and every \(0\le\lambda\le1\):
\[
\boxed{
\mathscr S((1-\lambda)K_*+\lambda K)
\ \ge\
(1-\lambda)M+\lambda\mathscr S(K).
}\tag{MC.17, **UNPROVED**}
\]
This asks only for **star-concavity of the *signed* full-turn objective from Romik**, not for joint concavity in terminal angles and not for global concavity between every pair of arbitrary hulls.

Then MC.16 would imply
\[
\mathscr S(K)\le M+
\limsup_{\lambda\downarrow0}
\frac{\mathscr S(K_\lambda)-M}{\lambda}\le M.
\]
By the already self-reviewed [SJ1 exact signed/full-turn value equivalence](signed-joint-convex-domain-global-value.md), together with the area-convergent **unit-height opposite-face approximation** [PD2](full-turn-positive-face-density.md), that would prove the **sharp *full-conventional-two-turn* supremum** equals M.

**What is not done:** MC.17 has **not been proved**. The signed objective is known to fail global Minkowski concavity when vertical scale varies ([SG](signed-global-scale-concavity-obstruction.md)); that counterexample does not settle the exact unit-height star-concavity question. Sparse numerical convex-hull checks are not a theorem and cannot replace a rigorous proof or a counterexample. This route would also still leave **original genuinely partial terminal angles**, unless a separate completion/area comparison were established. The global sharp ambidextrous conjecture remains open.

**New mathematical progress:** We have removed a previously nontrivial first-order obstruction across the **entire far-competitor, unit-height hull domain**: the positive clipping interaction cannot contribute a *linear* first-order directional gain from Romik under Minkowski interpolation. Any counterexample to the starred global route must come from **higher-order/nonconcave behavior of the signed joint functional** (or a failure of its earlier one-turn dependency), not a hidden linear clipping credit. This is not a finite class exclusion or a proof that the full global area bound already holds.

No CI, Lean/Lake build, optimization certificate, or claim of a complete proof is made.
