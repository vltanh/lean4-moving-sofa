# Global **first-order** Romik calibration along every unit-height Minkowski chord: the clipping credit is sublinear

**Date:** October 9, 2026. **Scope:** This is a sharp-reference, but **globally directional**, geometric theorem: the perturbation endpoint is **any** compact convex hull of vertical span exactly one in a fixed bounded box, not merely a smooth or Hausdorff-near reference hull and not merely a specified face/contact class. The positive clipping credit in the exact two-handed signed area identity is **\(O(\lambda^{3/2})\)** on the entire Minkowski chord from Romik's reference hull. There is no assumption that the interpolated hull is itself an admissible sofa hull, has nonempty fibers, or retains any of Romik's active contacts.

Combining the new unconditional clipping estimate with the branch's **self-reviewed** [WV2 sharp weighted one-cap inequality](one-turn-weighted-value.md) gives a **global one-sided first-variation inequality** for the signed *two-handed full-turn* area functional: Romik has no positive first-order direction toward **any** unit-height hull, even an asymmetric far competitor with opposite-end top/bottom faces. This is much wider in directional scope than the local frozen-ray calibration. **It is not a proof of global optimality**: first-order stationarity does not imply a global maximum without an additional comparison such as the explicitly stated **star-concavity** inequality. The existing [fixed-height signed-concavity problem](signed-joint-convex-domain-global-value.md) remains open. Original partial terminal turns also remain open.

The central geometric proof, Sections 1–4, depends only on the reference support bounds from [RH.7](romik-horizontal-misalignment-sharp-bound.md), general support-function geometry, and Fubini. It does **not** depend on WV2's longer variational proof chain.

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
