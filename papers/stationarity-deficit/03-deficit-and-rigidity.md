# 3. A deficit identity instead of separate optimality and equality arguments

## 3.1 The elementary Hilbert-space identity

Let \(\mathcal D\) be a convex domain, let \(\Lambda:\mathcal D\to\mathbb R\) be affine, and let \(z_j:\mathcal D\to H_j\) be affine maps into real Hilbert spaces, for \(1\le j\le m\). Define

\[
Q(X)=\Lambda(X)-\tfrac12\sum_{j=1}^m\|z_j(X)\|_{H_j}^2.
\]

The derivative below is the one-sided derivative along the segment from X_* to X; no open ambient domain is needed.

**Proposition 3.1 (exact deficit).** For X,X_* in the domain,

\[
Q(X_*)-Q(X)
=-DQ_{X_*}(X-X_*)+	frac12\sum_j\|z_j(X)-z_j(X_*)\|^2.       \tag{3.1}
\]

**Proof.** Put \(\Delta_j=z_j(X)-z_j(X_*)\). Affineness gives

\[
Q((1-t)X_*+tX)=Q(X_*)+t\left[\Lambda(X)-\Lambda(X_*)-\sum_j\langle z_j(X_*),\Delta_j\rangle\right]
-	frac{t^2}{2}\sum_j\|\Delta_j\|^2.
\]

The bracket is the segment derivative. Set t=1. \(\square\)

If DQ_{X_*}(X-X_*)<=0 for every X, this one identity proves maximality and characterizes equality. It does not eliminate the work of proving that derivative sign.

More precisely, suppose A(K)<=Q(X_K) for a canonical extension X_K, and Q(X_G)=M. Then

\[
M-A(K)=\underbrace{Q(X_K)-A(K)}_{\text{geometric slack}}
+\underbrace{-DQ_{X_G}(X_K-X_G)}_{\text{first-variation slack}}
+\underbrace{\tfrac12\sum_j\|z_j(X_K)-z_j(X_G)\|^2}_{\text{quadratic defect}}.   \tag{3.2}
\]

Under the stated inequalities all three terms are nonnegative. Equation (3.2) is more informative than concavity alone: it displays exactly which information an equality case retains.

## 3.2 Application to Baek's functional

The retained input from Baek, Sections 7.4 and 8.3, is that Q plus its six Mamikon terms is affine on the triple domain \(\mathcal L\). Each Mamikon term is half the squared L2 norm of its tangent displacement. Four terms depend on the cap K; two depend on the auxiliary tail bodies B,D. Supporting-line intersections and outer corners are affine in support functions, so their displacement functions are affine under Minkowski combinations.

Thus the Hilbert spaces in Proposition 3.1 are six L2 spaces on the fixed angular intervals. Integrability is part of the Mamikon representation, not inferred from a zero integral. Write E_cap for the sum of the four cap squared norms and E_tail for the other two. Equation (3.2) becomes

\[
M-A(K)=Q(X_K)-A(K)-DQ_{X_G}(X_K-X_G)
+	frac12E_{\rm cap}(K,G)+	frac12E_{\rm tail}(X_K,X_G).        \tag{3.3}
\]

The area comparison and the derivative sign still come from Baek's geometric construction and first-variation calculation. This section reorganizes those inputs; it does not replace them by an appeal to the completed optimality theorem.

## 3.3 The cap kernel

Put L=pi/2, choose 0<phi<pi/4, and let psi=L-phi. For two normalized right-angle caps K_0,K_1 set

\[
f(t)=h_{K_1}(t)-h_{K_0}(t),\qquad f(L)=0.
\]

Support functions are Lipschitz. Derivatives in the following equations are classical derivatives almost everywhere, and integration is justified by absolute continuity.

For a tangent-intersection term whose target normal is T, the difference of tangent displacements is

\[
\eta(t)=\frac{f(T)-f(t)\cos(T-t)}{\sin(T-t)}-f'(t).           \tag{3.4}
\]

For the outer-corner term it is

\[
\eta(t)=f(t+L)-f'(t).                                       \tag{3.5}
\]

The four cap intervals/targets are

| Interval | Type / target |
| --- | --- |
| (0,phi) | Tangent, T=L |
| (phi,psi) | Outer corner |
| (psi,L) | Tangent, T=pi-phi |
| (L,pi) | Tangent, T=pi |

**Proposition 3.2 (zero-energy cap rigidity).** If all four displacement differences vanish almost everywhere, then K_1 is a horizontal translate of K_0.

**Proof.** A zero tangent difference gives

\[
\sin(T-t)f'(t)+\cos(T-t)f(t)=f(T).
\]

On each compact subinterval avoiding T, the integrating factor 1/sin(T-t) gives the complete solution

\[
f(t)=f(T)\cos(T-t)+b\sin(T-t).                              \tag{3.6}
\]

First take T=pi on (L,pi). Using f(L)=0 gives f(t)=a cos t, where a=-f(pi). Then the third interval has a known target value f(pi-phi) and the known value f(L)=0; (3.6) gives the same formula there. On the middle interval, (3.5) gives f'(t)=-a sin t; matching at psi removes the integration constant. On the first interval (3.6) gives b cos t, and matching at phi forces b=a. Continuity supplies all endpoints.

The upper support functions therefore agree after horizontal translation. A normalized right-angle cap contains the vertical projections of its points onto its bottom segment. Every lower normal is maximized on that segment. Its two endpoints are fixed by h(0) and h(pi), so the lower supports agree as well. Equality of full support functions proves K_1=K_0+(a,0). \(\square\)

The argument identifies the cap, not necessarily both tail bodies separately. It does not claim strict concavity on the whole triple domain.

## 3.4 Quantitative control of the same kernel

The following estimate also checks that no singular endpoint mode was lost in (3.6). Let

\[
a=-f(\pi),\quad F(t)=f(t)-a\cos t,\quad d=L-2\varphi,
\quad E_j=\|\eta_j\|_{L^2(I_j)},\quad E=\sum_{j=1}^4 E_j^2.
\]

Then F(L)=F(pi)=0, and subtracting the translation mode does not change any eta_j.

**Proposition 3.3 (cap coercivity).**

\[
d_H(K_1,K_0+(a,0))^2\le C_\varphi^2 E,
\]

where

\[
C_\varphi^2=\sec^2\varphi\left[L+\varphi\tan^2\varphi+	frac12(L-2\varphi+\tan\varphi)^2\right].    \tag{3.7}
\]

For 0<phi<=1/25, C_phi^2<3.

**Proof.** For a tangent term, (3.4) becomes

\[
\left(\frac{F(t)}{\sin(T-t)}\right)'
=\frac{F(T)}{\sin^2(T-t)}-\frac{\eta(t)}{\sin(T-t)}.           \tag{3.8}
\]

On the fourth interval,

\[
F(t)=-\sin(\pi-t)\int_L^t\frac{\eta_4(s)}{\sin(\pi-s)}ds.
\]

Cauchy-Schwarz gives the exact cancellation

\[
|F(t)|^2\le E_4^2\sin^2(\pi-t)\int_L^t\csc^2(\pi-s)ds
=E_4^2\sin(\pi-t)\cos(\pi-t)\le E_4^2/2.
\]

No division at t=pi occurs. Define A_4=E_4/sqrt(2); continuity extends the estimate to [L,pi].

On the third interval (3.8), with F(L)=0 and T=pi-phi, gives

\[
F(t)=F(T)\frac{\sin(t-L)}{\cos\varphi}
-\sin(T-t)\int_L^t\frac{\eta_3(s)}{\sin(T-s)}ds.
\]

Since sin(T-s)>=cos phi there,

\[
\|F\|_{\infty,[\psi,L]}\le A_3:=\tan\varphi A_4+\sqrt\varphi\sec\varphi E_3.
\]

Integrating F'(t)=F(t+L)-eta_2(t) backward from psi yields

\[
\|F\|_{\infty,[\varphi,\psi]}\le A_2:=A_3+d A_4+\sqrt d E_2.
\]

Finally, F'+tan(t)F=-eta_1 on the first interval, so

\[
\|F\|_{\infty,[0,\varphi]}\le A_1:=\sec\varphi A_2+\sqrt\varphi\sec\varphi E_1.
\]

Here A_1>=A_2>=A_3. Also d+tan phi>=1: its derivative is tan^2 phi-1<=0 on [0,pi/4] and its endpoint value is 1. Consequently A_1>=A_4. Expanding A_1 and applying Cauchy-Schwarz to its four coefficients gives

\[
\|F\|_{\infty,[0,\pi]}^2\le C_\varphi^2 E.
\]

The squared coefficient sum is exactly (3.7). On the lower semicircle, the translated support difference is zero on the left-bottom directions and F(0) cos t on the right-bottom directions. Thus the full support supremum has the same bound. The support-function formula for Hausdorff distance proves the assertion.

For the rational estimate, use cos phi>=1249/1250, tan phi<=2phi, d+tan phi<=L, and pi<22/7. Then

\[
C_\varphi^2\le(1250/1249)^2\left[11/7+4/15625+121/98\right]<3.
\]

The last inequality is checked by clearing positive integer denominators. No numerical maximization of C_phi is needed. \(\square\)

**Corollary 3.4.** Under the geometric upper-bound and first-variation inputs, every K in Baek's domain \(\mathcal K^i\) satisfies

\[
\inf_{a\in\mathbb R}d_H(K,C(G)+(a,0))^2\le6\,[M-A_L(K)].      \tag{3.9}
\]

Indeed (3.3) gives E_cap<=2[M-A_L(K)], and Proposition 3.3 applies. An explicit admissible a is h_{C(G)}(pi)-h_K(pi).

## Limits of the conclusion

Equation (3.9) controls caps already in \(\mathcal K^i\). It does not control the Hausdorff distance of arbitrary moving sofas to G, the continuity of the cap-minus-niche operation, or the sizes of their two monotonization enlargements. Those would require additional estimates. In particular this paper does not infer quantitative stability of the entire moving-sofa problem from cap coercivity alone.

The proof also retains all six L2 integrability hypotheses supplied by the Mamikon formula. The convention that a nonintegrable Bochner integral may be defined as zero cannot produce a spurious equality case.

## Sources

The affine-minus-Mamikon representation, upper-bound domain, and first-variation sign are retained from J. Baek, arXiv:2411.19826v1, Sections 7.4 and 8.1-8.5. The exact expansion, four-equation equality analysis, and explicit coercivity calculation above are supplied as part of this research manuscript. They are not a claim that the uncompiled source has been verified.
