# Exact counterexample to the proposed global concavity of the middle-half one-cap functional

**Status.** The uploaded \`candidate-functionals-package.zip\` (user-supplied, SHA-256 \`a93a2928a527c9fd4efa1228a15a16133ad6c9becfb7fef0ae12f98dc617e491\`) recommends proving the global Minkowski concavity CF5 of the one-cap spatial functional
\[
P_J(U)=\int_{I\setminus J} A_U(x)\,dx-\int_J n_U(x)\,dx,
\qquad J=[l+W/4,r-W/4].
\]
**CF5 is false on the stated convex domain**, including within the narrow range \(2<W<21/10\). The counterexample below is exact pen-and-paper geometry. Its numerical discovery and high-resolution replay were preliminary; neither is a proof premise. The proposed sharp *value* bound \(P_J(U)\le M/2\) is **not** refuted by these low-valued caps and remains a separate open question. Labels CN are local.

The package's geometric SPB enclosure and the elementary fact that concavity plus nonpositive reference directional derivatives would imply global maximality remain valid with their original hypotheses. What fails is the indispensable global concavity premise.

## 1. A Minkowski segment between two elementary triangles

For \(r>0\) put
\[
T_r=\operatorname{conv}\{(-r,0),(r,0),(0,1)\}.
\]
Both \(T_1,T_2\) are normalized height-one downward convex caps: their entire horizontal projection is a segment in their bottom boundary. Define the **Minkowski segment**
\[
U_\lambda=(1-\lambda)T_1+\lambda T_2,\qquad0\le\lambda\le1.
\tag{CN.1}
\]
Minkowski interpolation of supports is exactly affine. For \(0\le\lambda<1/3\), its upper boundary consists of the vertices
\[
(-1-\lambda,0),\quad (-2\lambda,1-\lambda),
\quad(0,1),\quad(2\lambda,1-\lambda),\quad(1+\lambda,0).
\tag{CN.2}
\]
The projection is \(I_\lambda=[-a_\lambda,a_\lambda]\), \(a_\lambda=1+\lambda\), with width \(W_\lambda=2+2\lambda\). Its centered middle-half window is
\[
J_\lambda=[-a_\lambda/2,a_\lambda/2].
\]
For \(\lambda\le1/3\), both exterior quarters lie on the linear lower flanks of the upper roof:
\[
A_\lambda(x)=a_\lambda-|x|\quad (a_\lambda/2\le|x|\le a_\lambda).
\]
Therefore their **exact** integrated area is
\[
\boxed{\int_{I_\lambda\setminus J_\lambda}A_\lambda\,dx
=2\int_{a_\lambda/2}^{a_\lambda}(a_\lambda-x)\,dx
=\frac{(1+\lambda)^2}{4}.}
\tag{CN.3}
\]
The positive quadratic dependence on \(\lambda\) is the prospective concavity obstruction; we next bound the full niche correction rather than dropping it.

## 2. The full niche costs only \(O(\lambda^3)\)

Set \(L=\pi/2\), \(c=\cos t,s=\sin t\), \(0<t<L\). The first and second upper support values of the cap \(U_\lambda\) are
\[
f_\lambda(t)=(1-\lambda)\max(c,s)+\lambda\max(2c,s),
\quad
g_\lambda(t)=(1-\lambda)\max(s,c)+\lambda\max(2s,c).
\]
For \(0<t\le L/2=\pi/4\), \(s\le c\) and \(2c\ge s\), hence
\[
f_\lambda=(1+\lambda)c,\qquad
g_\lambda=c+\lambda(2s-c)_+.
\tag{CN.4}
\]
The canonical forbidden quadrant at angle \(t\) has vertical roof
\[
\min\left(
\frac{f_\lambda-1-xc}{s},
\frac{g_\lambda-1+xs}{c}
\right).
\]
The two bounding lines meet at vertical height
\[
C_\lambda(t)=(f_\lambda-1)s+(g_\lambda-1)c.
\tag{CN.5}
\]
The supremum over x of the minimum of these two opposing-slope lines is \(C_\lambda(t)\). Thus no *positive* niche at angle t occurs if \(C_\lambda(t)\le0\), and in general its vertical height is at most \((C_\lambda(t))_+\).

Put \(t_0=\arctan(1/2)\). For \(t_0\le t\le\pi/4\), \(c\le2/\sqrt5\), \(c+s\ge1\), and \(0\le(2s-c)_+\le s\), so
\[
\begin{aligned}
C_\lambda(t)
&=-(1-c)(c+s)+\lambda[cs+c(2s-c)_+]\\
&\le-(1-2/\sqrt5)+2\lambda cs
\le-(1-2/\sqrt5)+\lambda<0
\end{aligned}
\]
for \(0\le\lambda\le1/16\), since \(1-2/\sqrt5>1/16\).

For \(0<t<t_0\), \(g_\lambda=c\), \(c\ge2/\sqrt5>4/5\), \(1-c=s^2/(1+c)\ge s^2/2\), and \(c+s\ge4/5\). Consequently
\[
\boxed{
C_\lambda(t)
=-(1-c)(c+s)+\lambda cs
\le-\frac25s^2+\lambda s
\le\frac58\lambda^2.}
\tag{CN.6}
\]
Moreover an angle-t forbidden quadrant intersects the baseline y=0 only for
\[
\frac{1-g_\lambda(t)}s <x<
\frac{f_\lambda(t)-1}c,
\]
and in this early regime the endpoints obey
\[
\frac{1-c}{s}\ge0,\qquad
\frac{(1+\lambda)c-1}{c}=\lambda+1-\sec t\le\lambda.
\]
Thus all its positive-height niche points have horizontal abscissae in \((0,\lambda)\).

The cap is symmetric under \(x\mapsto-x\), which exchanges the early and late angle regimes. Therefore every positive niche point over all \(0<t<\pi/2\) lies in \((-\lambda,\lambda)\), and has vertical height at most \(5\lambda^2/8\). The full positive niche \(n_\lambda\), including its **entire** continuous angle supremum, satisfies the *global* estimate
\[
\boxed{0\le N_\lambda:=\int_{J_\lambda}n_\lambda(x)\,dx
\le\frac54\lambda^3
\qquad(0\le\lambda\le1/16).}
\tag{CN.7}
\]
The reference cap \(T_1=U_0\) has no positive niche, and \(N_0=0\). No finite-angle sampling, differentiability of an active niche parameter, or convex-curve regularity assumption is used.

## 3. A strictly positive second difference inside \(2<W<2.05\)

Combine CN.3 and CN.7:
\[
\boxed{
P_{J_\lambda}(U_\lambda)
=\frac{(1+\lambda)^2}{4}-N_\lambda,\qquad
0\le N_\lambda\le\frac54\lambda^3.
}
\tag{CN.8}
\]

Let \(\varepsilon=1/128\) and take
\[
U_-=U_{\varepsilon},\quad
U_0^{\,\mathrm{mid}}=U_{2\varepsilon},\quad
U_+=U_{3\varepsilon}.
\]
The affine definition CN.1 gives the **exact Minkowski midpoint**
\[
U_0^{\,\mathrm{mid}}=\frac12U_-+\frac12U_+.
\]
All three caps have height one, full bottom projection and widths \(2+2\lambda\) in
\[
2+\frac1{64}\le W_\lambda\le2+\frac3{64}<\frac{21}{10}.
\]
Their \(\lambda\)-parameters are at most \(3/128<1/16\), so CN.8 applies. Since \(N_{2\varepsilon}\ge0\),
\[
\begin{aligned}
\frac{P_J(U_-)+P_J(U_+)}2-P_J(U_0^{\,\mathrm{mid}})
&=\frac{\varepsilon^2}{4}
+N_{2\varepsilon}-\frac{N_\varepsilon+N_{3\varepsilon}}2\\
&\ge\frac{\varepsilon^2}{4}
-\frac58(\varepsilon^3+27\varepsilon^3)\\
&=\varepsilon^2\left(\frac14-\frac{35}2\varepsilon\right)
=\boxed{\frac{29}{4194304}>0.}
\end{aligned}\tag{CN.9}
\]
This is the **wrong sign** for concavity, with an explicit rational lower margin. It is an exact mathematical counterexample to CF5 on the full domain of normalized caps of width greater than two; even restricting widths to a tiny subinterval just above two does not repair it.

The endpoint caps are point-top caps, and no claim is made here about concavity on a domain additionally requiring longer positive top faces, a fixed width, or the actual hull-cap compatibility conditions of a high-area two-turn competitor. Those would be genuinely new and narrower conjectures, not CF5 as uploaded.

## 4. Implications for the candidate-functionals program

**Invalidated:** the proposed direct chain “CF5 global concavity + CF6 reference criticality ⇒ CF7 \(P_J\le M/2\) for all caps” has a false first premise. The package's numerical concavity screens missed a narrow, algebraically identifiable family near the minimum width threshold, where the exterior roof area varies quadratically but the niche correction begins cubically.

**Not invalidated:** the separate sharp value conjecture \(P_J(U)\le M/2\), since these caps have \(P_J\) near \(1/4\), far below \(M/2\). A proof by a different global method, or a concavity theorem on a *proved* competitive cap class, might still work. The package's numerical reflection-segment dip is substantial and worth further certification, but it is **not** promoted here to an exact counterexample to hull symmetrization; its current record contains only floating-point/raster tests without rigorous error bounds.

A profitable narrowed direction is to test a **fixed-width** convex cap class, where the positive \((1+\lambda)^2/4\) variation used above is unavailable. The uploaded record contains fixed-width negative second-difference samples, but no continuum proof of fixed-width concavity, no proof of reference criticality on a suitable domain, and no theorem putting every competitive two-turn cap there. Fixed-width concavity by itself also does not optimize over width; that requires an additional exact sharp width envelope.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long numerical optimization was used. This proof is self-reviewed rather than independently refereed or kernel-verified.