# 13. A contact-corrected quadratic and its exact concavity gap

The full-inner-wall contact terms lead to a more useful quadratic than Q_0. This note constructs it explicitly and proves its concavity, including the exact translation kernel. Note 14 evaluates its global maximum at Romik's exact constant. A geometric area-majorant assertion is **not** included in either algebraic theorem.

## 13.1 The functional suggested by the three-piece niche boundary

Keep the normalized support-function notation of Note 12 and put L=pi/2. On the upper half write

\[
f(t)=h(t),\quad g(t)=h(t+L),\quad
p_h(t)=f'(t)-g(t)+1,\quad q_h(t)=g'(t)+f(t)-1.
\tag{13.1}
\]

These are the rotating-frame components of the canonical corner velocity. For switching parameters

\[
0<a\leq b<L,
\]

define

\[
F_{a,b}(h)=C(h)+I(h)
-\frac12\int_a^L p_h^2\,dt
-\frac12\int_0^b q_h^2\,dt,
\tag{13.2}
\]

and

\[
\mathcal Q_{a,b}(h)
=F_{a,b}(h)+F_{a,b}(h^\rho)-h(0)-h(\pi).
\tag{13.3}
\]

By (12.5), the equivalent whole-body expression is the area integral plus the two I terms, minus the four displayed squared-velocity terms. Notice the **plus** sign before I here; this is a different functional from Q_0.

The fixed parameters a,b are part of the certificate. At the Romik candidate they will be beta and L-beta. For an arbitrary body they are not automatically its actual contact-switching angles.

## 13.2 The exact boundary identity motivating the signs

Let c=(f-1)mu+(g-1)nu, and set

\[
B=c+p_h\nu,\qquad D=c-q_h\mu.
\]

For any absolutely continuous path Z write \(I_Z[r,s]=\frac12\int_r^s\det(Z,Z')\). Integration by parts gives

\[
I_B[r,s]=I_c[r,s]-\frac12\int_r^s p_h^2
+\frac12[(f-1)p_h]_r^s,
\tag{13.4}
\]

\[
I_D[r,s]=I_c[r,s]-\frac12\int_r^s q_h^2
+\frac12[(g-1)q_h]_r^s.
\tag{13.5}
\]

For example, B'=(q_h+p_h')nu; subtract det(c,c') and integrate (f-1)p_h' by parts, using (f-1)'=p_h+g-1. The D calculation is the same with the other component.

Suppose, as an **additional geometric hypothesis**, that a niche boundary is the simple positively oriented concatenation of B traversed from L down to a, c from a to b, D from b down to 0, and the baseline, with

\[
p_h(a)=0,\qquad q_h(b)=0,\qquad f(L)=g(0)=1.
\]

All endpoint terms in (13.4)–(13.5) vanish, and its enclosed area is

\[
-I(h)+\frac12\int_a^L p_h^2+\frac12\int_0^b q_h^2.
\tag{13.6}
\]

This explains (13.2). It does not prove that every niche has this boundary, that the switching parameters are fixed, or that the enclosed region lies inside the common hull. Those are separate geometric questions.

## 13.3 Explicit Hessian

For a support difference delta with delta(L)=0 on [0,pi], now put

\[
f(t)=\delta(t),\quad g(t)=\delta(t+L),\quad
P=f'-g,\quad Q=g'+f,
\]

\[
X=f'+f\tan t,\qquad Y=g'-g\cot t.
\tag{13.7}
\]

Here f(L)=0 and g(0)=0. The integrability of X,Y follows from Lemma 31 and its reflected version. Let B_full be the negative homogeneous quadratic part of F_{0,L}. Expansion gives

\[
B_{\rm full}(\delta)
=\frac12\int_0^L[2f'^2+2g'^2+fg'-gf'-f^2-g^2].
\]

Using Theorem 32 and the two one-endpoint square identities,

\[
B_{\rm full}
=\frac12\int_0^L P^2+\frac12\int_0^L X^2+\int_0^L Y^2.
\tag{13.8}
\]

The negative quadratic part for the selected contacts is

\[
B_{a,b}=B_{\rm full}-\frac12\int_0^a P^2-\frac12\int_b^L Q^2.
\tag{13.9}
\]

Subtracting squares does not by itself preserve positivity. The following identity establishes the required sign.

**Theorem 34 (contact-quadratic factorization).**

\[
\begin{aligned}
B_{a,b}(\delta)={}&\frac12\int_a^b P^2
+\frac12\int_0^b X^2+\int_0^b Y^2\\
&+\int_b^L X^2+\frac12\int_b^L Y^2
+\frac{(\sin b\,f(b)+\cos b\,g(b))^2}{2\sin b\cos b}.
\end{aligned}
\tag{13.10}
\]

Every term is nonnegative. The kernel consists exactly of delta(theta)=k cos(theta) on [0,pi].

**Proof.** On an interval away from the endpoints write
\(f=\cos t\,u\), \(g=-\sin t\,v\). Then

\[
X=\cos t\,u',\quad Y=-\sin t\,v',
\quad P=\cos t\,u'-\sin t(u-v),
\quad Q=-\sin t\,v'+\cos t(u-v).
\]

Expansion yields the pointwise identity

\[
\frac12P^2+\frac12X^2+Y^2-\frac12Q^2
=X^2+\frac12Y^2
-\frac{d}{dt}\left[\frac{\sin t\cos t}{2}(u-v)^2\right].
\tag{13.11}
\]

Apply it on [b,L] to the remaining tail in (13.9). The bracket tends to zero at L: after expansion its potentially singular term is a constant multiple of f(t)^2/(L-t), which tends to zero by f(L)=0 and the same Cauchy-Schwarz estimate used in Lemma 31. The other terms tend to zero directly. The bracket at b is the final term of (13.10). This proves the factorization, first by truncation and then by a limit for H^1 functions.

If the expression vanishes, X=Y=0 almost everywhere, so f=A cos(t) and g=B sin(t). The boundary square at b forces A+B=0. This is exactly a horizontal-translation support difference. Conversely that difference makes all terms vanish. QED.

The assumption a<=b is essential to this displayed positivity proof: it makes the first integral have nonnegative orientation. The proof does not establish positivity for a gap with a>b.

## 13.4 Global concavity, not just a candidate Hessian calculation

**Corollary 35.** On the affine H^1 space of periodic functions satisfying h(L)=1 and h(-L)=0,

\[
\begin{aligned}
\mathcal Q_{a,b}(h_\lambda)
&-(1-\lambda)\mathcal Q_{a,b}(h_0)-\lambda\mathcal Q_{a,b}(h_1)\\
&=\lambda(1-\lambda)
\left[B_{a,b}(h_1-h_0)+B_{a,b}((h_1-h_0)^\rho)\right]\geq0.
\end{aligned}
\tag{13.12}
\]

For 0<lambda<1 equality holds exactly when h_1-h_0=k cos(theta) on the full circle.

**Proof.** Expand the quadratic. Reflection is affine on support functions, and the subtracted width is linear, so only the two negative quadratic parts remain. Theorem 34 gives the sign and the half-kernels. Their constants agree at theta=0, yielding one global translation. QED.

This statement already controls symmetric and antisymmetric support perturbations. It does not restrict the perturbations to reflected witness pairs. A sharp first-order certificate at a candidate will therefore give a genuine global maximization theorem for this quadratic; that calculation is carried out next.

Neither convexity of a support function nor feasibility of a body is needed for the algebraic inequality. Conversely, algebraic validity on this large space must not be confused with an area bound on that space.
