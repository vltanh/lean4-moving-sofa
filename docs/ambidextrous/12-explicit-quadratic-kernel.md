# 12. An explicit quadratic functional: concavity, exact kernel, and limitations

This is a concrete algebraic result, not just the abstract quadratic template of Lemma 18. The natural two-corner quadratic has a sum-of-squares concavity gap whose only kernel is horizontal translation. However, Note 11 proves that this quadratic is **not** a universal area majorant. A second test below shows that its unrestricted convex-body maximum is too large for the Romik target.

The point is to retain a verified quadratic identity that may be useful as part of a corrected certificate, while recording exactly why it does not solve the problem as it stands.

## 12.1 Definitions on a normalized support function

Let h be a real 2pi-periodic H^1 function with

\[
h(\pi/2)=1,\qquad h(3\pi/2)=0.
\tag{12.1}
\]

For geometric interpretation h is the support function of a convex body K of vertical span exactly one, between y=0 and y=1. Width strictly less than one is not covered by this normalization without an additional argument.

Set L=pi/2 and, for 0<=t<=L,

\[
f(t)=h(t),\qquad g(t)=h(t+L),\qquad
c_h(t)=(f(t)-1)\mu_t+(g(t)-1)\nu_t.
\]

Define

\[
I(h)=\frac12\int_0^L\det(c_h,c_h')\,dt,
\qquad
C(h)=\frac12\int_0^\pi(h^2-h'^2)\,dt.
\tag{12.2}
\]

A direct differentiation in the rotating frame gives

\[
I(h)=\frac12\int_0^L\left[(f-1)^2+(g-1)^2+(f-1)g'-(g-1)f'\right]dt.
\tag{12.3}
\]

Let \(h^\rho(t)=h(-t)+\sin t\), the support function of reflection across y=1/2. Define the full quadratic

\[
Q_0(h)=\frac12\int_0^{2\pi}(h^2-h'^2)\,dt-I(h)-I(h^\rho).
\tag{12.4}
\]

For a convex-body support function the first integral is |K|. For smooth strictly convex bodies this follows by writing the boundary as \(p=h\mu+h'\nu\), calculating \(p'=(h+h'')\nu\), and integrating \(\det(p,p')/2\); integration by parts gives the formula. Polygonal/general convex bodies can be reached by smooth support approximation, with H^1 convergence of support functions and area convergence. The algebraic results below only need the displayed integral definition, not this extension.

An identity useful for accounting for the affine reflection is

\[
C(h)+C(h^\rho)
=\frac12\int_0^{2\pi}(h^2-h'^2)\,dt+h(0)+h(\pi).
\tag{12.5}
\]

Indeed the cross term produced by adding sin(t) in the reflected half is the endpoint term h(0)+h(pi), while the integral of sin^2-cos^2 is zero. Thus Q_0 is the sum of the two half-functionals C-I, minus a convex-linear horizontal-width term. Omitting this width term would give an incorrect value, although not an incorrect Hessian.

## 12.2 A sharp one-endpoint square identity

**Lemma 31 (half-interval factorization).** If g is in H^1(0,L), L=pi/2, and g(0)=0, then

\[
\int_0^L(g'^2-g^2)\,dt
=\int_0^L(g'-g\cot t)^2\,dt\geq0.
\tag{12.6}
\]

Equality holds exactly for \(g(t)=b\sin t\).

**Proof.** On [epsilon,L], expand the square and use

\[
(g^2\cot t)'=2gg'\cot t-g^2\csc^2t.
\]

The resulting identity is

\[
\int_\varepsilon^L(g'-g\cot t)^2
=\int_\varepsilon^L(g'^2-g^2)+g(\varepsilon)^2\cot\varepsilon.
\]

Since g(0)=0, Cauchy-Schwarz gives
\(g(\varepsilon)^2/\varepsilon\leq\int_0^\varepsilon g'^2\to0\).
The boundary term therefore tends to zero. Taking epsilon down to zero proves integrability of the square and (12.6). If it vanishes, \((g/\sin t)'=0\) on each compact subinterval of (0,L), so g=b sin(t), with the endpoint value obtained by continuity. The converse follows by substitution. QED.

## 12.3 The half-functional has a sum-of-squares Hessian

Let h_0,h_1 satisfy h_i(pi/2)=1 on [0,pi]. Put delta=h_1-h_0, and now write

\[
f(t)=\delta(t),\qquad g(t)=\delta(t+L).
\]

Then f(L)=0 and g(0)=0. The negative of the quadratic homogeneous part of C-I is

\[
B(\delta)=\frac12\int_0^L(f'^2+g'^2+fg'-gf')\,dt.
\tag{12.7}
\]

**Theorem 32 (explicit half-kernel).**

\[
\boxed{
B(\delta)=\frac12\int_0^L(f'-g)^2\,dt
+\frac12\int_0^L(g'-g\cot t)^2\,dt\geq0.
}
\tag{12.8}
\]

Moreover B(delta)=0 exactly when \(\delta(\theta)=a\cos\theta\) on [0,pi].

**Proof.** Integration by parts gives \(\int fg'=-\int f'g\), since fg vanishes at both endpoints. Complete the first square in (12.7), leaving \(\frac12\int(g'^2-g^2)\), and apply Lemma 31. If both squares vanish, g=b sin(t) and f'=g. The condition f(L)=0 gives f=-b cos(t). Replacing b by -a gives delta(theta)=a cos(theta) on both quarter intervals. Conversely this function makes both squares zero. QED.

## 12.4 Full concavity and its geometric equality case

Let \(h_\lambda=(1-\lambda)h_0+\lambda h_1\), with both functions satisfying (12.1), and put delta=h_1-h_0 and \(\delta^\rho(t)=\delta(-t)\).

**Corollary 33 (full concavity gap).** For 0<=lambda<=1,

\[
Q_0(h_\lambda)-(1-\lambda)Q_0(h_0)-\lambda Q_0(h_1)
=\lambda(1-\lambda)\,[B(\delta)+B(\delta^\rho)]\geq0.
\tag{12.9}
\]

For 0<lambda<1, equality holds exactly when

\[
\delta(\theta)=a\cos\theta\quad\text{for all }\theta.
\tag{12.10}
\]

**Proof.** Expand the quadratic and use (12.5); the width term is linear and cancels. Apply Theorem 32 to the original and reflected upper halves. Their constants must agree because both functions have the same value delta(0). This joins the two half-kernels into (12.10). QED.

For support functions, (12.10) means exactly that K_1 is the horizontal translate K_0+(a,0): scalar products of a translation add a cos(theta) to the support function, and a compact convex set is determined by all its supporting half-planes.

Consequently, if a corrected majorant had the form Q_0 minus additional convex terms on a convex normalized domain, this existing gap would already force hull equality up to horizontal translation whenever the total concavity gap vanished. This statement is conditional on the corrected terms having the asserted sign and on a sharp global comparison; neither is supplied by (12.9).

## 12.5 A second explicit obstruction: even the maximum value is too large

Take the rectangle \(K_a=[-a,a]\times[0,1]\). Its canonical lower corner is

\[
c_a(t)=(a\cos2t-\cos t+\sin t,
\ 1-\sin t-\cos t+a\sin2t).
\]

Writing it as a(cos2t,sin2t)+(sin t-cos t,1-sin t-cos t), and integrating each quadratic and cross term, gives

\[
I(h_{K_a})=\frac\pi2a^2-2a+\frac\pi2-1,
\]

\[
Q_0(K_a)=6a-\pi a^2-\pi+2.
\tag{12.11}
\]

For detail, the pure rotating-vector term contributes pi*a^2/2, the cross term has integrand -a(sin t+cos t) and contributes -2a, and the remaining term is pi/2-1. The reflected path gives the same I, while the rectangle area is 2a.

At a=1,

\[
Q_0(K_1)=8-2\pi>12/7.
\tag{12.12}
\]

But Y<3/10, since the candidate cubic takes value 1/125 at 3/10. Therefore

\[
M=1+4Y^2+\arctan Y<1+4(3/10)^2+3/10=83/50<12/7.
\]

So Q_0 cannot be bounded by M on all normalized convex bodies. This rectangle is not a viable connected canonical common hull: at t=pi/4 the lower corner height is 2-sqrt(2)>1/2; its reflected niche overlaps the lower one over x=0. The vertical barrier of Theorem 24 rules out a connected body with this hull following these quarter-turn canonical paths.

**Conclusions.** There are two separate missing ingredients, not one: the signed-area-to-niche inequality fails without geometric hypotheses (disk test), and the all-convex-body relaxation has values above M (rectangle test). The exact square kernel is valid despite both failures. A successful certificate must handle those geometric issues rather than infer them from concavity.
