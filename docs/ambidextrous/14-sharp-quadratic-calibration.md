# 14. The contact quadratic has exactly Romik's value as its unique maximum

This note closes the **algebraic maximization problem** for the explicit quadratic in Note 13. It does not close the moving-sofa problem: the geometric comparison between actual area and this fixed-contact quadratic is not generally valid. The distinction is demonstrated again at the end.

The candidate functions are the support-form rewrite of Romik's (SOL1), (SOL6), and (SOL5), with his constants. The matching, stationarity, value, and quadratic equality calculation are supplied below by hand; no symbolic solver or numerical experiment is used. Source for comparison: [Romik, Section 5](https://arxiv.org/html/1606.08111v3#S5).

## 14.1 Exact functions and a matching identity

Let Y be the positive root of \(4Y^3+3Y-1=0\), and set

\[
\beta=\arctan Y,\quad L=\pi/2,\quad b=L-\beta,
\quad s=\sin\beta,\quad c=\cos\beta,
\]

\[
A=\frac1{4s},\quad k=1-\frac43A,\quad
T=\frac32(\pi/4-\beta),\quad R=\frac{c}{\cos T}.
\tag{14.1}
\]

On [0,L] define f_* and g_* by

\[
(f_*,g_*)=
\begin{cases}
(\cos t+\tfrac12\sin t,
(2A-1)\sin t+\tfrac12\cos t+\tfrac12),&0\leq t\leq\beta,\\
(R\cos(t/2+\pi/8)+k\cos t+\tfrac12\sin t,
R\sin(t/2+\pi/8)-k\sin t+\tfrac12\cos t),&\beta\leq t\leq b,\\
((1-\tfrac23A)\cos t+\tfrac12\sin t+\tfrac12,
(\tfrac83A-1)\sin t+\tfrac12\cos t),&b\leq t\leq L.
\end{cases}
\tag{14.2}
\]

Define h_* on [0,pi] by h_*(t)=f_*(t), h_*(t+L)=g_*(t), and extend to the lower half by

\[
h_*(-t)=h_*(t)-\sin t\quad(0\leq t\leq\pi).
\tag{14.3}
\]

This makes \(h_*^\rho=h_*\). Both values at the top normal are one, and the bottom-normal value is zero.

**Lemma 36 (matching).** The pieces in (14.2) match in value and first derivative at beta and b. Moreover

\[
p_*(\beta)=0,\qquad q_*(b)=0,
\tag{14.4}
\]

where p_*=f_*'-g_*+1 and q_*=g_*'+f_*-1.

**Proof.** The only nontrivial trigonometric relation needed is

\[
R\cos T=c,\qquad R\sin T=\frac1{3s}-s.
\tag{14.5}
\]

The first is the definition. For the second put \(z=(1-2Y^2)/(3Y)\). The exact bounds from Notes 4 and 10 give 2/7<Y<3/10 and pi/12<beta<pi/4, so 0<z<1 and 0<T<pi/4. The triple-angle and double-angle identities, reduced using the cubic, give

\[
\tan(2T)=\frac{3(4Y^2-5Y-1)}{5-15Y-12Y^2},
\quad
\tan(2\arctan z)=\frac{3(5Y-1)}{16Y^2-Y-1}.
\]

The denominators are nonzero on the indicated root bounds. Their cross-product difference, after cancelling the common factor 3, is

\[
(16Y-6)(4Y^3+3Y-1)=0.
\]

Both doubled angles lie in (0,pi/2), where tangent is injective. Hence tan(T)=z. Multiplying by R cos(T)=c proves the second part of (14.5).

For a short verification of the vector matching, form the corner c_*=(f_*-1)mu+(g_*-1)nu. Its first-phase value and derivative at beta are

\[
c_*(\beta)=(1-c,\tfrac12-s),
\qquad
c_*'(\beta)=(s-c/2,\ c^2/(2s)-c).
\tag{14.6}
\]

For the middle phase, writing z_0=t-pi/4 gives

\[
c_*(t)=
(k-R\sin(3z_0/2)+\sqrt2\sin z_0,
\tfrac12+R\cos(3z_0/2)-\sqrt2\cos z_0).
\]

Substitute t=beta and (14.5), using \(\sqrt2\sin(\pi/4-\beta)=c-s\) and \(\sqrt2\cos(\pi/4-\beta)=c+s\). This gives exactly (14.6), including its derivative. Therefore f_*,g_* and their derivatives match. The identities

\[
f_*(L-t)=g_*(t)+2k\sin t,
\qquad g_*(L-t)=f_*(t)-2k\cos t
\tag{14.7}
\]

follow directly from the displayed formulas, and transfer matching to b. Finally p_* in the first phase is 1/2-2A sin(t), so p_*(beta)=0. Equation (14.7) gives p_*(L-t)=-q_*(t), proving q_*(b)=0. QED.

No numerical matching is hidden in this lemma. In particular h_* is a well-defined periodic H^1 function, even though its derivative can jump at the top and bottom normals corresponding to flat faces.

## 14.2 Interior equations and interface fluxes

Write F=F_{beta,b}. Its three integrands, expressed without abbreviating total derivatives, are

\[
\mathscr L_1=\tfrac12[f^2+2g^2-2g+1-f'^2-2g'^2-(fg)'+f'+g'],
\]

\[
\mathscr L_2=\tfrac12[f^2+g^2-2f'^2-2g'^2-fg'+gf'+g'-f'],
\]

\[
\mathscr L_3=\tfrac12[2f^2+g^2-2f+1-2f'^2-g'^2+(fg)'-f'-g'].
\tag{14.8}
\]

Their Euler equations are, respectively,

\[
(f''+f,\ g''+g-1/2)=(0,0),
\]

\[
(2f''-g'+f,\ 2g''+f'+g)=(0,0),
\]

\[
(f''+f-1/2,\ g''+g)=(0,0).
\tag{14.9}
\]

The elementary trigonometric functions in (14.2) satisfy these equations on each open phase: the middle phase combines the frequency-1 translation solution with the frequency-1/2 solution.

Let chi be the indicator of [beta,L] and psi that of [0,b]. The derivative fluxes for integration by parts are

\[
\Pi_f=-f'-\tfrac12(g-1)-\chi p_h,
\qquad
\Pi_g=-g'+\tfrac12(f-1)-\psi q_h.
\tag{14.10}
\]

At beta the change in the f-flux is -p_*(beta)=0; at b the change in the g-flux is q_*(b)=0. Thus no interface terms remain at h_*. The endpoints satisfy

\[
f_*'(0)=\tfrac12,\qquad g_*'(L)=-\tfrac12,
\qquad f_*(L)=g_*(0)=1.
\tag{14.11}
\]

For any H^1 variation delta with delta(L)=0, integration by parts now gives

\[
DF(h_*)[\delta]=\tfrac12[\delta(0)+\delta(\pi)].
\tag{14.12}
\]

Reflection preserves these endpoint values. Therefore the two copies of (14.12) cancel the derivative of the width subtracted in (13.3):

\[
D\mathcal Q_{\beta,b}(h_*)[\delta]=0
\tag{14.13}
\]

for every periodic variation satisfying delta(L)=delta(-L)=0. This calculation includes nonsymmetric variations; it is not restricted to the reflected candidate family.

## 14.3 Exact value without integrating the geometric boundary

Here is a direct evaluation of the quadratic at h_*. It does not use the geometric area of the sofa as an input.

Write F=F_2+F_1+F_0 for its homogeneous quadratic, linear, and constant parts. Integrating the linear terms in (14.8) gives

\[
F_1=-\int_0^\beta g-\int_b^L f
+f(\beta)+g(b)-\tfrac12[f(0)+g(0)+f(L)+g(L)],
\qquad F_0=\beta.
\tag{14.14}
\]

At h_*, (14.7) and the early-phase formulas simplify this to

\[
F_1(h_*)=4A c-\tfrac83A-1-\beta.
\tag{14.15}
\]

For verification, \(\int_0^\beta g_*=(2A-1)(1-c)+s/2+\beta/2\), \(f_*(\beta)=c+s/2\), and (14.7) supplies the late integral and the other switching value.

Integration by parts against h_* itself, using the Euler equations and flux continuity, gives

\[
2F_2(h_*)+F_1(h_*)
=[\Pi_f f_*+\Pi_g g_*]_0^L=\tfrac{16}{3}A-1.
\tag{14.16}
\]

The last number follows from

\[
f_*'(L)=2A/3-1,\quad g_*'(0)=2A-1,
\quad f_*(0)=1,\quad g_*(L)=8A/3-1,
\]

and (14.10)–(14.11). Combining (14.14)–(14.16),

\[
F(h_*)=\tfrac43A+2A c-1+\beta/2.
\]

Since h_* is reflection invariant and its horizontal width is \(h_*(0)+h_*(\pi)=8A/3\),

\[
\mathcal Q_{\beta,b}(h_*)=4A c-2+\beta
=\cot\beta-2+\beta.
\tag{14.17}
\]

Finally the cubic gives \(1/Y=4Y^2+3\), and hence

\[
\cot\beta-2+\beta=1+4Y^2+\arctan Y=M.
\tag{14.18}
\]

Thus the exact constant emerges from the quadratic evaluation itself.

## 14.4 The completed algebraic theorem

**Theorem 37 (sharp quadratic calibration and rigidity).** For every real periodic H^1 function h with h(L)=1 and h(-L)=0, let delta=h-h_*. Then

\[
\boxed{
M-\mathcal Q_{\beta,L-\beta}(h)
=B_{\beta,L-\beta}(\delta)+B_{\beta,L-\beta}(\delta^\rho)\geq0.
}
\tag{14.19}
\]

Equality holds exactly when \(h(\theta)=h_*(\theta)+a\cos\theta\) for a real a.

**Proof.** The Taylor expansion of a quadratic is exact. Its first derivative at h_* is zero by (14.13), its value there is M by (14.18), and its negative quadratic part is the sum in Corollary 35. Theorem 34 supplies the nonnegative squares and their kernel. QED.

For convex-body support functions, equality means a horizontal translate of the candidate hull. The calculation identifies the same support pieces as Romik's construction, but the theorem itself is an algebraic statement on a larger affine function space.

## 14.5 Why this is not yet an optimality proof for sofas

The required geometric assertion would be

\[
|E_K|\leq\mathcal Q_{\beta,L-\beta}(h_K).
\tag{14.20}
\]

It is false without additional hypotheses. For the radius-1/2 disk in Note 11, p=1/2, q=-1/2, and direct substitution gives

\[
\mathcal Q_{\beta,L-\beta}(h_K)=\frac\pi4-\frac12+\frac\beta2
<\frac\pi4=|K|.
\tag{14.21}
\]

The algebraic inequality is true; its use as an area upper bound is the issue. Moreover the full-turn, vertical-span-one normalization used here has not been proved for all competitive common hulls from Theorem 30. Actual contact switches can move, and a full swept niche can extend outside the common hull.

What is now proved is substantially more specific than the initial program: **an explicit quadratic, its exact global maximum M, and its complete equality kernel have been calculated.** The remaining task is to establish an appropriate geometric comparison, possibly with corrected auxiliary terms or on a rigorously reduced maximizing class. None of those missing statements is inferred from Theorem 37.
