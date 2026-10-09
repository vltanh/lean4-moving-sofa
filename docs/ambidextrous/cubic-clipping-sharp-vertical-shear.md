# An exact vertical-shear witness: the two-handed clipping interaction is **genuinely cubic**

**Date: 2026-10-09. Status:** A sharp-order obstruction for the global Romik-centered Minkowski interpolation mechanism. The previously proved [MC3](global-directional-romik-clipping-vanishes.md) bound \(G(K_\lambda)=O(\lambda^3)\) applies uniformly to **every** unit-height convex hull direction, including asymmetric opposite-end-face hulls. This note proves **the exponent three cannot be improved uniformly to \(o(\lambda^3)\)**: along a simple actual unit-height affine shear of Romik's hull,
\[
\boxed{G(K_\lambda)=\frac{a^3}{6}\lambda^3+O_a(\lambda^4)}
\]
for every fixed sufficiently small \(a>0\).

This is **not** a counterexample to Romik optimality or to the conjectured unit-height star-concavity of the **signed full two-turn area**. The clipping term is only the *positive* interaction credit; the total signed area also contains two *negative* weighted one-turn deficits. The result identifies the first nontrivial positive interaction whose payment is indispensable to a global proof. No numerical samples or old contact-chart assumptions on an arbitrary competing hull enter the theorem.

## 1. Fix a shear direction that separates the two top support faces

Use the horizontally and vertically reflection-symmetric Romik reference convex hull \(K_*\subset\mathbb R\times[0,1]\), with top and bottom horizontal support faces
\[
F_*=[-b,b],\qquad b=m/2,\qquad m=\frac1{3\sin\beta},
\quad \beta=\arctan Y,\quad 4Y^3+3Y-1=0 .
\]
Let \(U_*\) be its downward upper convex cap. The complete one-handed positive niche roof is \(n_*(x)\), and the *true ordinary upper-roof deficiency* is \(d_*(x)=1-A_*(x)\). Romik's exact terminal circular arcs imply, at either face endpoint,
\[
\boxed{
n_*(b-z)=z^2+O(z^4),\qquad
d_*(b+z)=z^2+O(z^4)
}\qquad(z\downarrow0),
\tag{SH.1}
\]
with horizontally reflected versions at \(-b\). This is immediate from
\(
n_*(b-z)=\frac12-\sqrt{\frac14-z^2}
\)
and
\(
A_*(b+z)=\frac12+\sqrt{\frac14-z^2}.
\)

For fixed \(a>0\) sufficiently small (e.g. any sufficiently small rational a), let
\[
T_a(x,y)=\bigl(x+a(y-\tfrac12),y\bigr),\qquad
K^{(a)}=T_aK_*,
\]
and interpolate by the **genuine Minkowski chord**
\[
\boxed{K_\lambda=(1-\lambda)K_*+\lambda K^{(a)}.}\tag{SH.2}
\]
Every \(K_\lambda\) has vertical span **exactly one**. For small a, the entire chord belongs to the project's fixed normalized bounding box \([-5/2,5/2]\times[0,1]\), with horizontal translation if needed. No assumption of physical two-handed feasibility of the sheared endpoint is made.

Let \(U_\lambda\) and \(V_\lambda\) be the downward upper and *vertically reflected lower* caps associated with \(K_\lambda\). Because vertical reflection conjugates \(T_a\) with \(T_{-a}\), the top-face intervals are **exactly**
\[
\boxed{
\begin{aligned}
F_U(\lambda)&=[-b+\tfrac12a\lambda,\ b+\tfrac12a\lambda],\\
F_V(\lambda)&=[-b-\tfrac12a\lambda,\ b-\tfrac12a\lambda].
\end{aligned}}\tag{SH.3}
\]
These are actual exposed face intervals: the top face of a Minkowski sum is the sum of the two top faces. Thus its right and left mismatch intervals each have length
\[
\boxed{\Delta=a\lambda.}\tag{SH.4}
\]

## 2. Uniform outer-flank and attached inner-ray quadratic expansions

The reference upper circular flank immediately to the right of \(b\) has the actual graph
\[
(x,y)=(b+z,\ 1-z^2+O(z^4)).
\tag{SH.5}
\]
Under \(T_a\) this becomes
\[
(x',y')=(b+\tfrac12a+z-az^2+O_a(z^4),\
1-z^2+O(z^4)),
\]
so with \(d=x'-(b+a/2)\), \(1-y'=d^2+O_a(d^3)\). In particular the right-hand *terminal* support of \(T_aK_*\), for \(v=L-t\downarrow0\) with \(L=\pi/2\), has expansion
\[
h_{T_aK_*}(u_{L-v})
=1+(b+\tfrac12a)v-\frac14v^2+O_a(v^3).
\tag{SH.6}
\]
The original terminal support has the same quadratic coefficient \(-1/4\). Minkowski linearity of support functions therefore gives
\[
\boxed{
h_{K_\lambda}(u_{L-v})
=1+\bigl(b+\tfrac12a\lambda\bigr)v
-\frac14v^2+O_a(v^3)
}\tag{SH.7}
\]
**uniformly** in sufficiently small \(\lambda\). The analogous left terminal upper support has right/left exchanged and its endpoint shifted by \(a\lambda/2\).

The resulting outer roof \(A_{U_\lambda}\), just beyond either of its top-face endpoints, satisfies
\[
\boxed{
d_{U_\lambda}(b+\tfrac12a\lambda+z)
=z^2+O_a(z^3).
}\tag{SH.8}
\]
The same assertion holds for \(V_\lambda\) with \(-a\lambda/2\), and after horizontally reflecting to the left endpoint. This follows either by Legendre inversion of SH.7 or directly by optimizing the nearby upper supporting lines:
\(
A(b_\lambda+z)=\inf_{v>0}
[(h(u_{L-v})-(b_\lambda+z)\sin v)/\cos v]
=1-z^2+O_a(z^3).
\)

There is a **matching actual inner-wall ray expansion** on the *inside* of the same top face. The first-wall lower forbidden roof is
\[
R_{L-v}(b_\lambda-z)
=\frac{h(u_{L-v})-1-(b_\lambda-z)\sin v}{\cos v}
=zv-\frac14v^2+O_a(v^3).
\]
Its stationary maximum occurs at \(v=2z+O_a(z^2)\) and has height
\(z^2+O_a(z^3)\). Its companion inner wall is strictly higher on this terminal contact region: the reference companion support has a strict positive margin, and the small shear and Minkowski interpolation preserve it. Every other turn angle has a strict lower height near the face endpoint, by the global reference terminal-ray chart and continuity. Therefore the **complete angular niche** satisfies
\[
\boxed{
n_{U_\lambda}(b+\tfrac12a\lambda-z)
=z^2+O_a(z^3),
}\tag{SH.9}
\]
uniformly for \(\lambda,z\downarrow0\). The reflected left counterpart and both analogous statements for \(V_\lambda\) hold.

**No extra clipped strips.** Romik's open-quarter curvature measures obey
\(0\le h_*+h_*''\le1-\kappa\) with \(\kappa\ge7/400>0\). For fixed small a, the affine shear of its piecewise-smooth outer arcs has bounded nonnegative open-quarter curvature, with no atoms away from the two horizontal axis normals (all joins retain a common exposed boundary point). For sufficiently small \(\lambda\), the interpolated support thus still satisfies
\(
0\le h_\lambda+h_\lambda''\le1
\)
on both relevant open quarters. The elementary comparison in [SR.4](curvature-only-signed-roof.md) then places each entire positive niche inside **its own top-face interval**. Hence a positive clipping interaction
\(
\min(n_U,d_V)+\min(n_V,d_U)
\)
can occur only where **one** face extends past the other: the right interval \([b-\Delta/2,b+\Delta/2]\) and the left interval \([-b-\Delta/2,-b+\Delta/2]\). The two intervals are disjoint.

## 3. The complete ordinary clipping integral is **asymptotically exact**

At the **right** mismatch interval, put
\[
x=b-\frac{\Delta}{2}+s,\qquad 0\le s\le\Delta.
\]
Here \(d_{V_\lambda}(x)=s^2+O_a(\Delta^3)\) by SH.8 and
\(n_{U_\lambda}(x)=(\Delta-s)^2+O_a(\Delta^3)\) by SH.9. The other clipping term vanishes on this interval because \(n_{V_\lambda}(x)=0\) outside \(V_\lambda\)'s top face. Thus the right contribution is
\[
\begin{aligned}
G_R(\lambda)
&=\int_0^\Delta
\min\bigl(s^2+O_a(\Delta^3),
          (\Delta-s)^2+O_a(\Delta^3)\bigr)\,ds\\
&=\Delta^3\int_0^1\min(z^2,(1-z)^2)\,dz+O_a(\Delta^4)\\
&=\boxed{\frac{\Delta^3}{12}+O_a(\Delta^4).}
\end{aligned}\tag{SH.10}
\]
The **left** mismatch interval is identical after interchanging U and V and reflecting x:
\[
G_L(\lambda)=\frac{\Delta^3}{12}+O_a(\Delta^4).
\]
Therefore the entire exact positive two-handed clipping correction is
\[
\boxed{
G(U_\lambda,V_\lambda)
=\frac{\Delta^3}{6}+O_a(\Delta^4)
=\frac{a^3}{6}\lambda^3+O_a(\lambda^4).
}\tag{SH.11}
\]

**Theorem SH1 (cubic exponent is optimal).** For any fixed sufficiently small positive shear parameter a, the positive clipping term along the genuine unit-height Romik-to-shear Minkowski chord satisfies
\[
\boxed{
\lim_{\lambda\downarrow0}
\frac{G(U_\lambda,V_\lambda)}{\lambda^3}
=\frac{a^3}{6}>0.
}
\]
Thus the global bound MC3 cannot be improved to \(o(\lambda^3)\) uniformly over unit-height hull directions, and the cubic term cannot simply be dropped from the global signed-area comparison.

## 4. A global star-concavity shortcut that is **provably false**

A tempting proof decomposition is to seek concavity of each *weighted one-turn* functional \(\Psi\) and separately demand a Jensen lower bound on the positive clipping interaction:
\[
\boxed{G(U_\lambda,V_\lambda)\stackrel{?}{\ge}
(1-\lambda)G(U_*,U_*)+\lambda G(U^{(a)},V^{(a)})
=\lambda G(U^{(a)},V^{(a)}).}\tag{SH.12, FALSE}
\]
Such an inequality would make the full signed area star-concavity follow by adding the three purportedly concave terms. But SH.12 fails **on the exact vertical shear family just constructed**.

For each fixed sufficiently small positive a, the terminal outer-flank and stationary-ray expansions above also hold along the *entire* interpolation \(0\le\lambda\le1\) (the small fixed shear preserves the strict reference curvature gap, after reducing a if necessary). Taking \(\lambda=1\) and letting a tend to zero gives
\[
G(U^{(a)},V^{(a)})=\frac{a^3}{6}+O(a^4)>0
\qquad(0<a\ll1).
\]
For this same fixed a, however,
\[
\frac{G(U_\lambda,V_\lambda)}{\lambda}
=\frac{a^3}{6}\lambda^2+O_a(\lambda^3)\longrightarrow0
\quad(\lambda\downarrow0).
\]
Thus for all sufficiently small positive \(\lambda\),
\[
\boxed{G(U_\lambda,V_\lambda)
<\lambda G(U^{(a)},V^{(a)}).}\tag{SH.13}
\]

**Consequences:** Even if one succeeded in proving that the two individual \(\Psi\)-terms are Minkowski-concave on the unit-height cap class, the positive cross-handed clipping credit is **not** Minkowski-star-concave and cannot be added term by term. The combined star-concavity proof must exploit a **quantitative extra Jensen gain** from the cap terms large enough to pay the missing clipping Jensen mass. This is exactly the nontrivial *global deficit-versus-clipping charge* that remains unresolved. The false SH.12 inequality is excluded rigorously by real, smooth, unit-height convex hulls, with no random numerical optimizer.

**What this does *not* imply:** The signed full-turn sofa-area functional is
\(
\mathscr S(K_\lambda)
=\Psi(U_\lambda)+\Psi(V_\lambda)+G(U_\lambda,V_\lambda).
\)
The **positive cubic clipping credit** may be more than paid by the **negative quadratic** one-turn losses; this is consistent with Romik optimality and with numerical shear tests. The missing star-concavity (or an alternative universal deficit-versus-clipping inequality) remains **unproved**. This example is not a feasible above-\(M\) sofa.

No CI, Lean/Lake compilation, random screen as proof, or complete unrestricted optimality result is claimed. The argument uses exact reference terminal geometry and elementary expansions, and is subject to independent mathematical review.
