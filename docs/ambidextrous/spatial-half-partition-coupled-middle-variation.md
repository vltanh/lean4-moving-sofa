# Coupled middle-arc \(P_J\) stability without a symmetry assumption

**Theorem PJ-COUP1 (exact local two-source deficit).**
The single-arc calculation [PJ-MID](spatial-half-partition-middle-arc-variation.md)
extends to *simultaneous and independent* perturbations of the two
middle curved upper support arcs of Romik's one-turn reference cap.
There is a signed cross term, but the resulting quadratic form is
strictly negative by a short Dirichlet estimate. This is a true
**local** statement on the exposed reference contact chart;
it neither restores the disproved global concavity CF5 nor treats
arbitrary competitor supports.

Let \(T=(\beta,L-\beta)\), \(L=\pi/2\), and use the reference
\(f,g,p,q\) and candidate \(M\) from PJ-MID.
Let \(\phi,\psi\in C_c^2(T)\). For sufficiently small
\(|\varepsilon|\), form the convex cap \(U_\varepsilon\) by replacing

\[
f(t)\mapsto f(t)+\varepsilon\phi(t),\qquad
g(t)\mapsto g(t)+\varepsilon\psi(t),
\quad(t\in T),
\tag{PJ-COUP.1}
\]

and leaving all other upper support directions unchanged.
The support patches have positive reference curvature and the
reference corner/one-wall exposure signs are strict on the compact
perturbation supports; therefore sufficiently small perturbations
retain convexity, the incoming width and middle half \(J\),
and the same *two smooth wall branches plus one corner branch*
of the actual niche where they vary. This is **not** a general
contact assumption for arbitrary caps; it is the stable explicit
Romik reference chart.

Then the following identity is exact for that small-\(\varepsilon\)
interval:

\[
\boxed{
\begin{aligned}
P_J(U_\varepsilon)-\frac M2
&=\varepsilon^2 Q(\phi,\psi),\\
Q(\phi,\psi)
&=\frac12\int_T(\phi^2+\psi^2)\,dt
-\int_T(\phi'^2+\psi'^2+\phi\psi')\,dt.
\end{aligned}}
\tag{PJ-COUP.2}
\]

In particular,

\[
\boxed{\frac M2-P_J(U_\varepsilon)
\ge\frac58\varepsilon^2
\int_T(\phi'^2+\psi'^2)\,dt.}
\tag{PJ-COUP.3}
\]

Equality in PJ-COUP.3 for nonzero perturbations is not claimed;
in fact the Dirichlet interval is strictly shorter than \(L\).
This establishes strict two-sided local maximality at the reference
within the independently varying two-middle-arc class.

## 1. Two exterior roof pieces

Use normals \(n=(c,s)\), \(n^\perp=(-s,c)\). The outer
contact points are

\[
O_f=f n+f'n^\perp,\qquad
O_g=g n^\perp-g'n.
\]

Both actual upper roof flanks are decreasing in their horizontal
coordinate as \(t\) increases. Writing
\(\rho_f=f''+f\), \(\rho_g=g''+g\), their horizontal
derivatives are \(x_{O_f}'=-\rho_f s\),
\(x_{O_g}'=-\rho_g c\).
The exterior roof areas change by the ordinary support-area
first variation

\[
\varepsilon\int_T(\rho_f\phi+\rho_g\psi)\,dt,
\tag{PJ-COUP.4}
\]

and have the exact quadratic coefficient

\[
Q_{\rm outer}
=\frac12\int_T
(\phi^2-\phi'^2+\psi^2-\psi'^2)\,dt.
\tag{PJ-COUP.5}
\]

The two outer curve pieces are disjoint, so there is no cross
term here. Compact support makes their endpoint contributions zero.

## 2. Both smooth one-wall niche pieces

The first-wall stationary niche point is \(Z_f=O_f-n\),
with \(x_{Z_f}'=(1-\rho_f)s>0\).
The second-wall stationary point is \(Z_g=O_g-n^\perp\),
with \(x_{Z_g}'=(1-\rho_g)c>0\).
Their companion walls have strictly positive inactive margins
throughout the affected reference chart, and the two smooth
niche pieces occur in disjoint horizontal intervals.

Their area first variation is

\[
\varepsilon\int_T[(1-\rho_f)\phi+(1-\rho_g)\psi]\,dt,
\tag{PJ-COUP.6}
\]

and their total exact quadratic coefficient is

\[
Q_{\rm stationary}=-Q_{\rm outer}.
\tag{PJ-COUP.7}
\]

This last identity follows directly from the graph parametrizations:
the change of each stationary height is the same as for its
corresponding outer boundary, while the change of its horizontal
Jacobian is the negative of the outer Jacobian change.

## 3. The shared moving-corner region and its cross term

The corner curve is

\[
C=(f-1)n+(g-1)n^\perp,\qquad
C'=p n+q n^\perp,
\quad p<0<q.
\]

It traverses the central active niche boundary with \(x_C'<0\).
The joint variation has

\[
\delta C=\phi n+\psi n^\perp,\qquad
\delta x_C=\phi c-\psi s,\quad
\delta y_C=\phi s+\psi c,
\]

and

\[
\delta x_C'
=\phi'c-\phi s-\psi's-\psi c.
\]

Integrating the true geometric corner area
\(\int_T y_C(-x_C')\,dt\), the *first* variation from both
supports is

\[
\varepsilon\int_T(q\phi-p\psi)\,dt.
\tag{PJ-COUP.8}
\]

The **second** coefficient is

\[
\begin{aligned}
Q_{\rm corner}
&=-\int_T(\phi s+\psi c)
(\phi'c-\phi s-\psi's-\psi c)\,dt\\
&=\frac12\int_T(\phi^2+\psi^2)\,dt
+\int_T\phi\psi'\,dt.
\end{aligned}
\tag{PJ-COUP.9}
\]

For clarity, the cross terms on the first line are
\(2sc\,\phi\psi-c^2\psi\phi'+s^2\phi\psi'\).
Integrating the term with \(\phi'\) by parts yields
\(\phi\psi'\), with no boundary term. **The sign of this
oriented cross term is essential.** It is not permissible to
discard it or replace it with an unsigned scalar correction.

## 4. Cancellation of all first-order terms

For the explicit Romik middle supports
\(f=R\cos(t/2+\pi/8)+s/2\),
\(g=R\sin(t/2+\pi/8)+c/2\),

\[
q=2\rho_f-1,\qquad -p=2\rho_g-1.
\tag{PJ-COUP.10}
\]

Thus the full niche first variation, smooth walls *plus corner*,
is

\[
\int_T[(1-\rho_f+q)\phi+
(1-\rho_g-p)\psi]\,dt
=\int_T(\rho_f\phi+\rho_g\psi)\,dt,
\]

exactly the exterior first variation PJ-COUP.4.
All first-order terms cancel.

The full niche quadratic coefficient is
\(-Q_{\rm outer}+Q_{\rm corner}\).
Subtracting it from the exterior coefficient gives
\(2Q_{\rm outer}-Q_{\rm corner}\), which is exactly the
quadratic form in PJ-COUP.2.

These calculations involve the **actual exposed geometric
niche** in the reference chart, not a formal signed area
whose corners might wind negatively. Every affected boundary
segment is counted once, with the orientation specified above.
The support perturbations vanish near the switch endpoints,
so each changing branch-area integral is literally quadratic
in \(\varepsilon\). No higher-order remainder is hidden.

## 5. Coercivity of the coupled form

The interval \(T\) has length \(L-2\beta<\pi/2\).
Dirichlet's inequality gives

\[
\|\phi\|_2\le\tfrac12\|\phi'\|_2,\qquad
\|\psi\|_2\le\tfrac12\|\psi'\|_2.
\]

Consequently, with
\(E=\|\phi'\|_2^2+\|\psi'\|_2^2\),

\[
\frac12(\|\phi\|_2^2+\|\psi\|_2^2)\le E/8,
\]

and

\[
\left|\int_T\phi\psi'\,dt\right|
\le\tfrac12\|\phi'\|_2\|\psi'\|_2
\le E/4.
\]

Therefore \(Q(\phi,\psi)\le E/8-E+E/4=-5E/8\),
giving PJ-COUP.3. In particular, the signed cross
term cannot destroy local strict maximality in this class.

## 6. Review boundary and next proof gate

This closes the **full two-arc compactly supported smooth
second-variation calculation** under the actual candidate contact
pattern, including both stationary walls and their jointly moving
corner. It makes no claim about variations touching the
candidate's curvature switches, moving the horizontal top face,
changing incoming width, or entering a different exposed-contact
topology. A purported global \(P_J\le M/2\) theorem would have
to control those modes and all far competitors as well.

This is a self-reviewed analytic proof, not a Lean formalization,
CI result, independent referee check, or global numerical search.
