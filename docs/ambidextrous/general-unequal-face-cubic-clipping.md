# The exact cubic clipping law for *unequal* and independently displaced top faces

**Lemma UFC1.** Let U,V be two compact downward convex normalized
one-turn caps of height one on the **same horizontal projection**
I, with (possibly unequal) top-face intervals
\(J_U=[a_U,b_U]\) and \(J_V=[a_V,b_V]\).
Assume both caps:

* contain the entire horizontal incoming midline
  in their cap and have cap roof \(A_X\ge1/2\);
* have their full positive-height turning niche roofs
  \(0\le n_X\le1/2\);
* have open-quarter support curvature densities
  \(0\le\rho_{X,f},\rho_{X,g}\le1-\eta\)
  a.e. and **no singular curvature on those quarters**,
  for a common \(0<\eta\le1\).

For each cap its niche is automatically confined to its own
top-face interval. Define four nonnegative endpoint displacements
\[
\begin{array}{ll}
d_{U,L}=(a_V-a_U)_+,&
d_{U,R}=(b_U-b_V)_+,\\
d_{V,L}=(a_U-a_V)_+,&
d_{V,R}=(b_V-b_U)_+.
\end{array}
\]
Suppose each of these four distances is at most \(\eta\).
Then the true connected two-turn envelope E of the two caps has
the exact area identity
\[
|E|=\Psi(U)+\Psi(V)+G
\]
with a **uniform nonnegative** interaction correction satisfying

\[
\boxed{
0\le G\le
\frac{|a_U-a_V|^3+|b_U-b_V|^3}{3\eta}.
}
\tag{UFC.1}
\]

There is **no equal-top-face-length condition**, reference proximity,
reflection symmetry, common active contact pattern, or numerical
quadrature premise. This sharpens CCC1 to independently varying
*both* endpoints of both top faces. The estimate is geometric,
without importing the WV2 upper value.

## Proof

Write for the cap X the first and companion supports
\(f_X(t)=h_X(\cos t,\sin t)\) and
\(g_X(t)=h_X(-\sin t,\cos t)\).
Their endpoint support data are
\[
f_X(L)=g_X(0)=1,\quad
f_X'(L^-)=-b_X,\quad
g_X'(0^+)=-a_X,\qquad L=\pi/2.
\]
The support-curvature ODE and the nonnegative sine Green kernel
give, as in CCC,
\[
\begin{aligned}
g_X(t)&\le1-a_X\sin t-\eta(1-\cos t),\\
f_X(t)&\le1+b_X\cos t-\eta(1-\sin t).
\end{aligned}
\]
Testing the corresponding inner forbidden walls shows
\(n_X(x)=0\) outside \(J_X\).
For \(0\le d\le\eta\), maximizing the applicable single-wall
upper bound over all \(t\in(0,L)\) gives the **two true tip bounds**
\[
\boxed{
n_X(a_X+d)\le d^2/\eta,\qquad
n_X(b_X-d)\le d^2/\eta.
}
\tag{UFC.2}
\]
The first follows explicitly from the supremum of
\(d\tan t-\eta(\sec t-1)\), which equals
\(\eta-\sqrt{\eta^2-d^2}\le d^2/\eta\);
the other follows after reversing t.

Because \(A_X\ge1/2\) and \(n_X\le1/2\), the full two-turn
envelope E has nonempty interval fibers through y=1/2. Its
standard exact ordinary-area identity is
\[
G=\int_I[
  \min(n_U(x),1-A_V(x))+
  \min(n_V(x),1-A_U(x))]\,dx .
\]
The first integrand can be nonzero only on
\(J_U\setminus J_V\), because the niche of U vanishes outside
\(J_U\) and the V roof is identically one on \(J_V\).
For intervals, the difference \(J_U\setminus J_V\) is
contained in the two *end slivers*
\[
[a_U,a_U+d_{U,L}]\cup
[b_U-d_{U,R},b_U].
\]
This remains a valid **covering** even if the two intervals
are disjoint. Similarly the second integrand is supported
in the end slivers of \(J_V\).
Integrate UFC.2 over these slivers:
\[
G\le
\frac{d_{U,L}^3+d_{U,R}^3+
      d_{V,L}^3+d_{V,R}^3}{3\eta}.
\]
At each side precisely one of the two endpoint displacements
is positive; thus the numerator equals
\(|a_U-a_V|^3+|b_U-b_V|^3\), proving UFC.1.

**Scope.** UFC1 does not assert that arbitrary sofa caps
satisfy a curvature gap or a common midline. It gives the exact
cost *once those hypotheses are proved*, and does not by itself
show the weighted deficits dominate that cost. Its immediate
use is the genuinely infinite-dimensional smooth
near-reference theorem in
[SMOOTH-2CAP](smooth-two-cap-sharp-neighborhood.md).
No Lean, CI, optimization, or sampled-angle test is used.
