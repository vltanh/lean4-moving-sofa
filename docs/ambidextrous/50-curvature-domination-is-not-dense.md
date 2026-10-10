# 50. The curvature-dominated class is closed, not dense in feasible hulls

This records a precise obstruction to one possible shortcut in the remaining structural proof. Feasible rounding and polygonal approximation do not imply that a given hull can be approximated arbitrarily closely by hulls with curvature bounded by one. The latter class is closed in uniform support distance, and a curvature violation has an explicit positive distance from it.

The result is elementary distributional duality, with a concrete bound for an exposed-edge atom. It is consistent with the improving repair in Note 48: that repair is allowed to move the hull by a nonzero amount and to increase actual area.

## 50.1 A separating test function

Let J be an open coordinate quarter and let sigma_h=h+h'' be the curvature measure of a convex support function h. If phi is a nonnegative smooth function compactly supported in J, define

\[
D_\phi(h)=\int_J\phi\,d\sigma_h-\int_J\phi\,dt.
\]

For any other support function k satisfying sigma_k<=dt on J,

\[
D_\phi(h)\leq\int_J\phi\,d(\sigma_h-\sigma_k)
=\int_J(h-k)(\phi+\phi'')\,dt.
\]

Therefore, whenever D_phi(h)>0,

\[
\boxed{\|h-k\|_\infty\geq
\frac{D_\phi(h)}{\|\phi+\phi''\|_{L^1(J)}}>0.}
\tag{50.1}
\]

The denominator cannot vanish for a nonzero compactly supported phi: the equation phi''+phi=0 and zero exterior data would force phi=0.

**Theorem 94 (closedness and separation).** Curvature domination sigma_h<=dt on J is closed under uniform convergence of support functions. If it fails, h has positive uniform-support distance from that class, witnessed by (50.1).

**Proof.** For a uniformly convergent sequence k_n->h with sigma_{k_n}<=dt, test against any nonnegative smooth compactly supported phi and pass to the limit in integral k_n(phi+phi''). This yields integral phi d sigma_h<=integral phi, which is the measure inequality. If domination fails, the signed Radon measure sigma_h-dt is positive on some nonnegative continuous compactly supported test, and approximation gives a nonnegative smooth test with positive value. Equation (50.1) then separates h from every dominated k. QED.

Translation modes do not change the curvature measure. Consequently the same lower bound applies after any translation of k that is allowed in the chosen normalization; it is not an artifact of a badly chosen origin.

## 50.2 An explicit obstruction from an edge atom

Suppose sigma_h has an atom of mass m>0 at an interior normal t_0. Assume r=m/4<=1 and [t_0-r,t_0+r] lies compactly inside J. Use the nonnegative C¹, piecewise C² test

\[
\phi(t)=\left(1-\frac{(t-t_0)^2}{r^2}\right)^2
\quad\text{for }|t-t_0|\leq r,
\qquad\phi=0\text{ otherwise}.
\tag{50.2}
\]

Its first derivative vanishes at both endpoints, so its second distributional derivative has no endpoint atoms. Smooth approximation, or integration by parts directly, makes (50.1) applicable. Direct integration gives

\[
\int\phi=\frac{16r}{15},\qquad
\int|\phi''|=\frac{32}{3\sqrt3\,r}<\frac8r.
\]

Since phi(t_0)=1 and sigma_h is nonnegative,

\[
D_\phi(h)\geq m-16r/15=11m/15\geq m/2.
\]

For every k with sigma_k<=dt on J, (50.1) therefore gives

\[
\|h-k\|_\infty
\geq\frac{m/2}{16r/15+8/r}
\geq\frac{15mr}{272}
>\frac{mr}{20}=\frac{m^2}{80}.
\tag{50.3}
\]

The middle inequality uses r<=1. For smaller available angular room one can choose any smaller r with 16r/15<=m/2 and retain the preceding bound with that r.

Thus even a small exposed-edge atom cannot be removed while making the support change arbitrarily small at fixed m. In the explicit atom family of Note 49, m=2epsilon, so the separation is at least epsilon²/20 once the window condition holds.

## 50.3 What this says about the remaining maximizer argument

The finite-angle selection theorems approximate an arbitrary maximizing hull by polygonal optimizers with controlled variational errors. To conclude domination in the limit, one must actually prove the appropriate curvature-measure inequalities or bounds on their atomic masses. One cannot impose the desired conclusion on an arbitrarily close comparison hull merely by invoking general smoothing or density.

The feasible near-candidate bodies in Note 49 are concrete tests: they can be as close to optimal in area as desired, yet each fixed singular example lies a positive distance from the dominated class. The improving repair compares its area to a different hull; it does not contradict this separation.

This leaves maximality, an admissible improvement operation, or a covering sharp comparison as the necessary source of the unrestricted curvature conclusion. The statement is an obstruction to a shortcut, not a counterexample to candidate optimality or to the already proved local repair theorem.
