# 39. Explicit penalties select every maximizing hull at a quantified rate

The finite-angle repair theorem removes the dependence on the unknown numbers v_n-V in the penalty choice of Note 32. It also turns the selected finite-angle polygons into polygons satisfying both full continuous motions, with quantified area and hull errors.

This is an existence/approximation theorem with explicit bounds. The target maximizing hull still appears in the selection penalty, so the result is not an algorithm for finding that unknown hull.

## 39.1 A deterministic penalty schedule

Use N=2^n, L=pi/2, the box B and radius R_B from Note 38, and the finite-angle class F_n from Note 32. Choose a full-circle normal grid D_n, containing the axes, with angular gaps at most L/N. Fix the hull K_* of any prescribed normalized global maximizer and set

\[
r_n(K)=\max_{u\in D_n}|h_K(u)-h_{K_*}(u)|,
\qquad \kappa_n=N^{-1/2}.
\tag{39.1}
\]

Maximize

\[
|S|-\kappa_n r_n(\operatorname{conv}S)
\tag{39.2}
\]

over F_n. This upper semicontinuous objective attains a maximum by the same compactness proof as Note 32. Denote a selected body by C_n and its hull by K_n. The finite-envelope component construction in Section 32.3 allows C_n to be compact connected and polygonal while retaining every recorded support and the penalty.

The schedule kappa_n does not use V, v_n, or a convergence modulus for those values.

## 39.2 Quantitative convergence to the prescribed hull

Set

\[
e_n=R_B L/N,\qquad E_n=|B|(2e_n+e_n^2).
\]

The prescribed maximizer has penalty zero and is an admissible competitor. Corollary 77 therefore gives

\[
V\leq|C_n|\leq V+E_n,
\qquad r_n(K_n)\leq E_n/\kappa_n.
\tag{39.3}
\]

The difference of two support functions of hulls in B is 2R_B-Lipschitz in angle. A nearest grid normal lies within L/(2N), so

\[
d_H(K_n,K_*)\leq r_n(K_n)+e_n.
\]

In particular,

\[
\boxed{
d_H(K_n,K_*)
\leq |B|\left(2R_B L+\frac{R_B^2L^2}{N}\right)N^{-1/2}
+\frac{R_B L}{N}.
}
\tag{39.4}
\]

These bounds target any maximizing hull, without replacing it by a selected symmetric or specially regular optimizer.

## 39.3 Complete-motion polygonal approximants

Apply Theorem 76 and put

\[
T_n=\frac{C_n}{1+e_n}.
\]

These are compact connected polygonal bodies following both complete motions, with the same endpoint angles as their finite data. Since they are genuinely feasible,

\[
\frac{V}{(1+e_n)^2}\leq |T_n|\leq V,
\]

hence

\[
\boxed{0\leq V-|T_n|\leq \frac{E_n}{(1+e_n)^2}.}
\tag{39.5}
\]

Their hulls converge to K_* as well:

\[
d_H(\operatorname{conv}T_n,K_*)
\leq d_H(K_n,K_*)+\frac{R_B e_n}{1+e_n}.
\tag{39.6}
\]

The last term follows by pairing each point of K_n with its scaled image, using the radius bound. Thus the area error is O(N^-1) and the hull error is O(N^-1/2), with the constants displayed above.

**Theorem 78 (quantified arbitrary-maximizer selection).** For every normalized maximizing hull K_*, the explicit penalty (39.2) has polygonal selected representatives satisfying (39.3)–(39.4). Their repaired versions satisfy both full continuous motions and the quantitative bounds (39.5)–(39.6).

**Proof.** Comparison with the zero-penalty target, the finite-angle value bound, the support-grid estimate, and the repair construction give each displayed inequality. QED.

The selected hull convergence does not assert Hausdorff convergence to every possible original maximizing body sharing that hull. Exact body recovery still requires the saturation/equality argument.

## 39.4 The exact variational error retained by the finite optimizers

For every T in the same finite class,

\[
|T|-|C_n|
\leq\kappa_n\max_{u\in D_n}
|h_{\operatorname{conv}T}(u)-h_{K_n}(u)|.
\tag{39.7}
\]

This is the same reverse-triangle argument as Theorem 67, now with an explicit kappa_n. For an admissible two-sided differentiable variation with sampled support displacement at most A_n|s|,

\[
\left|\frac{d}{ds}|T_s|\bigg|_{s=0}\right|
\leq A_nN^{-1/2}.
\tag{39.8}
\]

A uniform bound on A_n, or merely A_n=o(sqrt(N)), makes this error vanish. Neither bound has been proved for arbitrary floating-edge/endpoint variations.

The repaired bodies T_n are not asserted to maximize a corresponding full-motion penalty. Their role is complete-motion approximation; equation (39.7) belongs to the unscaled finite-class optimizers C_n. Conflating the two would create a false stationarity conclusion.

## 39.5 Consequence and remaining work

Unknown relaxation rates and a penalty depending on the unknown optimum are no longer obstacles to the selection stage. The missing measure-level argument is now more sharply localized: construct genuinely admissible finite variations, compute their visible/active contact contributions, and control their support amplification well enough to use (39.8).

The finite repair cost cannot simply be suppressed to declare an inadmissible variation admissible. Full-angle endpoints, curvature/contact structure, and exact uniqueness of unrestricted maximizers remain unproved.
