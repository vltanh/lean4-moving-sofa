# 2. Select the specified maximizer; retain only the needed stationarity

The main simplification in this section is that the penalty is sampled at normals already defining the polygon. A floating-facet variation changes exactly one sampled support value. No estimate of a sine hat on the full circle, and no coupling of a vanishing penalty coefficient to the angular mesh, is needed.

## 2.1 An abstract fixed-penalty selection theorem

Let X be a compact metric space, with nonempty compact approximation spaces X_n contained in X. Let F_n be continuous on X_n. Suppose F is an objective on X and

\[
x_{n_j}\in X_{n_j},\quad x_{n_j}\to x
\quad\Longrightarrow\quad
\limsup_j F_{n_j}(x_{n_j})\le F(x).                    \tag{2.1}
\]

Let continuous observations \(\ell_j:X\to\mathbb R\) separate points, and let \(w_j>0\), \(\sum_jw_j\le1\). Fix a global maximizer \(x_*\) of F. Suppose recovery points \(r_n\in X_n\) satisfy

\[
\ell_j(r_n)=\ell_j(x_*)\quad(j\le n),\qquad
F_n(r_n)\ge F(x_*)-\epsilon_n,\quad \epsilon_n\to0.
\]

Define

\[
P_n(x)=\sum_{j\le n}w_j|\ell_j(x)-\ell_j(x_*)|^2.
\]

**Theorem 2.1.** Every sequence of exact maximizers \(x_n\) of \(F_n-P_n\) on X_n converges to \(x_*\). Also \(P_n(x_n)\to0\).

**Proof.** Recovery and maximality give

\[
F(x_*)-\epsilon_n\le F_n(x_n)-P_n(x_n).             \tag{2.2}
\]

Take any convergent subsequence, with limit x. Equations (2.1)-(2.2) and \(F(x)\le F(x_*)\) imply

\[
0\le\limsup_jP_{n_j}(x_{n_j})\le F(x)-F(x_*)\le0.
\]

For each fixed observation index i, eventually i is included, so

\[
0\le w_i|\ell_i(x_{n_j})-\ell_i(x_*)|^2\le P_{n_j}(x_{n_j})\to0.
\]

Continuity and \(w_i>0\) show \(\ell_i(x)=\ell_i(x_*)\). Separation gives \(x=x_*\). Every accumulation point is therefore x_*, and compactness proves convergence of the full sequence. Applying (2.1)-(2.2) again proves convergence of the penalties. \(\square\)

The same proof works when only the selected superlevel sets are uniformly precompact. One first obtains the compactness bound; it must not be assumed as a consequence of convergence.

**Two failed shortcuts.** On [0,1], \(F_n(x)=x/n\) converges uniformly to zero, but its unpenalized maximizers are always 1. They do not select the specified limiting maximizer 0. Nor is an arbitrarily weakened penalty sufficient: maximizing \(x/n-x^2/n^2\) still selects 1 for n>2, even though that penalty tends to zero there. Persistence of a positive weight for each fixed observation is the identifying mechanism.

## 2.2 The cap specialization

Write L=pi/2. For a fixed angle \(0<\omega\le L\), let \(\mathcal K_\omega\) be the normalized cap space defined in the main manuscript. Use nested dyadic sets \(\Theta_n\subset(0,\omega)\), including a fixed coarsest angle \(t_0\) at every stage. Let \(C_n(K)\) be the circumscribed cap defined by the two strips and the supporting normals in \(\Theta_n\cup(\Theta_n+L)\). Let \(N_n(K)\) be the union of the corresponding open inner wedges, intersected with the entire fan, and set

\[
A_n(K)=|C_n(K)|-|N_n(K)|.
\]

For polygon caps at stage n, C_n(K)=K. Enumerate the sampled upper normals by first occurrence, keeping each weight fixed thereafter. Both \(t_0\) and \(t_0+L\) receive positive weights. Repeated normals can equivalently be grouped into a total weight \(w_n(t)\), with \(\sum_t w_n(t)\le1\).

The observations are \(\ell_t(K)=h_K(t)\). Dense upper supports and the fixed lower fan inequalities determine a cap. The recovery polygon C_n(K_*) contains K_* and uses its supporting heights, hence

\[
h_{C_n(K_*)}(t)=h_{K_*}(t)
\]

at every sampled normal: containment gives one inequality, and the defining half-plane gives the other. Its penalty is exactly zero, and A_n(K_*)>=A_omega(K_*).

**One-sided convergence, not uniform convergence.** If bounded stage-n polygons K_n converge in Hausdorff distance to K, convex area continuity gives |K_n|->|K|. Any point of N_omega(K) satisfies two strict inner inequalities at some interior angle. Density of the nested mesh and uniform convergence of support functions place that point in N_n(K_n) eventually. Fatou's lemma consequently gives

\[
|N_\omega(K)|\le\liminf_n|N_n(K_n)|,
\quad
\limsup_nA_n(K_n)\le A_\omega(K).                  \tag{2.3}
\]

For the first assertion, choose a nearby angle from one fixed coarse mesh; it remains in every finer mesh. There is no need to interchange an uncontrolled angular infimum with a limit. A common bound for the relevant sets supplies finiteness. In fact Fatou's inequality itself needs no such bound.

**Compactness before selection.** We retain the following local geometric input from Baek's Lemma 3.4.2: for fixed omega and t_0, positive finite cap objective implies a common horizontal width bound c(omega,t_0), independently of the finer mesh. Because polygon caps have height one, A_n(K)<=|K|<=c. If the penalized objective is at least a positive recovery value, P_n(K)<=c. The two persistent observations therefore bound h_K(t_0) and h_K(t_0+L) relative to their target values. These two independent directions, the width bound, and the unit-height strip give a common coordinate box. This controls horizontal translation even at omega=L.

For fixed n the polygon objective is continuous in its finite defining heights, including zero-length facets; alternatively it is the area of finite unions/intersections of half-planes. The constrained cap conditions are closed. Maximization on the compact positive superlevel set therefore supplies an exact maximizer of A_n-P_n. Blaschke compactness and (2.3) permit Theorem 2.1. For every specified cap K_* with positive value that maximizes A_omega, we obtain

\[
K_n\longrightarrow K_*,\qquad
\eta_n:=\|h_{K_n}-h_{K_*}\|_\infty\longrightarrow0.        \tag{2.4}
\]

No statement that K_n maximizes A_n alone is made. In particular K_n is not declared balanced, connected, or niche-containing.

The finite objective continuity, width bound, closure of the cap family, and finite first-variation geometry used below are retained pre-optimality inputs. They are not consequences of Theorem 2.1. See the dependency ledger for the precise source boundary.

## 2.3 Floating facets: only one penalty summand changes

For a polygon cap P, let sigma_P(t) be its facet length. Let tau_P(t) be the total length of edges with upper normal t in the completed inner-boundary polyline. This polyline and the upper boundary of P have the same endpoints. Set

\[
d_P(t)=\sigma_P(t)-\tau_P(t).
\]

The finite geometric variation formula is

\[
A_n^{\rm assigned}(P_{t,\varepsilon})-A_n(P)
=d_P(t)\varepsilon+O(\varepsilon^2),\quad\varepsilon\downarrow0.       \tag{2.5}
\]

Here an upper defining line is moved outward. For a pinned normal the opposite strip line is moved with it. Formula (2.5) is Baek's local Nef-polygon area calculation, not a balance assumption.

Suppose t is floating, \(\sigma_P(t)>0\), and only its assigned height is increased. For sufficiently small positive epsilon the moved line still meets a facet. The new polygon contains P; every unchanged defining line still attains its old support value, by containment and its unchanged upper bound. Thus, at the sampled normals,

\[
h_{P_{t,\varepsilon}}(s)-h_P(s)=
\begin{cases}\varepsilon&s=t,\\0&s\ne t.\end{cases}
\]

This remains true when an adjacent defining constraint had a zero-length facet. No two-sided perturbation is asserted.

For the selected P=K_n, the exact penalty increment is

\[
P_n(P_{t,\varepsilon})-P_n(P)
=2w_n(t)(h_P(t)-h_{K_*}(t))\varepsilon+w_n(t)\varepsilon^2.
\]

Maximality of A_n-P_n, followed by epsilon->0 at fixed n, gives

\[
d_{K_n}(t)\le2\eta_n w_n(t).                      \tag{2.6}
\]

If sigma_P(t)=0, this bound holds without a perturbation because tau_P(t)>=0. Summing (2.6) over any collection of floating normals costs at most 2 eta_n. There is no factor equal to the number of facets.

This is why persistent samples are better suited to this proof than a continuous support penalty whose derivative requires endpoint sine-hat estimates.

## 2.4 Pinned facets and the sign of the actual/assigned comparison

Now fix omega<L. The pins are omega and L. At a positive pinned facet, the finite perturbation lemma supplies a translated normalized polygon after the relevant unit strip is moved. The translation is fixed by the two distinct strip normals.

A mesh-independent support estimate is needed here. It cannot be inferred from bounded diameter alone. One way to obtain it is the following elementary sandwich. If B(q,rho) is contained in P and each normalized defining height changes by at most a epsilon, then for delta=a epsilon/rho<1,

\[
(1-\delta)P+\delta q\ \subseteq\ P'\ \subseteq\ (1+\delta)P-\delta q.     \tag{2.7}
\]

For the first inclusion substitute into every half-plane inequality. For the second apply the original inequalities to q+(p'-q)/(1+delta). Both use h_P(u)-q.u>=rho. A bounded family then satisfies d_H(P',P)<=C epsilon. Normalizing the two strip heights adds an O_omega(epsilon) translation.

For fixed omega<L, normalized caps contain a common nondegenerate triangle: with c=sec(omega)-tan(omega) and o=(c,1), the triangle conv{O,(c,0),o} is contained in every cap. Supporting contacts at the two upper strip lines show h_K(t)>=o.u_t on their two allowed upper intervals; vertical lowering to the fan boundary gives the other vertices. Thus (2.7) has a common rho. This use is restricted to omega<L; the triangle degenerates at a right angle.

It follows that the actual normalized perturbation obeys

\[
|P_n(P')-P_n(P)|\le2C_\omega\eta_n\varepsilon+C_\omega^2\varepsilon^2.   \tag{2.8}
\]

There is a further issue: after a pinned perturbation, an assigned height need not be the actual support height. The half-plane intersection is unchanged when redundant bounds are tightened to actual supports, whereas the actual niche can only shrink. Hence

\[
A_n^{\rm actual}(P')\ge A_n^{\rm assigned}(P').             \tag{2.9}
\]

This is the direction needed to combine maximality of the actual penalized objective with (2.5). Equations (2.8)-(2.9) yield

\[
d_{K_n}(k)\le2C_\omega\eta_n,\qquad k\in\{\omega,L\}.    \tag{2.10}
\]

For zero-length pinned facets, again d<=0. The admissible epsilon may depend on n and the facet. All first-variation limits are taken before n->infinity; uniform admissible step sizes are unnecessary.

Following the upper and completed inner boundary walks gives the exact endpoint identity

\[
\sum_t d_{K_n}(t)v_t=0,
\qquad\sum_t\sin t\,d_{K_n}(t)=0.                         \tag{2.11}
\]

Every allowed upper normal lies strictly between 0 and pi. Since sin t<=1, (2.6) and (2.10) bound the sum of positive sine-weighted defects by (2+4C_omega)eta_n. Equation (2.11) gives the same bound for the negative defects. In particular

\[
|d_{K_n}(k)|\le\frac{(2+4C_\omega)\eta_n}{\sin k}
\longrightarrow0,\quad k\in\{\omega,L\}.                  \tag{2.12}
\]

Only a fixed pinned sine appears in this denominator; there is no division by the smallest mesh angle.

## 2.5 Pass the pin inequalities to the specified cap

The finite inner-boundary geometry gives

\[
w_{K_n}^{\circ}\le\tau_{K_n}(L),\qquad
z_{K_n}^{\circ}\le\tau_{K_n}(\omega).                       \tag{2.13}
\]

These are inequalities for the completed inner boundary, not assertions of balance. The gap infima are Hausdorff-continuous for fixed omega<L: the intercept formula bounds their change by (1+sec omega)eta_n. Curvature measures converge weakly under Hausdorff convergence of convex bodies. Upper semicontinuity of a fixed atom gives

\[
\limsup_n\sigma_{K_n}(\{k\})\le\sigma_{K_*}(\{k\}).
\]

Combine this with (2.12)-(2.13) to obtain

\[
w_{K_*}^{\circ}\le\sigma_{K_*}(\{L\}),\qquad
z_{K_*}^{\circ}\le\sigma_{K_*}(\{\omega\}).                 \tag{2.14}
\]

The target cap has not changed at any point of the argument.

## 2.6 Endpoint-safe curvature bounds

At omega=L, only the floating estimates (2.6) are needed. The three-neighbor inner-ray calculation, before any maximality assumption, gives for a first-quadrant mesh normal t

\[
\tau_P(t)\le\tan\delta\bigl(|g_P^+(t)-1|+\tan(\delta/2)\bigr)
 +\bigl(2\tan(\delta/2)-\sigma_P(\{t\})\bigr)_+.            \tag{2.15}
\]

Here is the local geometric decomposition behind this input. Split the exposed inner half-ray using the three opposite inner half-planes at t-delta,t,t+delta. The part in their union has length at most the first term in (2.15), using g^-<=g^+. The remaining interval is cut out by the three same-side inner lines; its signed length is 2 tan(delta/2)-sigma_P({t}). Its nonnegative length is the positive part. At the two extreme cells use the virtual endpoint hallways, whose inner quadrants miss the fan. No balance or niche containment is used.

Write e_n(t)=2 eta_n w_n(t). Substituting (2.6) into (2.15) and separating the cases sigma_P({t})>=2 tan(delta/2) and sigma_P({t})<2 tan(delta/2) gives, for uniformly bounded caps,

\[
\sigma_{K_n}(\{t\})\le\delta_n k(g_{K_n}^+(t))
   +C\delta_n^2+e_n(t),\qquad\sum_t e_n(t)\le2\eta_n\to0.    \tag{2.16}
\]

The bound follows from tan delta=delta+O(delta^3), uniformly for sufficiently small delta; bounded arm lengths control the constants. The first case has leading term delta|g-1|; the second has delta(|g-1|+1)/2. Their maximum is exactly k(g).

Spread each first-quadrant curvature atom uniformly over the cell immediately preceding its mesh normal. Equation (2.16) bounds the spread measure by a step-function density plus an error measure of total mass O(delta_n)+2eta_n. Moving an atom within its cell changes an integral against a continuous test function by at most its modulus of continuity at delta_n times the bounded perimeter.

At almost every normal, the limiting support point is unique. Hausdorff convergence then forces support points at converging normals to converge. Thus the bounded step densities converge almost everywhere to k(g_{K_*}^+); dominated convergence applies. Testing on a circular arc crossing normal zero and ending before L gives

\[
\sigma_{K_*}|_{[0,L)}\le k(g_{K_*}^+(t))\,dt.               \tag{2.17}
\]

The selected polygons have no curvature atom at zero and no mass just below it. Nevertheless this alone would not exclude concentration there in the limit: (2.16), including its summed errors, is what excludes it. Equation (2.17) proves sigma_{K_*}({0})=0.

Reflect the cap horizontally. Reflection preserves cap maximality and sends normal t to pi-t, exchanging g^+ with f^-. Applying (2.17) to that specified reflected cap yields

\[
\sigma_{K_*}|_{(L,\pi]}\le k(f_{K_*}^-(t-L))\,dt.           \tag{2.18}
\]

This proves absence of the atom at pi as well. A top atom at L is permitted throughout.

The distribution identity h''+h=sigma now gives separate C1 restrictions with absolutely continuous first derivatives on the two closed half-intervals. Set

\[
f(t)=h(t+L)-h'(t),\qquad g(t)=h(t)+h'(t+L),
\]

using the appropriate one-sided values at L. These arms are nonnegative; the end-atom conclusions and the bottom-segment geometry give f(0)=g(L)=1. With the two curvature densities r,s,

\[
f'=g-r\ge m(g),\qquad -g'=f-s\ge m(f)
\]

almost everywhere. Integration supplies (1.2), so Theorem 1.1 gives the strict arm estimates needed for injectivity.

## Scope and dependency discipline

This section derives two consequences of specified-cap maximality: pinned edge bounds and right-angle curvature bounds. It does not infer that an arbitrary cap is feasible, and it never uses |S|<=|G|. The finite geometric inputs retained from Baek are listed explicitly in the main paper and dependency ledger. Their use has not been replaced by an assertion that the uncompiled Lean scripts verify them. The new limiting/selection arguments and their endpoint details still require independent mathematical review.
