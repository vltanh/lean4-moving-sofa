# 32. Finite-angle selection can target every maximizing hull

This note supplies a rigorous selection framework for a future two-turn variation proof. It does not compute the missing curvature balance. Its useful feature is that it can target the hull of **any specified global maximizer**, rather than only a convenient maximizing limit. That distinction is needed for an eventual uniqueness theorem.

The construction is pen-and-paper and noncomputational. It does not run a search, a solver, CI, or Lean.

## 32.1 Compact finite-angle relaxations

Let B be the fixed box from Proposition 54, let A_0=8/5, and put theta_0=arccos(1/A_0). Let V be the attained unrestricted maximum from Theorem 55. Fix a maximizing body S_* in its normalized representative and write K_*=conv(S_*).

For n>=1, consider triples (S,alpha,gamma) with:

- S a nonempty compact connected subset of B, with vertical span one and area at least A_0;
- alpha,gamma in [theta_0,pi/2], with the two outgoing hull widths at most one;
- the lower canonical hallway inclusion imposed at t=k alpha/2^n, and the upper inclusion at t=-k gamma/2^n, for every k=0,...,2^n.

Call this class F_n. It is compact in Hausdorff distance for S and ordinary distance for the endpoints. Connectedness, the support-dependent finite hallway inclusions, span, and endpoint widths are closed by the arguments in Note 25. The area condition |S|>=A_0 is closed because area is upper semicontinuous on compact subsets of B.

The area functional attains a maximum v_n on F_n. The classes are nested, and every normalized genuinely feasible competitive body belongs to each class. Thus

\[
v_n\geq V,\qquad v_{n+1}\leq v_n.
\]

**Lemma 66 (exact convergence of finite-angle upper values).**

\[
v_n\downarrow V.
\tag{32.1}
\]

**Proof.** Choose an area maximizer in each F_n and pass to a compact subsequential limit. For every fixed dyadic fraction r, all sufficiently fine members obey the two inclusions at r alpha_n and -r gamma_n. The limiting triple obeys them at the limiting endpoints. Continuity of the canonical paths extends the inclusions from the dense set of dyadic fractions to both complete angular intervals. Endpoint widths pass to the limit, so the limit is a genuine two-turn body. Upper semicontinuity of area gives V>=lim v_n. The opposite inequality was already noted. QED.

This proof does not provide a convergence rate or a numerical upper bound. A finite value v_n is an exact variational quantity, not an experimentally estimated number.

## 32.2 A vanishing penalty selects the prescribed hull

Let D_n be the full-circle dyadic normal grid, including all four axis normals, and define

\[
r_n(K)=\max_{u\in D_n}|h_K(u)-h_{K_*}(u)|.
\]

For hulls in B, the sampled support distance converges uniformly to Hausdorff distance. Indeed both support functions have a common Lipschitz bound on the unit circle, so an angular grid of mesh eta_n gives

\[
0\leq d_H(K,K_*)-r_n(K)\leq C_B\eta_n,
\qquad\eta_n\to0.
\tag{32.2}
\]

Put delta_n=v_n-V and choose

\[
\varepsilon_n=\sqrt{\delta_n}+2^{-n}>0.
\]

Maximize, over F_n, the upper semicontinuous objective

\[
\Phi_n(S)=|S|-\varepsilon_n r_n(\operatorname{conv}S).
\tag{32.3}
\]

It attains a maximum. Let S_n be a maximizer and K_n=conv(S_n). Since S_* is an admissible competitor with penalty zero,

\[
|S_n|-\varepsilon_n r_n(K_n)\geq V,
\qquad |S_n|\leq v_n.
\]

Consequently

\[
r_n(K_n)\leq\delta_n/\varepsilon_n\leq\sqrt{\delta_n}\to0,
\qquad V\leq|S_n|\leq v_n\to V.
\tag{32.4}
\]

Together with (32.2), this proves K_n->K_* in Hausdorff distance.

The choice of epsilon_n is an existence device. It uses the mathematically defined values V and v_n; it is not claimed to be an effective algorithm for computing those values.

## 32.3 The selected bodies can be polygonal saturated components

For a selected triple, form the finite envelope E_n by intersecting B with:

- its finitely many canonical hallway placements;
- its incoming and terminal supporting strips;
- the supporting half-planes p dot u<=h_{K_n}(u) for every u in D_n;
- the supporting half-planes in every other normal used by those finite placements and endpoint strips, including the opposite normals.

The last extra half-planes are redundant for the original S_n, but make preservation of all the recorded support data explicit. The envelope contains S_n. It is a finite Boolean combination of half-planes in a bounded box. Each of its components is a compact polygonal set, allowing segments and point contacts as well as two-dimensional cells.

Let C_n be the component containing S_n. For every recorded normal u,

\[
h_{K_n}(u)\leq h_{\operatorname{conv}C_n}(u)\leq h_{K_n}(u),
\]

where the first inequality uses containment and the second uses its retained supporting half-plane. Thus equality holds at every recorded normal. The canonical placements, endpoint widths, and sampled penalty are unchanged. The body C_n belongs to F_n and has area at least |S_n|. Maximality of (32.3) forces equality of its penalized objective, so it too may be chosen as a penalized maximizer.

This construction retains connectedness explicitly. It does not replace the body by the entire possibly disconnected finite envelope, nor assume that its unsampled support values remain unchanged. The latter are controlled in the limit by the dense auxiliary grid.

## 32.4 The resulting variational inequality

**Theorem 67 (selection of every maximizing hull).** For each specified maximizing hull K_*, there are compact connected polygonal finite-angle penalized maximizers C_n such that

\[
\operatorname{conv}(C_n)\to K_*,
\qquad |C_n|\to V,
\qquad\varepsilon_n\to0.
\tag{32.5}
\]

For every competitor T in the same finite class F_n,

\[
|T|-|C_n|
\leq\varepsilon_n
\max_{u\in D_n}|h_{\operatorname{conv}T}(u)-h_{\operatorname{conv}C_n}(u)|.
\tag{32.6}
\]

**Proof.** The selection and component saturation above prove (32.5). Optimality of the penalized objective gives
\(|T|-|C_n|\leq\varepsilon_n[r_n(\operatorname{conv}T)-r_n(\operatorname{conv}C_n)]\).
The reverse triangle inequality for the finite maximum norm gives (32.6). QED.

In particular, if an admissible two-sided variation T_s has sampled support displacement at most L_n|s| and differentiable area at zero, then

\[
\left|\frac{d}{ds}|T_s|\bigg|_{s=0}\right|\leq\varepsilon_n L_n.
\tag{32.7}
\]

A one-sided variation gives the corresponding one-sided inequality. A uniform bound on L_n would make this an approximate balance tending to zero. Such a bound must be checked for the proposed variation; it is not assumed for arbitrary moving-vertex perturbations.

## 32.5 What selection does not solve

This selects the **hull** of every maximizer. It does not assert convergence to a prescribed original body as a set, which is not needed to derive a hull-curvature theorem. Exact body recovery would still use the equality/saturation argument at the end of Theorem 65.

The missing work is to construct admissible support/angle variations, evaluate their area changes with the correct visible and active-contact terms, control any amplification L_n, and derive the required curvature/contact inequalities in the limit. The finite-angle selection theorem does not turn the invalid full-edge balance from Note 21 into a valid identity.

Nevertheless, attainment and arbitrary-maximizer selection are now available without invoking the desired upper bound or uniqueness. The remaining structural argument can be formulated noncircularly for every maximizing hull.
