# Stationarity, deficit, and rigidity for Gerver's sofa

## A dependency-explicit reorganization of the moving sofa argument

**Working research manuscript — 3 October 2026.** This manuscript is a proposed mathematical proof relative to the geometric toolkit identified below. It is not an independently reviewed result or a machine-checked formalization. The accompanying repository uniqueness source is uncompiled and is not used as evidence that a mathematical step is correct. Authorship and publication decisions are left to the repository maintainers.

### Abstract

We reorganize the moving sofa argument around three principles: selection of a specified cap maximizer by a persistent sampled penalty, a maximum-deficit estimate for the coupled arm inequalities, and an exact affine-minus-squares decomposition of the terminal area bound. The scalar estimate replaces a finite iteration by a single contradiction argument and admits uniform additive errors. The quadratic identity proves the upper bound and exposes the equality equations simultaneously; solving four first-order equations identifies the entire cap up to horizontal translation and gives a Hausdorff-distance estimate on the injective cap domain. We distinguish numerical domination, which suffices for optimality, from actual containment, which is essential for uniqueness of a specified starting sofa. A pre-optimality feasible-attainment theorem from Baek is retained explicitly: maximizing a cap functional does not automatically yield a connected sofa. Subject to the retained geometric inputs, the resulting order of proof establishes optimality before using it to recover every equality case. It is therefore a reorganization of Baek's framework, not a claimed independent replacement of all of its geometry or a proof that the balanced-maximizer existence layer can simply be deleted.

## Contents and reading order

The main text gives definitions, the exact dependency boundary, and the global argument. The four companion sections are integral parts of the manuscript and contain its detailed proofs:

1. [Maximum-deficit arm bootstrap, robust version, and a counterexample](01-arm-bootstrap.md).
2. [Specified-maximizer selection and the two stationarity consequences](02-selection-and-stationarity.md).
3. [Exact deficit identity, equality kernel, and quantitative cap rigidity](03-deficit-and-rigidity.md).
4. [Same-sofa angular extension and exact-set recovery](04-angle-and-set-recovery.md).

The [dependency ledger](DEPENDENCIES.md) and [research log](RESEARCH_LOG.md) record what is retained, what is new, and what has not been checked.

## 1. The question and the scope of the simplification

Let H=(-infinity,1] times [0,1] and V=[0,1] times (-infinity,1], and let the hallway be H union V. A moving sofa is a nonempty closed connected set that a continuous path of orientation-preserving rigid motions carries from H to V while remaining in the hallway. Initial translations are allowed in the paper presentation. In the identity-start presentation the set is already in H and the first isometry is the identity.

Let G denote the concrete Gerver construction, not an arbitrarily chosen maximizing set, and write M=|G|. The target is

\[
|S|\le M,\qquad |S|=M\ \Longleftrightarrow\ S\text{ is congruent to }G          \tag{1.1}
\]

for moving sofas S. Congruence is equality of sets under a Euclidean isometry.

Baek [B] proves optimality using cap geometry, special limiting maximizers, injectivity, and a quadratic bound. This manuscript keeps the cap geometry and the construction and first variation of that bound. It changes the organization of the stationarity, scalar bootstrap, and equality arguments. In particular, the new work is not obtained by citing the completed uniqueness statement to prove optimality; that would be circular.

Three different levels of simplification should not be confused.

**Local simplification.** Theorem 1.1 of the companion arm section replaces the iteration in [B, Section 6.5] while leaving the rest of Baek's proof intact. This is the smallest change and does not depend on the new variational theory.

**Integrated reorganization.** Persistent sampled penalties provide the two stationarity consequences for a specified maximizer. The same analytic ingredients then support optimality and uniqueness, with a single terminal deficit identity. This is the main route written here.

**Fully balance-free proof.** To remove the existing balanced-maximizer existence theory as well, one must prove feasible attainment independently. We do not claim that the present argument accomplishes this. Renaming that input would not remove its mathematical content.

## 2. Caps, niches, and two distinct optimization problems

Put L=pi/2, u_t=(cos t,sin t), and v_t=(-sin t,cos t). For a compact convex set K write h_K(t)=sup{p.u_t:p in K}; sigma_K is its curvature measure on the circle of normal directions. In distributions, h_K''+h_K=sigma_K. At a polygon normal, sigma_K({t}) is the corresponding facet length.

For 0<omega<=L let

\[
F_\omega=\{p:p_y\ge0,\ p\cdot u_\omega\ge0\},\quad
P_\omega=\{p:0\le p_y\le1,\ 0\le p\cdot u_\omega\le1\},
\quad J_\omega=[0,\omega]\cup[L,L+\omega].
\]

A normalized omega-cap is a nonempty compact convex set represented by the lower fan inequalities and its upper supports on J_omega, with upper strip supports h_K(omega)=h_K(L)=1 and lower strip supports h_K(omega+pi)=h_K(3L)=0. Thus

\[
K=F_\omega\cap\bigcap_{t\in J_\omega}\{p:p\cdot u_t\le h_K(t)\}.
\]

Define the open inner quadrant

\[
Q_K^-(t)=\{p:p\cdot u_t<h_K(t)-1,\ p\cdot v_t<h_K(t+L)-1\}
\]

and the niche

\[
N_\omega(K)=F_\omega\cap\bigcup_{0<t<\omega}Q_K^-(t).
\]

The relaxed cap functional is

\[
A_\omega(K)=|K|-|N_\omega(K)|.                              \tag{2.1}
\]

For the cap of a monotone sofa T, one has N_omega(K) contained in K and T=K minus N_omega(K), so A_omega(K)=|T|. But this need not hold for an arbitrary cap. Always,

\[
|K\setminus N_\omega(K)|=A_\omega(K)+|N_\omega(K)\setminus K|.             \tag{2.2}
\]

Moreover K minus N_omega(K) can be disconnected. The relaxed cap maximum and the feasible connected-sofa maximum are not interchangeable by definition.

### A concrete warning

Take the right-angle cap K=[0,4] times [0,1]. At t=pi/4 its inner corner is (2,3-sqrt(2)), above K. The entire vertical segment {2} times [0,1] lies strictly inside that inner quadrant, while the two bottom endpoints (0,0),(4,0) survive every inner quadrant. Hence K minus N_L(K) is disconnected. This is not a maximizing cap; it demonstrates why a feasibility theorem cannot be omitted merely because the defining object is a cap.

## 3. The retained geometric toolkit

The following are inputs, with their pre-optimality sources stated explicitly. None is the final assertion that all sofas have area at most M.

### G1. Monotonization and angle reduction

Moving sofas are bounded. A sofa of area at least a_0:=11/5 has an admissible rotation angle omega in [arcsec(a_0),L]. After a translation it lies in its own monotonization T, a moving sofa of that angle, and the own cap K of T satisfies T=K minus N_omega(K) and A_omega(K)=|T|. These are the angle and monotone-sofa results in [B, Theorem 1.5.1 and Chapter 2].

### G2. Feasible attainment at fixed angle

For each 0<omega<=L there is a cap C_omega maximizing A_omega over all normalized omega-caps such that N_omega(C_omega) is contained in C_omega. The set T_omega=C_omega minus N_omega(C_omega) is a monotone moving sofa and its area equals the maximum cap value.

This is the content retained from [B, Theorems 3.5.2, 3.5.4-3.5.6]. Its original proof uses limits of balanced polygon maxima. We use the resulting feasible-attainment fact, and do not claim to have replaced its proof.

### G3. Local finite-angle geometry

We retain finite polygon objective continuity and the positive-superlevel width bound; the completed inner-boundary polyline and its endpoint identity; the one-sided assigned-height derivative sigma-tau; and the feasibility of an outward move at a positive facet. We also retain the local three-neighbor inner-ray geometry and the polygon gap-to-inner-edge inequalities. Their precise uses and references are recorded in the companion stationarity section and dependency ledger.

These facts concern arbitrary finite polygon caps where stated, not only unpenalized maximizers. Where a local calculation is extracted from an argument originally used for maximizers, we display the calculation before introducing stationarity. We do not silently apply a theorem whose maximality hypothesis is missing.

### G4. The geometric quadratic bound and its supporting derivative

For a right-angle cap K in Baek's injective domain \(\mathcal K^i\), there is a canonical triple X_K=(K,B_K,D_K) in a convex domain \(\mathcal L\) and a functional Q such that

\[
A_L(K)\le Q(X_K),\qquad Q(X_G)=M,
\]

\[
Q(X)=\Lambda(X)-\tfrac12\sum_{j=1}^{6}\|z_j(X)\|_{L^2}^2,
\qquad DQ_{X_G}(X-X_G)\le0.                                \tag{3.1}
\]

Here Lambda and z_j are affine, and the first four z_j are the cap tangent-displacement functions. The domain, integrability, area comparison, affine representation and first-variation inequality are the retained results of [B, Chapters 7-8]. They are the most substantial remaining part of the proof. Their conclusions do not require the final moving-sofa optimality theorem.

The parameter phi governing the four cap intervals satisfies 0<phi<=1/25 for the concrete G. The domain \(\mathcal K^i\) also includes the cap area lower bound a_0.

### G5. The concrete Gerver witness and its envelope

G is a feasible moving sofa of area M>=a_0. Its contact curves have the envelope properties stated in Section 4.2 of the companion angle/recovery section. Those properties imply G=closure(interior G) by the elementary envelope criterion proved there. Gerver's construction and Romik's phase description supply the concrete reference; the needed enclosures and contact facts are identified separately from any global optimality assertion.

The analytic nature of this manuscript is not a claim that the numerical enclosures disappear. Every inherited enclosure must have a proof in a final self-contained formal submission. Neither decimal approximations nor a declaration's existence in an uncompiled file count as such a proof.

## 4. New stationarity consequences and the scalar replacement

The companion selection section proves the following two statements from G3 and specified positive-value cap maximality.

**S1.** For omega<L, every specified positive maximizer K of A_omega satisfies

\[
w_K^\circ\le\sigma_K(\{L\}),\qquad z_K^\circ\le\sigma_K(\{\omega\}).
\]

**S2.** Every specified positive maximizer K of A_L has the endpoint-inclusive curvature bounds

\[
\sigma_K|_{[0,L)}\le k(g_K^+(t))dt,
\qquad\sigma_K|_{(L,\pi]}\le k(f_K^-(t-L))dt,
\]

where k(x)=max(|x-1|,(|x-1|+1)/2). In particular the two outer endpoint atoms vanish. The top atom at L is allowed.

Persistent support samples select approximations converging to K itself. Moving a floating facet changes only its own sampled height, so its defect is bounded by 2 eta_n w_n(t), where eta_n->0 and the weights have total mass at most one. At pins a uniform support perturbation estimate and the signed endpoint identity give vanishing two-sided defects. The error sum, rather than a uniform error per facet, is what passes to the limit. This avoids an inverse-mesh loss.

For a right-angle cap, h''+h=sigma and the one-sided endpoint geometry turn S2 into nonnegative absolutely continuous arms f,g satisfying

\[
f(t)\ge1+\int_0^t m(g(s))ds,\qquad
 g(t)\ge1+\int_t^L m(f(s))ds,\quad m(x)=x-k(x).
\]

Theorem 1.1 of the arm section gives

\[
f(t)\ge1+t/2,\qquad g(t)\ge1+(L-t)/2.                       \tag{4.1}
\]

Together with the derivative formula

\[
x_K'(t)=(1-f(t))u_t+(g(t)-1)v_t,
\]

these establish the required injectivity condition. This is a direct maximum-deficit argument, not a fixed-point iteration or a numerical replay. The robust version of the theorem also allows uniform additive errors in the integral inequalities.

For a feasible monotone sofa, S1 and the two-threshold geometric argument of the angle section provide a right-angle motion of a rotated copy of that same sofa. S1 by itself is not declared to imply feasibility.

## 5. Optimality first: a noncircular proof

**Theorem 5.1 (optimality relative to G1-G5).** Every moving sofa S satisfies |S|<=M.

**Proof.** If |S|<a_0, use a_0<=M. Otherwise apply G1: a translate of S lies in its own monotone enlargement T_0 at an angle omega in [arcsec(a_0),L]. If K_0 is the own cap of T_0, then

\[
|S|\le|T_0|=A_\omega(K_0).
\]

Choose the feasible fixed-angle maximizer C_omega supplied by G2, with sofa T_omega. Therefore

\[
A_\omega(K_0)\le A_\omega(C_\omega)=|T_\omega|.
\]

This positive maximum qualifies for S1. When omega<L, the same-sofa angle lemma gives a rotated copy of T_omega with a right-angle motion; when omega=L no extra rotation is needed. Normalize and monotonize that moving sofa at a right angle. Its own cap has A_L value at least |T_omega|.

Now choose the feasible maximizer C_L supplied by G2. Its A_L value is at least |T_omega|, hence at least a_0. Since |C_L|>=A_L(C_L), S2 and the scalar bootstrap put C_L in \(\mathcal K^i\). The exact deficit identity from (3.1) gives

\[
A_L(C_L)\le Q(X_{C_L})\le Q(X_G)=M.
\]

Chaining these inequalities proves |S|<=M. \(\square\)

Notice that numerical domination is sufficient throughout this argument. C_omega and C_L may be different maximizers. No conclusion about the shape of the original S is inferred from that domination.

**Corollary 5.2 (all cap values are bounded).** For every normalized omega-cap K,

\[
A_\omega(K)\le M.
\]

**Proof.** By G2, A_omega(K)<=A_omega(C_omega)=|T_omega|. Apply Theorem 5.1 to the feasible sofa T_omega. \(\square\)

This corollary becomes available only here. Calling the existing library helper `cap_area_le_gerver` earlier would import the old final optimality theorem and make a purported new proof circular.

## 6. Equality second: retain the starting set

**Theorem 6.1 (exact shape uniqueness in the proposed framework).** Under G1-G5 and the stationarity consequences established above, if S is a moving sofa with |S|=M, then U(S)=G for a Euclidean isometry U.

**Proof.** Normalize S at the angle from G1, obtaining S_0, and take its OWN monotonization T_0. Theorem 5.1 makes the actual inclusion

\[
S_0\subseteq T_0
\]

an equal-area inclusion. The own cap K_0 of T_0 has A_omega(K_0)=M. Corollary 5.2 now says K_0 is an unrestricted cap maximizer.

Apply S1 and the same-sofa angle lemma to K_0, not to a substitute feasible maximum. A rotation V of T_0 has a right-angle motion. Apply a translation W to normalize it and take its own right-angle monotonization T_1. The inclusions are

\[
W(V(S_0))\subseteq W(V(T_0))\subseteq T_1,                 \tag{6.1}
\]

and all three areas are M by Theorem 5.1. The own cap K_1 of T_1 has A_L(K_1)=M and is a cap maximizer by Corollary 5.2. S2 and (4.1) place K_1 in \(\mathcal K^i\).

The deficit identity has three nonnegative parts:

\[
M-A_L(K_1)=Q(X_{K_1})-A_L(K_1)-DQ_{X_G}(X_{K_1}-X_G)
+	frac12\sum_{j=1}^6\|z_j(X_{K_1})-z_j(X_G)\|^2.
\]

Its left side is zero. Each of the four cap displacement energies vanishes, and the cap-kernel proposition gives K_1=C(G)+(a,0). Horizontal translation commutes with the right-angle niche construction, so

\[
T_1=G+(a,0).
\]

Composing the actual isometries in (6.1) and removing this translation gives U(S) contained in G with equal finite area. U(S) is closed and G is regular closed by G5 and the envelope criterion. The set-recovery lemma therefore gives U(S)=G. \(\square\)

The converse in (1.1) follows from invariance of planar measure under isometries. Thus this conclusion concerns exactly the original set, not just its cap, monotonization, area, or equivalence modulo null sets.

## 7. A quantitative consequence, with a restricted domain

For K already in \(\mathcal K^i\), the cap-coercivity theorem and the exact deficit yield

\[
\inf_a d_H(K,C(G)+(a,0))^2\le6\,[M-A_L(K)].                 \tag{7.1}
\]

This is a quantitative consequence of the same four-equation kernel used in Theorem 6.1. It controls a cap, not an arbitrary moving sofa before the reductions. The argument supplies neither a modulus for the enlargement S to T_0 nor a general Hausdorff-continuity statement for K minus N(K). A global sofa-stability theorem is therefore not asserted.

## 8. Relation to the exact formal-conjectures statement

The identity-start formulation uses EuclideanSpace R (Fin 2), planar volume, and E(2), with the same horizontal and vertical sides. A continuous E(2) path starting at the identity stays orientation-preserving. A paper motion with an initial translation gives an identity-start motion of its initial placement; conversely the canonical motion has a continuous real angle lift. The coordinate identification preserves topology and volume, although the ordinary product norm on R times R is not the Euclidean norm.

These relationships are implemented by the repository's ordinary `Bridge` modules. The core shape theorem is meant to be shared, not reproved under two unrelated definitions. To specialize it to the exact `gerversSofa` name, its concrete integral/path formula must be identified with G. The uncompiled reference-correspondence work at commit 36dec2e supplies a proposed algebraic/calculus bridge independently of shape uniqueness. This manuscript does not treat that source as machine verification, and its parameter proof remains a separate review target.

The intended formal endpoint remains

```lean
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa
```

No extra regularity, symmetry, injectivity, balancedness, or maximality hypothesis is added to the input sofa. Regular-closedness is established for the target G, not assumed for s.

## 9. What has and has not been simplified

| Part of the argument | Treatment here |
| --- | --- |
| Coupled arm bootstrap | Replaced by one maximum-deficit estimate; uniform errors allowed |
| Selecting a specified maximizer | Fixed persistent sampled penalty; no tuned vanishing weight or uniform objective convergence |
| Floating variations | One changed sample, with a summable total error |
| Terminal quadratic argument | One exact deficit identity handles the bound and equality |
| Cap equality | Four first-order equations; an explicit coercivity estimate checks endpoints |
| Global proof order | Upper bound first, own-cap maximality second, exact starting-set recovery last |
| Feasible fixed-angle maximum | Retained from Baek's Chapter 3; not eliminated |
| Cap/niche geometry and local inner-ray analysis | Retained and used explicitly |
| Q domain, area comparison, first-variation sign | Retained from Baek's Chapters 7-8 |
| Full numerical/reference/formal verification | Not performed by this manuscript PR |

A short outline is not a short proof. The comparison above is a change in organization and in particular analytic subarguments, not a measured reduction of the total formalization size. The finite geometry and feasibility theory remain substantial.

## 10. Constants and proof methods

The constants are accounted for rather than treated as unexplained numerical oracles. L=pi/2 comes from the hallway. The threshold a_0=11/5 is a convenient lower benchmark for the geometric reductions. The two angular thresholds 5/4 and 11/10 have explicit polynomial certificates and are not properties of the optimizer. The sufficient scalar range L<5/3 comes from a triangular-envelope integral; a counterexample at L=5pi/9 shows that the length hypothesis cannot simply be omitted, without claiming 5/3 is sharp. The cutoff phi<=1/25 makes the cap-coercivity constant less than three; the final six is twice that bound.

No Lean compiler, Lake build, CI runner, numerical root search, decision-kernel replay, or external proof-source generator is used in this paper PR. The original analytic statements and rational inequalities are displayed. This does not certify the transitive dependencies of the existing Lean project. A compliant final formal submission still requires checking the exact theorem and definitions, an elaborated axiom audit, the requested proof-method restrictions, and toolchain compatibility. Those tasks remain distinct from writing a mathematical manuscript.

## References

**[B]** Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826v1 (2024). Versioned source: https://arxiv.org/html/2411.19826v1. The regenerated HTML display date is not used as a separate version claim.

**[G]** Joseph L. Gerver, *On Moving a Sofa around a Corner*, Geometriae Dedicata 42 (1992), 267-283. DOI: 10.1007/BF02414066.

**[R]** Dan Romik, *Differential Equations and Exact Solutions in the Moving Sofa Problem*, Experimental Mathematics 27 (2018), 316-330. arXiv:1606.08111. DOI: 10.1080/10586458.2016.1270858.

**[KR]** Yoav Kallus and Dan Romik, *Improved Upper Bounds in the Moving Sofa Problem*, Advances in Mathematics 340 (2018), 960-982. arXiv:1706.06630. DOI: 10.1016/j.aim.2018.10.022. This is background on a different, computer-assisted approach; its bound is not a numerical input to the proof written here.

**[U]** Repository research, `vltanh/lean4-moving-sofa`, uniqueness/equality-cases at commit 36dec2efe72f3a75ea1fb6bd99578dc956530b14. Notes 11, 17, 19, 20 and 22 and the corresponding uncompiled source informed this manuscript. They are research material, not independent verification.
