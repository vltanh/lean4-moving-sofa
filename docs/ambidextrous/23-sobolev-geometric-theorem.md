# 23. The geometric theorem does not require finitely many analytic pieces

The final restricted theorem can be stated directly in support-curvature language, without prespecifying a finite contact decomposition or piecewise smooth boundary. This is useful because a general maximizing-body argument would naturally produce measure or Sobolev bounds rather than an explicit list of arcs.

The strict curvature bound and the linear contact inequality remain hypotheses. No approximation argument is used to assume that Minkowski combinations of feasible sofas remain feasible.

## 23.1 Regularity available from the stated bounds

Let K be a compact convex body normalized to vertical span one. Suppose its support function h belongs to the domain D of (22.4). In particular each quarter restriction f,g is H^2 and

\[
0\leq\rho_f=f''+f<1,\qquad
0\leq\rho_g=g''+g<1
\quad\text{a.e.}
\]

Since f and g are bounded continuous functions on the compact interval, these inequalities imply that f'' and g'' are essentially bounded. Thus f,g are W^{2,infinity}, their first derivatives are Lipschitz, and the corner and contact curves of (17.2) are Lipschitz. The velocities p,q are Lipschitz as well.

Every derivative identity used in Notes 17 and 20 therefore holds almost everywhere and can be integrated. No singular curvature measure is present in the open quarters under this hypothesis. At the vertical normals the two permitted derivative jumps encode the horizontal exposed faces.

## 23.2 The profile proof with almost-everywhere derivatives

The coordinates B_x,D_x are strictly increasing because their almost-everywhere derivatives are

\[
(1-\rho_f)\sin t>0,\qquad (1-\rho_g)\cos t>0
\quad\text{a.e. on }(0,L).
\]

Their side heights have the analogous strict monotonicities. Lemma 49 provides the unique ordered zeros a,b. The roof expressions R_t(x),L_t(x) are continuously differentiable on the open interval because f,g are C^1, and their derivatives are still (17.7). Thus the maximizing-parameter proof of the three-piece graph is unchanged.

On the middle interval, c_y has an absolutely continuous derivative and satisfies c_y''<=0 almost everywhere, so it is concave there. This supplies the same positive-height conclusion. These facts prove Theorem 41 in the present Sobolev setting.

The profile-area identity also survives without a smoothness assumption. The boundary arcs are absolutely continuous and have monotone horizontal coordinates. Fubini and change of variables along such an arc give its contribution to the area as the integral of height times horizontal displacement. Integration by parts for absolutely continuous coordinates identifies the sum with one half of the closed determinant integral. Applying the absolutely continuous versions of (13.4)–(13.5) therefore proves (17.8) directly. No differentiability of the inverse graph parametrizations is needed.

Extreme-point retention and the interval argument in Note 20 are topological and convex-geometric; their only analytic input is the now-established positive profile and the integrated curvature inequality. Hence forced alignment and absence of clipping hold as before.

## 23.3 The final proved geometric statement

**Theorem 52 (sharp area and uniqueness under support-curvature/contact conditions).** Let S be a compact connected body admitting both ambidextrous motions. Suppose, after a proper rigid normalization, K=conv(S) has vertical span one, and:

- S follows both canonical full conventional quarter turns determined by h_K;
- h_K belongs to the explicit convex function domain D of (22.4).

Then

\[
\boxed{|S|\leq1+4Y^2+\arctan Y,\qquad 4Y^3+3Y-1=0,\quad Y>0.}
\]

Equality holds exactly when S is congruent to Romik's candidate.

**Proof.** The preceding paragraphs establish the exact niche profiles under these hypotheses. Theorem 46 then forces the top and bottom exposed faces to align. Connected common-hull saturation, absence of overlap, and absence of clipping give

\[
|S|\leq|E_K|=\widetilde{\mathcal Q}(h_K)\leq M.
\]

The last inequality is Theorem 50 on D. Its equality kernel determines h_K up to a horizontal translation of h_*. The canonical envelope is then the corresponding translate of Sigma_*, which is regular closed by Section 18.4. Lemma 4 recovers exact equality of S with that envelope. Candidate attainment and its identification were established in Section 18.3. QED.

This theorem does not assume symmetric competitors, fixed contact switches, face alignment, ordinary monotonicity of p and q, or a finite number of analytic boundary pieces. It does assume a full-angle motion and, on both reflected halves,

\[
0\leq h''+h<1\quad\text{a.e. on the open quarters},
\qquad f'-g+1\leq g'+f-1,
\]

together with the H^2 quarter regularity encoded by D. These are not yet derived for arbitrary optimizers.

## 23.4 A closure argument that must not be silently inserted

For the algebraic functional alone, weak non-strict curvature bounds can often be approximated by taking a convex combination with h_*, since its curvature is strictly below one. That observation does not by itself extend Theorem 52 to every degenerate feasible body: feasibility of the corresponding common-hull envelopes under Minkowski interpolation has not been proved, and the positive profile/strict interval-overlap arguments can degenerate.

The theorem therefore retains its stated strict almost-everywhere curvature hypotheses. A limiting extension would need to verify geometric area convergence, component behavior, and exact-set recovery rather than citing algebraic continuity alone. This is recorded as an unproved extension, not as an additional obstruction to the already proved statement.
