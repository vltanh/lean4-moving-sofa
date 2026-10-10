# 22. Ordinary velocity monotonicity is unnecessary

The completed geometric theorem can be enlarged again. The strict monotonicity assumptions on p and q in Note 16 can be replaced by curvature bounds and the single linear inequality p<=q. Those conditions imply weighted monotonicity, the endpoint signs, and the unique ordered contact switches needed by the proof.

This improves the precise remaining reduction target; it does not establish the new hypotheses for every unrestricted maximizer.

## 22.1 The differential identities

Keep f(L)=g(0)=1 and

\[
p=f'-g+1,\qquad q=g'+f-1,
\qquad \rho_f=f''+f,\quad\rho_g=g''+g.
\]

Direct differentiation gives

\[
p'=\rho_f-1-q,\qquad q'=\rho_g-1+p.
\tag{22.1}
\]

Suppose 0<=rho_f,rho_g<1 almost everywhere and p<=q. Then

\[
p'+p=\rho_f-1+p-q<0,
\qquad q'-q=\rho_g-1+p-q<0
\tag{22.2}
\]

almost everywhere. In particular e^t p(t) and e^(-t)q(t) are strictly decreasing. The strictness follows by integration on any nonempty interval, since 1-rho is positive almost everywhere; no uniform negative derivative bound is assumed.

## 22.2 The endpoint signs follow from the strip normalization

Variation of constants, or integration of the outer contact coordinates, gives

\[
f'(0)=1-\int_0^L\rho_f(t)\cos t\,dt>0,
\]

\[
g'(L)=-1+\int_0^L\rho_g(t)\sin t\,dt<0.
\tag{22.3}
\]

Since g(0)=f(L)=1, these are p(0)>0 and q(L)<0. The inequality p<=q then supplies q(0)>0 and p(L)<0.

**Lemma 49 (automatic single crossings).** Under these assumptions, p and q have unique zeros a,b in (0,L), with a<=b. Their signs are positive before their respective zeros and negative afterwards. Moreover p'<0 and q'<0 almost everywhere on the middle interval (a,b).

**Proof.** The weighted strict monotonicity in (22.2), the endpoint signs, and continuity give the unique zeros and their sign changes. Since p<=q, the zero of p cannot occur after the zero of q. On (a,b), p<0<q, so (22.1) gives both ordinary derivative inequalities there. QED.

The functions need not be ordinarily decreasing on the early and late intervals. No later step requires that stronger statement.

## 22.3 The enlarged convex function domain

Let D consist of normalized periodic H^1 functions h with h(L)=1 and h(-L)=0, whose quarter restrictions f,g for both h and h^rho are H^2 and satisfy

\[
0\leq f''+f<1,\qquad0\leq g''+g<1
\quad\text{a.e.},\qquad
f'-g+1\leq g'+f-1.
\tag{22.4}
\]

All conditions are affine equations or linear inequalities, so D is convex. The candidate h_* belongs to D by (18.1) and the positive gap verified in (16.4).

**Theorem 50 (sharp adaptive maximum on D).** The adaptive functional of (16.2) satisfies

\[
\widetilde{\mathcal Q}(h)\leq M\qquad(h\in D),
\]

with equality exactly when h=h_*+a cos(theta).

**Proof.** Along any segment in D, Lemma 49 gives one zero for each velocity, with the ordered active intervals required by Theorem 34. The second-derivative calculation in Theorem 39 uses only that zero structure, not ordinary monotonicity away from the zeros. Dominated convergence is still applicable because H^2 quarter functions have bounded first derivatives and the zero sets have measure zero. Thus the same nonnegative integrated gap (16.5) holds, with the current roots furnished by Lemma 49. Candidate stationarity and value were proved in Note 14, and the kernel is unchanged. QED.

This is a global theorem on the displayed convex domain, including nonsymmetric functions. It is not asserted for arbitrary H^1 functions or for arbitrary convex hulls outside D.

## 22.4 The geometric profile and alignment proofs still work

For a piecewise C^2 support function in D, the B_x and D_x monotonicities in Theorem 41 follow only from rho_f,rho_g<1. Their side heights are positive for the same reason. The proof of the middle graph uses the signs of p,q and the inequalities p',q'<0 on (a,b), which Lemma 49 supplies. Every other step uses the unique ordered zeros, not ordinary monotonicity on the side phases.

The forced-alignment proof in Note 20 uses the same profile positivity, the curvature bound, and q(0)>0. All remain available by (22.3). Therefore no independent alignment or endpoint-sign assumptions need be retained.

**Corollary 51 (the enlarged geometric theorem).** Let S be a compact connected ambidextrous body. Suppose, after proper rigid normalization, K=conv(S) has vertical span one, S admits both canonical full conventional quarter turns, and h_K belongs to D with C^1, piecewise C^2 quarter restrictions having finitely many pieces. Then

\[
|S|\leq M,
\]

with equality exactly for bodies congruent to Romik's candidate.

**Proof.** The preceding paragraph supplies the exact profile formula and forced face alignment. Thus the canonical saturation has area tilde Q(h_K). Apply Theorem 50, then the same regular-closed exact recovery as in Theorem 44. Candidate membership, feasibility, and regular closedness were verified in Note 18. QED.

## 22.5 The remaining reduction is now more precise

For the unrestricted problem, correct turning signs, unit span, common-hull canonicalization, and niche separation are already proved for every competitive body. To apply Corollary 51 it remains to justify full quarter-turn endpoints and an appropriate regularity/curvature/contact reduction yielding (22.4), or to replace those requirements by a more general geometric certificate.

The inequality p<=q is still a real condition. For the feasible radius-1/2 disk, p=1/2 and q=-1/2, so it fails; it is not a universal consequence of convexity or full-turn feasibility. That low-area example does not rule out deriving it for relevant maximizers. The visible-side issue of Note 21 explains why a direct import of the single-turn balance proof has not yet supplied such a derivation.
