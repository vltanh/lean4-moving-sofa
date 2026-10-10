# 31. Optimality and uniqueness on the closed curvature/contact class

This strengthens Theorem 52: curvature may equal one on positive-measure sets, contact zeros may be degenerate, and separate H^2 regularity need not be assumed if curvature is stated as a measure inequality. The proof uses Note 30's direct geometry, not an unproved feasibility-preserving interpolation.

**Width-gate update.** Corollary WG4 below also removes the independent full-quarter-turn premise: the [width-gate supplement](64-width-gate-from-curvature-and-contact.md) derives it from the curvature and contact conditions for every competitive body. WG labels are used to avoid collisions with the concurrently extended numbered notes. The unrestricted problem still requires a proof of those two support conditions for relevant maximizers. They are not asserted for all feasible bodies.

## 31.1 The algebraic inequality extends to weak bounds

Let D_bar be the normalized function domain from (30.1), for both h and h^rho, with 0<=rho_f,rho_g<=1 rather than strict upper bounds. Its contact condition remains p<=q. It is convex.

**Theorem 64 (closed-domain adaptive maximum).** For every h in D_bar,

\[
\widetilde{\mathcal Q}(h)\leq M,
\]

with equality exactly when h=h_*+a cos(theta).

**Proof.** Put h_lambda=(1-lambda)h_*+lambda h. For lambda<1 its curvature is strictly less than one almost everywhere, since the candidate has that strict bound. Its contact gap q-p is strictly positive because the candidate gap is uniformly positive and the other gap is nonnegative. Thus h_lambda belongs to the strict domain D of Theorem 50. That theorem gives Q_tilde(h_lambda)<=M.

The functional is continuous in the quarter H^1 norms: its area and signed-corner terms are continuous quadratic forms, and the maps p to min(p,0) and q to max(q,0) are Lipschitz in L^2. Therefore lambda increasing to one gives the weak-domain bound.

For equality, suppose delta=h-h_* is not a common horizontal-translation mode. Along lambda<1 the second derivative is the negative sum of the two strictly positive Hessian forms from Theorem 34. In particular it is strictly negative at zero and the first derivative at zero is zero, so Q_tilde(h_lambda)<M for some positive lambda_0. Concavity on this segment and the zero initial derivative imply that the function is nonincreasing thereafter. Its endpoint limit is therefore at most Q_tilde(h_lambda_0)<M. A translation gives equality by substitution. QED.

Only the **function-space** segment is used here. The intermediate functions are not asserted to represent feasible sofas.

## 31.2 Curvature domination supplies the needed regularity

For a planar convex body K, denote its support function by h_K and its surface-area/curvature measure by

\[
\sigma_K=h_K+h_K''
\]

in the distributional sense. Suppose

\[
\sigma_K|_J\leq d\theta|_J
\tag{31.1}
\]

on each open coordinate quarter J. Convexity gives nonnegativity, so this measure is absolutely continuous on J with density rho in [0,1]. The support function is bounded and Lipschitz, and hence
\(h_K''=\rho-h_K\) is essentially bounded on J. It follows that h_K belongs to W^{2,infinity} on each quarter, with one-sided derivative traces at its endpoints. In particular the H^2 hypotheses used in Note 30 follow from (31.1).

Atoms at the four coordinate-axis normals are not excluded by (31.1). They correspond to exposed faces and are allowed at this stage. The equality theorem will identify the specific face structure of the candidate.

For 0<=t<=pi/2 define the quarter traces f(t)=h_K(t), g(t)=h_K(t+pi/2), and require

\[
f'(t)-g(t)+1\leq g'(t)+f(t)-1.
\tag{31.2}
\]

Impose the same condition for the support function of rho K. With the regularity just proved, an almost-everywhere version extends to every t by continuity of the one-sided quarter expressions.

## 31.3 The geometric theorem with full motions supplied

**Theorem 65 (weak-curvature geometric optimality and exact uniqueness).** Let S be compact and connected, K=conv(S), in a proper rigid normalization of vertical span one. Assume:

1. S follows both support-determined full conventional quarter-turn motions;
2. the curvature-measure domination (31.1) holds on all four open quarters;
3. the two contact inequalities (31.2) hold.

Then

\[
\boxed{|S|\leq M=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0.}
\]

Equality holds exactly for bodies congruent to Romik's candidate.

**Proof.** The curvature domination supplies the quarter regularity and weak bounds needed in Note 30. Connected common-hull saturation gives a compact connected feasible envelope E_K containing S. Lemmas 62–63 compute its niche profiles and eliminate positive clipping loss, even in the degenerate cases. The vertical-barrier lemma gives separation. Therefore

\[
|S|\leq|E_K|=\widetilde{\mathcal Q}(h_K)\leq M,
\]

where the last inequality is Theorem 64.

At equality the hull support is h_*+a cos(theta), hence K is the corresponding horizontal translate of K_*. Its canonical envelope is the same translate of Sigma_*. This envelope is regular closed by Section 18.4. The original S is a closed subset of it with equal area, so Lemma 4 gives equality of the sets. Undo the initial coordinate change. Candidate attainment was verified in Note 18. QED.

This theorem assumes neither strict curvature, symmetry, aligned faces, fixed contact switches, ordinary velocity monotonicity, nor a finite analytic arc decomposition. The direct no-clipping proof is what makes the weak-bound extension geometric rather than merely algebraic.

## 31.4 Removing the independent full-turn assumption

**Corollary WG4 (sharp comparison from two support conditions).** Let S be a compact connected ambidextrous body with arbitrary motions in the posed problem of Note 1. Suppose there is a common unit-span normalization in which K=conv(S) satisfies (31.1) and both inequalities (31.2). Then

\[
|S|\leq M,
\]

with equality exactly for bodies congruent to Romik's candidate. Full-quarter endpoint angles are not an additional hypothesis.

**Proof.** If |S|<=sqrt(2), the inequality is strict because M>8/5>sqrt(2), as proved in Note 10. Otherwise Corollary WG3 in the width-gate supplement supplies both full conventional canonical turns for the same body and hull. Its proof uses equality of widths under central Minkowski symmetrization and the bound

\[
w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|,
\]

which is greater than one for pi/4<=|t|<pi/2. The correct-sign canonical endpoints already exceed pi/4 by the two-strip area bound, so their outgoing unit strips force them to equal pi/2. Apply Theorem 65 and its exact equality recovery. The explicit candidate satisfies the two support conditions and attains M. QED.

The two support conditions must hold in **one and the same normalization**. Curvature domination obtained in one orientation and contact order obtained in another do not meet this corollary's hypothesis.

No feasibility-preserving symmetrization is assumed. The auxiliary centrally symmetric body is used only because its widths equal those of K. This result was initially numbered Corollary 123; the WG4 label supersedes that temporary number to avoid a collision with concurrent work.

## 31.5 The remaining sufficient route to unrestricted closure

Global attainment is proved in Theorem 55. With Corollary WG4, the sufficient maximizer statement becomes:

> Some global maximizer has a common unit-span normalized hull satisfying the curvature domination (31.1) and both contact inequalities (31.2).

This would prove the optimal value. To prove exact uniqueness by the same route, establish those conditions for **every** global maximizer, or supply an equality-preserving comparison that recovers each original body.

Full-quarter endpoint angles no longer need an independent proof once these two support conditions are established. The earlier unit-square gate is an alternative sufficient criterion, not a remaining premise of this route.

The conditions themselves have not been proved for unrestricted maximizers. High-area counterexamples in the earlier notes prevent substituting a feasibility threshold for a genuine maximality or improvement argument. Neither the weak-curvature extension nor the width gate eliminates the residual contact multipliers or proves the sharp density bound. Domination only at floating normals is not domination on every open quarter when partial terminal directions are still pinned.
