# 6. The exact conditional theorem still to be completed

The implications in this note are proved. Their problem-specific sharp-bound and rigidity hypotheses are not. This distinction is essential: writing a certificate template is not constructing a certificate for the ambidextrous sofa problem.

Let Sigma be Romik's candidate and let M denote its area, with the expression from Note 4. Candidate feasibility and area are the explicitly cited external inputs there.

## 6.1 Coverage must precede optimization

Let D be a class of normalized two-motion witness data z. Each z determines K,U,V,E as in Notes 1–2, and the fixed separator is h=1/2.

The coverage condition needed for both optimality **and** direct uniqueness recovery is:

> For every admissible body S there are z in D and an area-preserving rigid map T such that T(S) is a subset of E(z).

For the full witness class, common-pose normalization (Proposition 14) and Proposition 1 give this property, with T a translation and a box containing T(S). If D is restricted to monotone paths, canonical caps, injective sweeps, or a selected contact pattern, the corresponding coverage/containment theorem remains to be proved.

A replacement that only increases area may suffice for an optimality proof, but does **not** by itself transfer equality back to the original body. This is why containment, rather than only area domination, is stated above.

## 6.2 Five nonnegative defects

Suppose real functions a(z), b(z) satisfy

\[
a(z)\leq|U\cap\{y\leq1/2\}|,
\qquad b(z)\leq|V\cap\{y>1/2\}|,
\qquad Q(z)=|K|-a(z)-b(z).
\tag{6.1}
\]

The missing sharp estimate is

\[
Q(z)\leq M\quad\text{for every }z\in D.
\tag{6.2}
\]

For S represented by z, write S' = T(S). Corollary 10 then yields the exact identity

\[
M-|S|=D_{\rm opt}+D_-+D_++D_{\rm mask}+D_{\rm fill},
\tag{6.3}
\]

where

\[
D_{\rm opt}=M-Q(z),\quad
D_-=|U\cap\{y\leq1/2\}|-a(z),\quad
D_+=|V\cap\{y>1/2\}|-b(z),
\]

\[
D_{\rm mask}=|(U\setminus V)\cap\{y>1/2\}|
             +|(V\setminus U)\cap\{y\leq1/2\}|,
\qquad D_{\rm fill}=|E\setminus S'|.
\]

All five quantities would be nonnegative under (6.1)–(6.2). The candidate mask term is proved to vanish in Note 4; the other sharpness requirements have not been established here.

**Theorem 17 (conditional global optimality and exact uniqueness).** Assume the coverage condition, (6.1), and (6.2), and assume Sigma is feasible with area M. Then every feasible body has area at most M, so Sigma is optimal. Assume additionally:

- simultaneous vanishing of \(D_{\rm opt},D_-,D_+,D_{\rm mask}\) implies that E(z) is congruent to Sigma;
- Sigma is regular closed.

Then every compact connected maximizing body is congruent to Sigma.

**Proof.** Represent an arbitrary S by z. Equation (6.3), or the chain

\[
|S|\leq|E(z)|\leq P_{h=1/2}(z)\leq Q(z)\leq M,
\]

proves the upper bound. Feasibility of Sigma attains it; no independent existence theorem for a maximizing motion pair is needed. If |S|=M, all five nonnegative defects vanish. The rigidity hypothesis identifies E(z) up to congruence with Sigma, and hence E(z) is regular closed. Since S' is closed, is contained in E(z), and has the same area, Lemma 4 gives S'=E(z). Undo T. QED.

This theorem seeks uniqueness of the **body**, not uniqueness of its motion witnesses. Many different motions can in principle describe the same body.

## 6.3 What a quadratic certificate would have to prove

The following algebraic lemma describes a possible route to (6.2), not an existing ambidextrous Q.

**Lemma 18 (quadratic comparison).** Let D be a convex subset of a real vector space with a fixed affine origin. Suppose

\[
Q(z)=q_0+\ell(z)-B(z,z),
\]

where ell is linear and B is symmetric bilinear. Fix \(z_*\in D\). Assume for every \(z\in D\), with \(v=z-z_*\),

\[
B(v,v)\geq0,
\qquad \ell(v)-2B(z_*,v)\leq0.
\tag{6.4}
\]

Then

\[
Q(z_*)-Q(z)
=-\bigl(\ell(v)-2B(z_*,v)\bigr)+B(v,v)\geq0.
\tag{6.5}
\]

Equality holds exactly when both terms on the right vanish.

**Proof.** Expand \(B(z_*+v,z_*+v)\), use symmetry, and cancel the constant terms. This gives (6.5) identically. Each term is nonnegative by (6.4). QED.

The convex domain is the setting in which the candidate's first-order inequality may be derived along segments; the expansion itself is purely algebraic. If the zero directions of B and of the first-order loss reduce to geometric symmetries, (6.5) supplies the optimization part of rigidity. It does not supply equality in the clipped niche estimates or the geometric reconstruction.

For two motion variables, the quadratic form must control both symmetric and antisymmetric directions and their cross terms. Two one-turn concavity statements do not establish this. Likewise, a first-order equality at a stationary candidate is insufficient unless the global sign of B is proved on the relevant domain.

## 6.4 How the program could fail, and what that would mean

The partition upper bound might be too loose away from the candidate, even though it is exact near it. Finding normalized witness data with \(P_{h=1/2}>M\) would rule out a proof that bounds this particular P by M uniformly; it would not disprove optimality of Sigma.

Also, the full envelope E may be disconnected. Bounding its total area is a stronger relaxation than bounding the largest feasible component. A counterexample involving extra components may require a different majorant or a component-preserving reduction rather than a change to the conjectured optimal body.

Similarly, failure of a monotone-path reduction or of a single contact ansatz would invalidate that route, not constitute a proof of nonoptimality. These are concrete tests to perform before attempting a long equality-case calculation.

## 6.5 The next substantive target

Construct explicit clipped-niche lower bounds a and b in the normalized two-witness variables, exact at Romik's path, and examine whether their common-outer-set functional Q has a global comparison of the form (6.5). This requires a geometric argument for the clipped sweeps; no such inequality is claimed in these notes.

A first diagnostic is an admissible two-sided first-variation calculation at the candidate, including common outer-boundary arcs. A successful calculation would still need a global sign certificate and a coverage theorem for any reduced domain before Theorem 17 could be applied.
