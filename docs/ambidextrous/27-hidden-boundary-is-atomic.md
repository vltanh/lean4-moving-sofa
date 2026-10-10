# 27. Hidden outer-boundary loss is purely atomic in normal direction

The finite-angle counterexample in Note 21 remains valid. It does not, however, show that an opposite niche can hide a positive amount of the diffuse curvature measure of an actual common hull. This note proves that all strictly hidden outer boundary is on straight exposed edges. It separates that obstruction from the still-unresolved contact and variation-admissibility issues.

## 27.1 Extreme-point retention localizes the hidden set

Let S be compact, let K=conv(S) have nonempty interior, and let W be an open set disjoint from S. For applications W is the union of the two open forbidden sweeps. Define

\[
H=\partial K\cap W.
\tag{27.1}
\]

**Lemma 58 (hidden boundary consists of edge interiors).** Every point of H belongs to the relative interior of a nontrivial exposed edge of K. There are at most countably many such edges, and their total length is at most the perimeter of K.

**Proof.** Lemma 45 says every extreme point of K belongs to S and hence is outside W. Thus p in H is not extreme. There are distinct a,b in K such that p is strictly between them. Any supporting line at the boundary point p contains a and b, because its affine defining inequality is an equality at their strict convex combination. The exposed face on that line is therefore a nontrivial segment, and p lies in its relative interior.

The relative interiors of distinct maximal exposed edges are disjoint boundary arcs. Each has positive length. Since the boundary of a bounded planar convex body has finite length, there are only finitely many edges of length at least 1/n for each positive integer n, hence at most countably many in total. Disjointness bounds the sum of their lengths by the perimeter. QED.

This result only concerns points lying **inside** an open forbidden sweep. Points on its boundary can still be active constraints for a variation.

## 27.2 An exact measure identity

Let sigma_K be the surface-area measure of K: push boundary arclength forward by its outer unit normal, ignoring the arclength-null set where that normal is not unique. For an exposed edge e let n_e be its outer normal and let

\[
\lambda_e=\mathcal H^1(e\cap W).
\]

Define the retained-boundary measure sigma_ret by the same pushforward restricted to partial K minus W.

**Theorem 59 (atomic visibility defect).**

\[
\boxed{\sigma_K-\sigma_{\rm ret}
=\sum_e\lambda_e\,\delta_{n_e}.}
\tag{27.2}
\]

In particular the absolutely continuous and singular-continuous parts of sigma_K and sigma_ret are identical. Only their atomic parts can differ.

**Proof.** By Lemma 58 every removed boundary point lies in a relative edge interior. Its normal is constant there. The pushforward of the removed length on that edge is therefore lambda_e times the Dirac mass at its normal. The countable sum converges because its total mass is bounded by the perimeter. This accounts for the whole removed set, proving (27.2). Uniqueness of the measure decomposition gives the final assertion. QED.

For a planar support function, sigma_K is the curvature measure h_K+h_K'' in the distributional sense. Equation (27.2) therefore identifies precisely which part of a curvature-measure estimate could be lost by replacing full outer-edge length with retained length.

## 27.3 What a retained-side estimate would and would not prove

Suppose a future justified variational argument gives, on a floating angular interval J,

\[
\sigma_{\rm ret}|_J\leq c(t)\,dt
\tag{27.3}
\]

for an integrable nonnegative c. Then (27.2) implies:

- the diffuse part of sigma_K on J is absolutely continuous and has density at most c;
- any remaining singular part of sigma_K on J consists of hidden edge atoms.

If an edge of normal in J has any retained positive length, (27.3) also forces that retained length to be zero, a contradiction. Thus the only edge atoms not excluded by such an estimate would be edges whose interiors are hidden up to arclength zero, even though their endpoints remain in S.

This is a conditional consequence of (27.3), not a proof of that estimate. It gives a sharper target than the claim that all outer edges must first be fully visible.

## 27.4 Contact is not the same as strict hiding

The retained measure counts points on the boundary of W, because W is open. That is correct for the set identity, but it does not mean that moving those boundary points outward creates area at the full rate. A common boundary arc may be blocked immediately by the opposite motion, producing the one-sided terms discussed in Note 5.

Consequently (27.2) alone does not turn the finite formula sigma_visible minus tau_visible into a general first-variation theorem. A continuum proof must still address coincident contacts, admissibility under connectedness and endpoint constraints, and passage from polygons or smooth variations to measures.

## 27.5 Updated interpretation of the counterexample

Note 21's hidden sloping edge is exactly an atom in (27.2). Its example is not retracted. What is ruled out here is a stronger interpretation of that example: strict removal by the opposite sweep cannot hide a curved extreme boundary arc of a genuine common hull.

The remaining regularity program now has two distinct tasks: obtain a justified bound for the retained diffuse measure, and handle hidden edge atoms and active contact arcs separately. This distinction is useful even if the eventual proof uses a different global certificate.
