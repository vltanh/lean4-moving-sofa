# 52. A uniform support estimate removes one obstruction in the finite variation program

This note returns to the finite penalized maximizers, rather than enlarging the local candidate class. It resolves the support-amplification question in (39.8) for an explicitly defined family of variations. The estimate does not depend on the smallest angle between polygon sides.

It does **not** prove that the varied two-turn envelope remains connected or retains its intended hull. Those are separate geometric obligations. The distinction matters: a uniform estimate for a convex outer polygon is not automatically an estimate for a component surviving inside it.

## 52.1 Competitive convex hulls have a uniform inner disk

**Lemma 95 (elementary inner-radius bound).** If a compact convex planar body K has area at least A_0>0 and diameter at most D, then it contains a disk of radius at least A_0/(6D).

**Proof.** Choose diameter endpoints a,b, at distance d=diam(K)<=D. Let H_+,H_- be the maximum distances of points of K from their line on its two sides. Projection of K onto that line lies between a and b: a point projecting beyond an endpoint would have distance greater than d from the other endpoint. Therefore K is contained in a rectangle of area d(H_++H_-), and

\[
A_0\leq|K|\leq d(H_++H_-).
\]

On at least one side there is a point c of height H>=A_0/(2d). The triangle abc lies in K, has area dH/2>=A_0/4, and perimeter at most 3d. Its inradius is twice its area divided by its perimeter, hence at least A_0/(6d)>=A_0/(6D). QED.

For the selected finite bodies C_n of Note 39, their hulls K_n have area at least |C_n|>=V>A_0=8/5, and lie in a fixed box. Thus this lemma supplies a positive uniform radius r_0. The centers o_n may vary; no common center is asserted.

## 52.2 Moving supporting lines does not amplify Hausdorff distance by the mesh size

Let K be a convex polygon containing B(o,r), with r>0, and let H be a finite set of unit normals whose supporting half-planes reconstruct K. Extra recorded normals may be added. Given real heights v(u), u in H, set C=max_H |v(u)| and

\[
K_s=\bigcap_{u\in H}\{x:x\cdot u\leq h_K(u)+s v(u)\}.
\]

Write R=max_{x in K}|x-o|. For |s|C<r, put delta=|s|C/r.

**Theorem 96 (uniform supporting-line sandwich).**

\[
o+(1-\delta)(K-o)\subseteq K_s
\subseteq o+(1+\delta)(K-o),
\tag{52.1}
\]

and consequently

\[
d_H(K_s,K)\leq \frac{RC}{r}|s|.
\tag{52.2}
\]

**Proof.** In coordinates centered at o, every old supporting height a(u)=h_K(u)-o dot u is at least r. The perturbed height lies between

\[
(1-\delta)a(u)\leq a(u)-|s|C
\leq a(u)+s v(u)
\leq a(u)+|s|C\leq(1+\delta)a(u).
\]

Intersect these half-planes. Because the original inequalities reconstruct K, their common multiples reconstruct the corresponding homothetic copies. This gives (52.1). Pair each point of K with its (1-delta)-scaled copy, and each point of K_s with its (1+delta)-descaled copy in K. Both distances are at most delta R. This proves (52.2). QED.

No angle denominator occurs. A tracked polygon vertex can move a long distance along an almost parallel neighboring edge; that is not the Hausdorff distance from the new polygon to the old one. The distinction avoids an artificial O(N) factor in a grid of N normals.

## 52.3 Consequence for the selected penalized maxima

At each selected hull K_n, augment the recorded normal set by **all** edge normals of K_n, so its half-planes reconstruct the hull. This augmentation is used to define a competitor and does not change the selection objective or the finite hallway samples.

Suppose T_{n,s} is a two-sided admissible family in the same finite class as C_n such that

\[
\operatorname{conv}(T_{n,s})=(K_n)_s,
\qquad \max_u|v_n(u)|\leq C
\tag{52.3}
\]

for a fixed C. It is enough for each n to have its own possibly shrinking interval of admissible s; the derivative is taken before n tends to infinity. Endpoint angles are held fixed. Assume the area is differentiable at zero and T_{n,0}=C_n.

**Corollary 97 (vanishing penalty error with no mesh amplification).**

\[
\left|\frac{d}{ds}|T_{n,s}|\bigg|_{s=0}\right|
\leq \kappa_n\frac{DC}{r_0}\longrightarrow0,
\tag{52.4}
\]

where D bounds the diameters of the selected hulls, r_0=A_0/(6D), and kappa_n=N^(-1/2).

**Proof.** The center o_n belongs to K_n, so R_n<=D. Theorem 96 bounds the difference of every support value of (K_n)_s by DC|s|/r_0. Apply the exact finite-optimizer inequality (39.7) and divide by positive s. Apply it also to the negative variation to obtain the other derivative inequality. QED.

This applies to a single floating support height as well as a coherent multi-height variation, provided (52.3) and finite-class admissibility really hold. A one-sided admissible variation gives the corresponding one-sided derivative bound.

## 52.4 What is and is not removed

The penalty schedule and small angular separations are not a further obstruction for **hull-preserving supporting-line variations**. The remaining work is geometric:

- prove that an intended surviving component stays connected and is admissible;
- prove it retains the varied polygon as its actual convex hull;
- retain incoming and outgoing strip constraints, including support attainment when a normalization demands exact span;
- compute the visible and coincident-contact area terms.

An arbitrary component of a perturbed envelope may lose an entire lobe at a pinching contact. Theorem 96 controls the outer convex polygon and does not rule that out. Nor does an intersection of perturbed half-planes automatically retain every prescribed support height as an equality. The theorem needs only reconstruction of the original polygon; any later support-attainment claim must be proved independently.

For the first variation itself, the threshold |S|>=8/5 is inactive at the selected maxima because |C_n|>=V>=M>8/5. The geometric endpoint/connectedness restrictions are not thereby inactive. Only V>=M is known; the strict inequality V>M is neither assumed nor established.

No CI, Lean, numerical experiment, or symbolic computation was used. These are elementary pen-and-paper estimates applied to the already stated selection framework, with no claim of unrestricted optimality.
