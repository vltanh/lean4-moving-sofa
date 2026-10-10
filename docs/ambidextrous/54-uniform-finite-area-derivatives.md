# 54. The raw finite-envelope area has a uniform interior-angle derivative bound

The finite variational route needs two different estimates: control of the selection penalty, and control of the area derivative itself. Note 52 supplies the first for hull-preserving competitors. This note supplies the second for **raw** finite envelopes, even when they are disconnected or a contact assignment changes.

The estimate is for the area of the full envelope. It does not make that full envelope a connected competitor when it is disconnected. It will not be used to remove the normal-cone terms in Theorem 99.

## 54.1 Raw heights and fixed vertical gates

Fix finitely many correctly signed lower and upper hallway orientations, a bounded box whose horizontal projection is I=[a,b], and the incoming strip. Outer supporting-line heights are variables z_i. Each moving inner line has the same height z_i minus one, in the same unit normal direction u_i. Additional fixed-angle strip boundaries can be included. At this point the z_i need not be attained support values.

Let E(z) be the intersection of the box, the outer constraints and endpoint strips, with the finite open lower and upper forbidden quadrants removed. Its area is denoted A(z), whether or not it is connected.

Fix 0<s_0<=1 and allow only heights belonging to normals with

\[
|(u_i)_y|\geq s_0
\tag{54.1}
\]

to change. All zero-vertical-component lines, including vertical gates of endpoint quadrants, stay fixed. Write W=b-a.

**Theorem 100 (uniform finite-envelope area control).** If every allowed height changes by at most epsilon, then

\[
\boxed{|A(z')-A(z)|\leq\frac{2W}{s_0}\,\varepsilon.}
\tag{54.2}
\]

This constant is independent of the number of sampled angles, their separation, and the contact combinatorics.

**Proof.** On a vertical line x=constant, a nonvertical wall has height

\[
y=(z_i-(u_i)_x x)/(u_i)_y,
\]

or the same expression with z_i replaced by z_i-1 for an inner wall. Its change is at most epsilon/s_0; unchanged walls have zero change.

Each lower quadrant cuts off a downward half-line whose threshold is the minimum of its two wall heights. Their union has threshold equal to the maximum of these minima. Each upper quadrant similarly cuts off an upward half-line, with threshold a minimum of maxima. The convex outer constraints give a lower maximum and an upper minimum. Intersecting everything yields an interval, possibly empty, whose length is the positive part of the upper threshold minus the lower threshold.

Minimum and maximum are nonexpansive in the sup norm. Each threshold therefore changes by at most epsilon/s_0, and the positive-part map is one-Lipschitz. The surviving length changes by at most 2epsilon/s_0. At fixed vertical gates the same assertion holds on each resulting x-region; a gate may make a fiber identically empty, but its x-location does not move. The fixed incoming strip and box bound the surviving lengths. Integrate over I. QED.

No contact-angle derivative, curvature derivative, or division by a small angle between two successive samples appears in this proof.

## 54.2 Area derivatives on the finite charts are order-zero measures

The raw arrangement has a finite piecewise-quadratic area formula, by the same line-intersection subdivision as Lemma 98, now without requiring feasibility or hull retention. On the interior of any full-dimensional chart let g_i be its partial derivatives with respect to the permitted heights. Theorem 100 gives

\[
\sum_i|g_i|\leq2W/s_0.
\tag{54.3}
\]

Indeed choose a height velocity with v_i equal to the sign of g_i, apply (54.2) along a sufficiently short segment in that chart, and divide by its length. The coefficient bound extends to a limiting chart at a boundary by continuity of its polynomial gradient. If some height relations are held identically, make this argument in the independent raw-height coordinates before restriction to those relations.

Assign each height its normal angle theta_i and merge any repeated coordinates. Then

\[
\mu=\sum_i g_i\,\delta_{\theta_i}
\]

is a signed measure, with total variation bounded by (54.3), and a sampled perturbation phi has chart derivative

\[
DA(z)[\phi]=\int\phi\,d\mu.
\tag{54.4}
\]

At a generic configuration with no coincident moving segments, g_i is precisely visible outer-edge length minus newly exposed inner-wall length. At a degenerate configuration different incident charts can give different limiting measures. There is no assertion of a unique two-sided derivative there.

## 54.3 What can now be passed to a subsequence

Let the meshes become dense and keep a compact angular interval J away from the two horizontal-normal directions. The selected boxes have uniformly bounded W, and |sin(theta)| has a positive minimum s_0 on J. Thus the restrictions of the chart measures to J have uniformly bounded total variation. They have weak-* convergent subsequences as measures on J.

For completeness, choose a countable dense subset of continuous functions on the compact interval, use the uniform bound to select a diagonal subsequence on that subset, and extend its limiting functional by the same bound to all continuous functions. The signed-measure representation of that bounded functional gives the subsequential limit. This is ordinary measure compactness, not a curvature conclusion.

Therefore angular refinement by itself does not force an uncontrolled derivative distribution of positive order in the interior. The remaining difficulty is the **identity satisfied by the limit**, not existence of some bounded distributional limit.

## 54.4 Raw feasibility and canonicalization are different steps

A connected E(z) is a legitimate finite-angle body under its raw hallway placements, provided its endpoint strip conditions hold. Tightening those placements to the actual hull supports preserves that body by Proposition 19. It need not preserve the raw envelope or its area as a function of all z.

For the selection penalty, its input is the actual hull of the body. Theorem 96 applies directly when that hull is the varied outer polygon. If a component loses a lobe, neither (54.2) for total envelope area nor (52.2) for the outer polygon estimates its lost component area. The pinching example in Note 53 makes the distinction explicit.

Thus the raw formulation is useful for deriving area coefficients, but it is not a license to substitute raw heights for true support values in the penalty or to count a disconnected union as a sofa.

## 54.5 Compactness does not make the limiting defect zero

Even with uniformly bounded measures and kappa_n tending to zero, Theorem 99 has constraint terms. A fixed nonzero point mass is itself a uniformly bounded weakly convergent sequence. There is no analytic principle making those terms vanish just because the meshes are dense.

At an unconstrained nonsmooth maximum, one must also combine incident charts correctly: for example -|s| has a maximum at zero but the two limiting chart derivatives are 1 and -1, neither zero. In a constrained chart the obstruction is stronger: the maximum of s on s<=0 has derivative 1 and a nonzero constraint normal. These elementary examples are not sofa counterexamples; they identify invalid limit inferences.

The proved conclusion of this note is the mesh-independent estimate and order-zero compactness. A full measure-balance theorem still needs an admissibility/normal-cone argument. No CI, Lean, numerical optimization, or computer algebra was used.
