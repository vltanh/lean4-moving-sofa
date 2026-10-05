# 53. The finite polygonal Euler statement includes a normal cone

This note derives a finite-dimensional necessary condition directly at a selected penalized optimizer. It does not assume smooth boundary curvature, a single active wall, or that a pinching constraint is inactive. Its conclusion is an exact multiplier identity, not the unrestricted curvature bound.

The setting is a fixed-angle slice of the finite class: the sampled orientations and the endpoint angles are frozen at their selected values. Thus this calculation alone cannot prove that the endpoint angles are full quarters.

## 53.1 A parameter chart with actual geometric constraints

Fix a selected polygonal body C and its convex hull K. Use a finite set H of supporting normals that includes all edges of K and all normals needed by the finite hallway placements, terminal strips, and sampled penalty. Let z_0(u)=h_K(u), and put

\[
K(z)=\bigcap_{u\in H}\{x:x\cdot u\leq z(u)\}.
\]

In a sufficiently small bounded neighborhood of z_0 the polygons contain a common positive-radius disk, by Theorem 96. For each hallway use its **actual** supporting heights h_{K(z)} in its two directions, not an assumed equality between a redundant z(u) and an attained support value. Let E(z) be K(z) with the finitely many lower and upper canonical quadrants removed.

The following requirements define the competitors considered here:

- E(z) is compact and connected;
- conv(E(z))=K(z);
- the incoming and outgoing strip conditions and the selected box constraint hold;
- when using the original finite class of Note 39, its exact-span normalization holds too.

The area threshold is inactive in a small neighborhood of a selected optimizer, since its area is at least V>M>8/5. These are genuine finite-angle competitors; no full continuous motion is being inferred.

**Lemma 98 (finite polyhedral charts).** A neighborhood of z_0 can be subdivided into finitely many polyhedral charts on which the above conditions are given by affine equalities and inequalities, the sampled support penalty is piecewise affine, and |E(z)| is a quadratic polynomial. Lower-dimensional charts and zero-width connections are allowed.

**Proof.** All supporting-line normals are fixed. Every intersection of two nonparallel lines is therefore an affine function of z. The signs of a third line evaluated at that intersection are affine inequalities. A finite subdivision by these signs fixes the polygon incidences and which intersection attains each required support value. The attained support values, and hence the inner-wall offsets, are affine on that subdivision. Apply the same construction again to the resulting finite collection of outer and inner lines, also fixing the ordering of their intersection abscissae. Parallel lines are ordered by their offsets; they do not require division by a zero determinant.

For correctly signed finite turns, each lower quadrant is downward closed and each upper quadrant upward closed. At a fixed x, the surviving section of K(z) is an interval or empty. On each vertical band of the subdivided arrangement, its top and bottom boundaries are selected affine-in-x lines with fixed slopes and offsets affine in z. Their break abscissae are affine in z. Having nonempty fibers throughout the horizontal projection is equivalent to nonnegative gaps at the endpoints of these bands. Those are affine inequalities. The interval-fiber argument then proves connectedness. If a connected surviving set retains K(z) as its hull, it has that full projection, so these inequalities are necessary as well.

Hull retention is also a finite condition: every vertex of K(z) must avoid every open forbidden quadrant. For each vertex/quadrant pair, select at least one of the two nonnegative inner-wall clearances. There are finitely many such selections, each imposing affine inequalities. A convex polygon is the convex hull of its vertices, so these conditions are sufficient and necessary for conv(E(z))=K(z). Compactness follows from closedness in K(z). Strip widths and box conditions are affine after the chosen support subdivision; an exact-span requirement is an affine equality.

Finally, integrate the affine fiber height over each band. This is one half of its endpoint-height sum times its width, a product of affine functions of z. Summation gives a quadratic polynomial. Collapsing bands contribute zero by the same formula. Alternatively, the signed polygon-area formula gives the same conclusion from affine vertices. All subdivisions are finite. QED.

The chart inequalities include both actual feasibility restrictions and bookkeeping choices such as vertex incidence or wall ordering. A multiplier for a chart wall must not automatically be interpreted as a physical contact force.

For the selected canonical saturation, E(z_0)=C. Indeed C lies in the envelope built from its own hull and the same finite canonical placements. Its horizontal projection equals that of K. Every envelope fiber over that projection contains a point of C, and is an interval. The full envelope is connected, so cannot add a point outside C if C was already a saturated component in the finite construction of Note 32.

## 53.2 Exact optimality on one admissible chart

Write a chart containing z_0 as

\[
c_j(z)\geq0\quad(1\leq j\leq m),\qquad Az=b,
\]

where c_j are affine, and write its area polynomial as F(z). The sampled penalty has the form

\[
r(z)=\max_{k\in\mathcal I}\ell_k(z),
\]

where the affine functions ell_k include both signs of the difference between an attained support and the prescribed target support. Let kappa>0 be the selection penalty.

**Theorem 99 (finite optimality with the constraints retained).** If z_0 locally maximizes F-kappa r on this chart, then there are nonnegative numbers mu_j for the active constraints c_j(z_0)=0, weights theta_k>=0 on the active penalty functions ell_k(z_0)=r(z_0) with sum theta_k=1, and a vector lambda such that

\[
\boxed{
\nabla F(z_0)
=\kappa\sum_k\theta_k\nabla\ell_k
-\sum_j\mu_j\nabla c_j+A^T\lambda.
}
\tag{53.1}
\]

No differentiability of the maximum penalty, constraint qualification, or strictly feasible point is assumed.

**Proof.** Introduce the epigraph variable w and maximize the differentiable function F(z)-kappa w over the polyhedron defined by the chart and w>=ell_k(z). The point (z_0,r(z_0)) is a local maximizer. For every direction in its polyhedral tangent cone, the directional derivative is nonpositive: every such direction gives a short feasible segment. The polar of the cone defined by affine inequalities is the nonnegative span of their outward normals, together with the equality-normal subspace. This follows directly from finite-dimensional separation: a vector outside that span has a separating direction satisfying the tangent inequalities but a positive scalar product with the vector.

Apply this cone identity to (grad F,-kappa). An active epigraph constraint contributes beta_k(grad ell_k,-1), beta_k>=0. The w-component gives sum beta_k=kappa. Divide by kappa to obtain theta_k. The other active constraints contribute -mu_j grad c_j, with the sign fixed by c_j>=0. The equality rows contribute A^T lambda. This is (53.1). QED.

The theorem applies to every admissible incident chart. One cannot select a convenient chart and discard the others, nor discard the normal cone of the selected one.

## 53.3 What replaces a naive side-balance equation

In a differentiable configuration without coincident moving line segments, the derivative of F in a floating-height direction is the visible outer-edge gain minus the newly removed inner-edge length, as in Proposition 48. Equation (53.1) says this difference equals a small penalty term **plus constraint terms**, not necessarily just the small penalty term.

For a direction v tangent to all active chart constraints and to Az=b,

\[
DF(z_0)[v]=\kappa\sum_k\theta_kD\ell_k[v].
\tag{53.2}
\]

When the varied bodies retain the intended hull, Theorem 96 bounds the right side uniformly by kappa DC/r_0 for bounded supporting-height speed C. This yields a genuine asymptotic balance for these tangent directions.

For a general one-sided admissible direction, the terms -mu_j Dc_j[v] remain. In particular, kappa tending to zero does **not** imply that these terms tend to zero. At coincident lines, work with the area's polynomial on each chart rather than substituting an unproved two-sided strip derivative.

## 53.4 A fixed-line pinching test

The need to retain a connectivity normal can already be seen in an elementary polygon family. For |s|<1/10 put w=1+2s and

\[
E_s=\{(x,y):-w\leq x\leq w,\quad0\leq y\leq|x|-s\}.
\]

This is a Boolean combination of half-planes with **fixed normals** and affine offsets. Its hull is [-w,w] times [0,w-s], and all four extreme vertices survive for every s in this range.

For s<=0 the set is connected and

\[
|E_s|=\int_{-w}^{w}(|x|-s)\,dx=w^2-2sw=1+2s.
\]

For s>0 there is a gap |x|<s, and there are two equal components, each of area (1+s)^2/2. Thus at s=0 the largest connected-component area has a local maximum of one, even though the derivative of the connected-side area polynomial is 2. The connected chart has constraint c(s)=-s>=0; its nonzero normal multiplier is mu=2, since 2=-mu c'(0).

This is a fixed-line polygonal example, **not** a claimed pair of canonical unit-hallway motions. It disproves the purely logical inference that common-hull retention and vanishing selection penalty make all connectivity normals disappear. A special cancellation for sofa geometry would require an additional proof.

## 53.5 The revised finite-to-continuum obligation

The finite polygonal step is no longer an unspecified instruction to "derive Euler equations." It has a precise normal-cone form. To infer the unrestricted support-curvature/contact inequalities, one must control the contributions from active feasibility constraints and eliminate dependence on artificial chart choices when passing to the limit.

This note does not bound or eliminate those multipliers, derive full endpoint angles, or prove the sharp global theorem. It identifies the exact extra terms that a valid proof must address. The support-amplification estimate is available; the necessary admissibility and constraint analysis are not replaced by it.

All derivations are pen-and-paper. No CI, Lean, numerical optimization, or computer algebra was used.
