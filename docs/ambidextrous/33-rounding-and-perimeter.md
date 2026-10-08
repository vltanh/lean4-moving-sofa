# 33. Feasible rounding and an unrestricted perimeter condition

This note gives an explicit operation that preserves both complete motions, not merely a finite-angle relaxation. It supplies regular-closed and polygonal approximations of every feasible body and a necessary perimeter inequality for every global maximizer. It does not impose the support-curvature cap of Theorem 65.

Write B_2 for the closed Euclidean unit disk.

## 33.1 A rounding operation that preserves both turns

For t>0 define

\[
T_t(S)=\frac{S+tB_2}{1+2t},
\qquad\lambda=\frac1{1+2t},\qquad\varepsilon=\frac{t}{1+2t}.
\tag{33.1}
\]

Here the addition is a Minkowski sum of the body with a disk; S need not be convex.

**Theorem 68 (motion-preserving rounding).** If S is a compact connected ambidextrous body in the posed problem, then T_t(S) is also such a body. Its motions may have exactly the same rotational parts as the original motions.

**Proof.** In the fixed hallway coordinates,

\[
H_- =\{x\leq1,\ y\leq1,\ x\geq0\ \text{or}\ y\geq0\},
\]

\[
H_+ =\{x\leq1,\ y\geq0,\ x\geq0\ \text{or}\ y\leq1\}.
\]

Since lambda+2epsilon=1, a direct coordinate check gives, for either sign,

\[
\lambda H_d+\varepsilon(1,1)+\varepsilon B_2\subseteq H_d.
\tag{33.2}
\]

For example, in H_- the two outer coordinates remain at most one. If an original point has x>=0, its new x-coordinate is at least epsilon-epsilon=0; otherwise its y-coordinate supplies the inner disjunction. The H_+ check uses y>=0 and the disjunction x>=0 or y<=1. The same calculation preserves the incoming and outgoing arms separately.

If an original motion is g_d(s)p=R_d(s)p+a_d(s), use the new motion

\[
\widehat g_d(s)p=R_d(s)p+\lambda a_d(s)+\varepsilon(1,1).
\]

Its image of T_t(S) is lambda g_d(s)S plus epsilon B_2 plus epsilon(1,1), so (33.2) proves feasibility throughout and at the endpoints. Initial rotational parts remain the identity. Compactness and connectedness are preserved by scaling and Minkowski addition with a disk. QED.

No reflection is applied to the body, and the two original motions need not be symmetric or monotone.

## 33.2 Regular closedness, connected interior, and strict clearance

The set S+tB_2 is the closure of the connected open set S+t int(B_2). The latter is connected because it is a union of open balls whose centers form a connected set; an alleged separation would partition those centers. It is path connected, as an open connected subset of the plane. Its closure is regular closed, and its interior remains connected since any additional interior point has a neighborhood meeting that dense open set.

Thus T_t(S) is regular closed with connected interior. Moreover T_t(S)->S in Hausdorff distance and

\[
|T_t(S)|\to|S|.
\tag{33.3}
\]

The area statement follows from S+tB_2 decreasing to S before scaling, using continuity of measure from above in a bounded neighborhood.

There is also a strict-clearance version. Choose 0<eta<1 and set

\[
\lambda=\frac{1-\eta}{1+2t},\qquad
\varepsilon=\lambda t,\qquad d=\frac{1-\lambda}{2}.
\]

Use lambda(S+tB_2) and replace the motion translation by lambda a_d(s)+d(1,1). Then

\[
d-\varepsilon=\eta/2,
\qquad\lambda+d+\varepsilon=1-\eta/2.
\]

Every outer inequality and at least one inner inequality in the hallway disjunction has margin at least eta/2. The endpoint arms have the same margin. Hence a Hausdorff outer perturbation of the new body by less than eta/2 still follows the same complete motions. This gives robust feasible approximations, with area tending to |S| as t and eta tend to zero.

## 33.3 Polygonal bodies are sufficient for the supremum

For a robust rounded body, take the union of closed cells of a sufficiently fine square grid that meet it. This is a finite compact polygonal set. It is connected because each cell meets the connected body contained in the union; a separation of the union would separate either a cell or the original body. It lies within one cell diagonal of the rounded body, so the clearance estimate makes it feasible for both original rotational histories with the modified translations.

Choosing the mesh, t, and eta to tend to zero gives connected polygonal feasible bodies converging to S in Hausdorff distance and area. The lower area bound comes from containment of the rounded body, and the upper bound from Hausdorff upper semicontinuity.

**Corollary 69 (exact polygonal density).** The supremum of the posed ambidextrous problem is unchanged if one restricts to compact connected polygonal bodies. This assertion concerns the supremum; it does not assert that an optimal body is polygonal.

Unlike the finite-angle constructions of Note 32, these approximants satisfy the full original continuous motions. No claim is made that their curvature measures obey the bound required in Theorem 65.

## 33.4 Every maximizing body has controlled outer growth

Let S be any global maximizer, with area V. Theorem 68 and maximality imply, for every t>0,

\[
\boxed{|S+tB_2|\leq(1+2t)^2V.}
\tag{33.4}
\]

In particular its upper outer Minkowski perimeter satisfies

\[
\limsup_{t\downarrow0}\frac{|S+tB_2|-|S|}{t}\leq4V.
\tag{33.5}
\]

This is a necessary condition for **every** maximizer, obtained without the candidate value or any differentiability of S.

It also implies finite perimeter in the distributional sense. To see this directly, put
\(u_t(x)=\max(1-\operatorname{dist}(x,S)/t,0)\).
These compactly supported Lipschitz functions tend to 1_S in L^1. Their gradients vanish almost everywhere on S and outside S+tB_2, and have norm at most 1/t elsewhere. Thus

\[
\int|\nabla u_t|\leq\frac{|S+tB_2|-|S|}{t}\leq4V+4Vt.
\]

For every smooth compactly supported vector field phi with |phi|<=1, integration by parts and passage to the limit give
\(\int_S\operatorname{div}\phi\leq4V\).
Taking the supremum over these fields is the definition of perimeter. Therefore

\[
\boxed{\operatorname{Per}(S)\leq4|S|.}
\tag{33.6}
\]

For a body with piecewise smooth boundary this is the usual boundary length, including hole boundaries. The cutoff proof also covers arbitrary compact maximizers.

## 33.5 Candidate check and a strict first-order loss

For the explicit candidate, its boundary length can be computed from the contact curves without integrating its coordinates. The curved hull boundary contributes twice the integral of rho_f+rho_g. Replace the two horizontal faces by the two niche boundaries. Using B'=(rho_f-1)nu, D'=(1-rho_g)mu, the zero early rho_f and zero late rho_g from Note 18 cancel the remaining outer-arc terms, yielding

\[
\operatorname{Per}(\Sigma_*)
=2\pi-4\beta+2\int_\beta^{L-\beta}\sqrt{p_*^2+q_*^2}\,dt.
\tag{33.7}
\]

On the middle interval p_*<0<q_*. The stationary equations give
\(p_*'=-(q_*+1)/2\) and \(q_*'=(p_*-1)/2\), while
\(q_*(\beta)=\tfrac12\cot\beta-1\),
\(p_*(L-\beta)=-q_*(\beta)\).
Consequently

\[
2\pi-4\beta+2\int_\beta^{L-\beta}(q_*-p_*)\,dt
=4(\cot\beta-2+\beta)=4M.
\]

Subtracting (33.7),

\[
4M-\operatorname{Per}(\Sigma_*)
=2\int_\beta^{L-\beta}
\left[q_*-p_*-\sqrt{p_*^2+q_*^2}\right]dt>0.
\tag{33.8}
\]

The strict sign uses both nonzero components in the interior. Thus the rounding direction is strictly area-decreasing to first order at the candidate, consistent with but not proving its optimality. The usual first-order parallel-area formula applies to this explicitly piecewise smooth boundary.

## 33.6 Limitation

Finite perimeter of the body is much weaker than absolute continuity and pointwise domination of the convex hull's curvature measure. Rounding leaves any exposed-edge atoms of the hull, merely scaled, and adds a diffuse disk term. Thus it cannot be cited as a proof of the curvature hypothesis in Theorem 65.

The operation supplies genuine feasible regularizations and one unrestricted variational inequality. The sharper support-height/angle variations needed for closure remain to be established.
