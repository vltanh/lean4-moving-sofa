# 57. Focused structural status through Note 67 and the width-gate supplement

**The unrestricted proof is not closed.** The sufficient sharp route now has two support hypotheses rather than three: curvature domination and both contact inequalities imply full turns. Separately, the new singular-curvature argument removes the fiber-clearance assumption at strictly clear outer points of any maximizing hull.

This is the current research-entry ledger. Note 51 is the preceding broad inventory; older ledgers are historical snapshots. These are written arguments with self-review, not independent refereeing or Lean verification. The entire preceding proof chain has not been independently audited. No novelty or best-known-bound claim is made.

## 57.1 Full turns are no longer an independent hypothesis

[Theorem WG2 in the width-gate supplement](64-width-gate-from-curvature-and-contact.md) applies to a unit-span convex hull satisfying curvature-measure domination on the open quarters and both contact inequalities. It proves

\[
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.}
\]

The proof uses the centrally symmetric auxiliary body C=(K+((0,1)-K))/2. Its widths equal those of K. Quarter-moment inequalities and inherited endpoint contact conditions show that its two horizontal faces contain [-d,d], where d=1-1/sqrt(2); convexity gives the corresponding unit-height rectangle.

**C is not asserted to be feasible.** This is a comparison of widths, not a feasibility-preserving symmetrization or a proof that the original hull is symmetric.

For a body of area greater than sqrt(2), the canonical endpoint magnitudes already exceed pi/4 by the two-strip bound. The new width lower bound is strictly greater than one for pi/4<=|t|<pi/2. The outgoing unit strips therefore force both endpoints to be full quarter turns.

[Corollary WG4 in Note 31](31-closed-curvature-class-theorem.md) consequently gives the sharp bound and exact uniqueness from just

\[
\sigma_K\leq dt\quad\text{on every open quarter},
\qquad p\leq q\quad\text{for both }h_K\text{ and }h_K^\rho,
\]

in one common unit-span normalization. Full turns follow, rather than being an extra premise. Neither of these two support conditions has been proved for every unrestricted maximizer.

Only endpoint contact traces are needed by the width calculation. The full contact inequalities are still needed by the adaptive-functional theorem. Bounds only at floating normals are also insufficient: before endpoint completion a pinned terminal normal may lie inside a coordinate quarter.

## 57.2 The source-corner projection obstruction is removed

[Theorem 118 in Note 64](64-positive-corners-are-interior.md) gives the elementary estimates

\[
x_+-c_x\geq\frac{1-(1-c_y)\sin t}{\cos t},\qquad
c_x-x_-\geq\frac{1-(1-c_y)\cos t}{\sin t}
\]

for an interior-angle lower canonical corner in a hull contained in [x_-,x_+] times [0,1]. If c_y>=0, both distances are strictly positive. At or beyond a projection endpoint the corner instead lies strictly below the strip. Its sufficiently small circular support replacements therefore remove no strip points. Reflection handles the upper turn.

Corollary 119 deletes the projection-endpoint case from the prior singular-repair residual whenever its outer-clearance and floating-normal hypotheses apply. The independently added calculation at `65-active-corners-stay-inside-the-projection.md` is now a pointer to this common result; the duplicate proof is retained in history rather than maintained with conflicting theorem numbers.

## 57.3 New result: no fiber assumption for clear singular-continuous contacts

[Theorem 130 in Note 67](67-removing-the-fiber-clearance-hypothesis.md) proves:

> For any normalized global maximizer, its singular-continuous hull curvature gives zero mass to the set of floating normals whose exposed point is strictly clear of the closures of both swept niches.

This needs neither candidate proximity, full quarter turns, input smoothness, nor positive surviving-fiber clearance. The argument handles actual pinches rather than presuming that a zero-area connection is harmless.

There are three complementary mechanisms.

### A. Two corner graphs give a measure inequality

[Note 65](65-two-corner-pinch-measures.md) treats opposite corners on bi-Lipschitz graph charts. Put a=c_x', b=c_y', z=b/a. On nonatomic parts the exact identity is

\[
(Dz)_{\rm na}
=\frac{-q\,\sigma_{f,\rm na}+p\,\sigma_{g,\rm na}}{a^2}
+\frac{q-p+2p^2+2q^2}{a^2}\,dt.
\]

At source jumps the exact quotient difference, not a derivative at one trace, is used. With the graph orientation included, the source curvature terms have positive coefficients at an active lower corner and negative coefficients at an active upper one.

Connected feasibility gives a nonnegative gap G-F between the two selected graphs. BV level-set locality controls its derivative measure on {F=G}. Theorem 122 bounds all source curvature there under strict component bounds. Lemma 129 in Note 67 weakens the surrounding-chart conditions: the needed coefficient signs are imposed by feasibility on the contact set itself. The positively weighted source singular curvature is excluded even when nearby contact types differ. Countably many rational charts suffice.

This does not assert that every corner graph has nonzero horizontal speed or a globally signed second derivative.

### B. A vanishing coefficient pays for feasibility repair

[Note 66](66-zero-sensitivity-singular-repair.md) handles source singular curvature where the other velocity component vanishes. For example, at a second-source singular point with p=0 and q nonzero, BV locality gives sigma_f=(q+1)dt on the continuous level set of p. At good density scales, if m(r) is the central sigma_g mass, then

\[
r=o(m(r)),\qquad \sigma_f(J_r)=o(m(r)).
\]

The circular replacement raises the support by O(m(r)r) and gains hull area at least c m(r)^2r. A direct comparison of the two wall families bounds the **uniform hallway error** by e_r=o(m(r)^2r). This is stronger than just a bound on total lost area.

Form a connected comparison body using the new hull and old niches, retaining the entire old body and the strictly clear added region. Scaling it by 1/(1+e_r) gives genuinely feasible motions. Its exact area gain is

\[
\frac{G_r-|S|(2e_r+e_r^2)}{(1+e_r)^2}>0.
\]

The scaling cost is explicitly paid; it is not omitted from a claimed variation. Theorem 125 gives the singular-continuous exclusion, and Corollary 126 plus Section 67.6 give corresponding atom exclusions under their trace and outer-clearance conditions.

### C. A stationary blocking corner forces a constant-velocity level

Lemma 128 in Note 67 uses the retained exposed-face endpoints of a stationary corner. If an opposite corner coincides with it at an interior motion angle, two fixed-point feasibility tests force that other corner's velocities to satisfy

\[
p_-=p_+=-1,\qquad q_-=q_+=1.
\]

BV locality shows that this level set carries no source singular-continuous curvature. Thus an unparametrizable stationary blocking corner cannot be left as a new unexplained case in the clear-source proof.

The proof of Theorem 130 also retains the earlier inactive-corner and positive-gap improvements, the oblique affine-ceiling bound, and a countability argument for terminal or jumping blocking parameters. The latter is valid for singular-continuous measures, not for edge atoms.

## 57.4 The exact remaining singular-continuous support

[Corollary 131](67-removing-the-fiber-clearance-hypothesis.md) combines Theorem 130 with the outer-contact classification and the width-one curvature identity:

\[
\boxed{\text{Remaining singular-continuous curvature can occur only at
outer points that themselves coincide with canonical inner corners.}}
\]

The statement is up to a curvature-null set. The relevant outer point belongs to the source support normal; it is not merely the source inner corner pinching the body somewhere else.

The previous ledger listed three residual possibilities. Projection-endpoint source corners are removed by Note 64. Actual pinching source fibers at clear outer points are removed by Notes 65–67. The outer/inner-corner coincidence set itself has **not** been proved null.

Nor does this prove global curvature domination: hidden/coincident edge atoms, pinned interior-quarter normals, and the sharp bound on the remaining absolutely continuous density are separate obligations. Atoms cannot be discarded using the countability argument applied to singular-continuous curvature.

## 57.5 Finite optimality and the remaining global route

Attainment and selection of any prescribed maximizing hull are available in the earlier notes. Notes 52–55 supply mesh-independent variation estimates, finite contact charts, and the exact constrained optimality equation

\[
\nabla F_n=\kappa_n r_n-\sum_j\mu_{n,j}\nabla c_{n,j}+E_n^T\lambda_n,
\qquad \mu_{n,j}\geq0.
\]

Only the selection penalty is known to vanish. Contact multipliers are not removed merely by bounded normal work. Artificial chart walls and physical constraints must be distinguished across all incident admissible charts. The finite pinching counterexample remains valid.

The sufficient unrestricted structural conclusion is now:

1. curvature-measure domination by dt on every open coordinate quarter, including all residual singular/atomic and absolutely continuous parts;
2. both contact-order inequalities, in the same unit-span normalization.

A proof for one attained maximizer identifies the value M. A proof for every maximizer, or an equality-preserving comparison recovering each body, gives exact uniqueness. The width-gate supplement then supplies full turns; they are not an independent premise.

The new clear-contact theorem does not prove either entire support condition. A chart-dependent measure bound is not the sharp bound one. A localization of the remaining singular measure is not proof that its support is null. The unrestricted argument is not complete and is not merely awaiting compilation.

## 57.6 Audit and coordination

The contact-quadratic factorization and weak-profile argument were reread; the sign calculations used here agree with their displayed identities. This was not a full independent audit of the entire prior chain.

For the new graph calculation, the orientation factor under a decreasing abscissa, the exact quotient jump, and the coefficient signs on the contact set were checked separately. The level-set argument uses traces and signed-measure locality, not an assertion about almost-everywhere derivatives alone. Countable chart covers and countable blocker images are assigned only to the appropriate nonatomic measures.

For the zero-coefficient repair, the one-wall affine envelope identity is separated from the complete min-wall estimate. The old-body comparison is connected before scaling; the explicit scaling then restores every inner disjunction and endpoint inclusion. Its area cost is kept in the gain formula.

For stationary reciprocity, the tested points are retained extreme endpoints of the hull, not points merely assumed to lie in the body. The differentiated constraint is at the other, interior motion angle. One-sided inequalities and nonnegative support jumps force both traces, rather than presuming differentiability.

The branch received concurrent width-gate and projection-corner work during this pass. These results were read and preserved. The width-gate statements now use WG1–WG4 labels; the duplicate projection proof is a reference pointer. The numbered Notes 64–67 retain Theorems 118–131. This avoids changing the meaning of previously committed results or overwriting other work.

## 57.7 Execution

All changes are Markdown under docs/ambidextrous. Every research commit includes `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was used. The existing manuscript, Lean sources, dependencies, and workflow definitions are unchanged. The PR remains open and draft, with no merge or unrestricted-completion claim.
