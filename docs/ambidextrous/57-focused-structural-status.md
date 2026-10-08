# 57. Current proof boundary: global functional calibration, geometric enclosure still missing

**The unrestricted ordinary-area proof is not closed.** The new AF supplement proves the adaptive functional's exact global maximum and equality case without curvature or contact assumptions, for all normalized real H^1 profiles of horizontal width at least one. A second supplement computes a strictly positive ordinary-area defect on actual feasible near-candidate bodies. Thus the two sides of the intended sandwich are now sharply distinguished.

The numbered contact results through Note 67 and the WG width gate remain in force within their stated scopes. This is the current research-entry ledger. Earlier inventories are historical snapshots. All proofs are written and self-reviewed, not independently refereed or Lean-verified. No novelty or best-known-bound claim is made.

## 57.0 The sharp analytic optimization is now completed on a much larger domain

[Theorem AF3](adaptive-functional-global-calibration.md) applies to every real periodic H^1 profile h with

\[
h(\pi/2)=1,\quad h(3\pi/2)=0,\quad h(0)+h(\pi)\geq1.
\]

It proves

\[
\widetilde{\mathcal Q}(h)\leq M,
\qquad M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0,\quad Y>0,
\]

with equality exactly for h=h_*+b cos(theta). It does not assume that h is convex or feasible, or that its curvature or contact order satisfies any inequality. The width condition is automatic for a genuine unit-span hull containing a body of area greater than one.

The proof fixes the horizontal endpoint values h(0)=h(pi)=a first. Differences of two half-profiles vanish at both ends. For z=v+iw and y=exp(-it/2)z, the negative quadratic part of the unpenalized half-functional is

\[
\frac12\int_0^{\pi/2}(|y'|^2-\tfrac94|y|^2),
\]

strictly positive on nonzero Dirichlet variations by the first eigenvalue four. The subtracted contact losses are concave. Consequently each fixed-width fiber has a unique maximizer, and its two reflection symmetries follow in function space.

The Euler momenta P=p+min(p,0), Q=q+max(q,0) satisfy a globally Lipschitz piecewise linear Hamiltonian system. At a stationary free width, P(0)=1/2 and Q(pi/2)=-1/2. Classifying the transit times gives only the radius-one-half disk profile and the candidate. The candidate cubic comes from the unique orbit of duration pi/2. The disk boundary has smaller value, and an explicit large-width optimizer makes the value tend to minus infinity. This supplies existence of the global functional maximum, rather than just a stationary-point classification.

The candidate's exact value is the calculation in Note 14. The AF supplement independently supplies the widened domain, fixed-width coercivity, critical-orbit classification and equality reduction. It does not claim independent review of every earlier geometric lemma.

### The geometric enclosure fails even for the adaptive functional

[Proposition AF4](adaptive-functional-enclosure-counterexample.md) uses the already verified protected high-curvature bodies and their convexification repairs. For a nonzero first-quarter increment u and its reflected copy,

\[
\boxed{|S|-\widetilde{\mathcal Q}(h_{\operatorname{conv}S})
=\int_J(u'^2-u^2)>0.}
\]

The actual area gain and the functional gain are computed separately before subtraction. The Dirichlet inequality supplies the strict sign. These bodies have the candidate's exact horizontal width and areas tending to M from below. Thus neither AF3's width condition nor proximity in area makes enclosure automatic.

Their strict suboptimality comes from a feasible improving repair, not from the false inequality |S|<=tilde Q(h). This counterexample is different from the earlier failure of **fixed** switching angles. Both are retained.

A direct enclosure theorem for actual global maximizers would now suffice without first deriving the old support conditions. Alternatively, a constructed surrogate profile may use AF3 even if it is not convex or feasible. In either case the ordinary-area comparison still needs proof. For uniqueness a surrogate also needs equality/containment recovery; selecting a profile of value M is not such a construction.

## 57.1 The structural route no longer has an independent full-turn premise

[Theorem WG2](64-width-gate-from-curvature-and-contact.md) proves, for a unit-span convex hull satisfying open-quarter curvature domination and both contact inequalities,

\[
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.}
\]

Its centrally symmetric auxiliary body C=(K+((0,1)-K))/2 has exactly the widths of K. Quarter-moment inequalities and inherited endpoint contact traces show that C contains a unit-height rectangle of width 2-sqrt(2). **C is not asserted feasible.** This is a width comparison, not a symmetrization of an actual sofa.

For a body of area greater than sqrt(2), the general canonical endpoints already have magnitudes greater than pi/4. The bound is strictly greater than one before pi/2, so the outgoing unit strips force full turns.

[Corollary WG4 in Note 31](31-closed-curvature-class-theorem.md) therefore gives the sharp area and exact body-uniqueness theorem from just curvature domination and both contact inequalities in one common incoming unit-span normalization. Those conditions remain sufficient for the **geometric enclosure** even though they are no longer assumptions of the analytic theorem AF3.

Only endpoint contact traces are used in the width gate. The existing geometric profile proof uses the full contact inequalities. Domination only at floating normals also does not control a pinned partial-terminal normal lying inside an open quarter.

## 57.2 Projection-endpoint source corners are harmless under the prior outer-clearance assumptions

[Theorem 118 in Note 64](64-positive-corners-are-interior.md) gives

\[
x_+-c_x\geq\frac{1-(1-c_y)\sin t}{\cos t},\qquad
c_x-x_-\geq\frac{1-(1-c_y)\cos t}{\sin t}.
\]

For an interior-angle lower corner with c_y>=0, both projection margins are strictly positive. At or beyond an endpoint the corner is strictly below the incoming strip, and its sufficiently small circular support replacements remove no strip points. Reflection gives the upper case.

Corollary 119 removes this residual case when the outer-clearance and floating-normal assumptions of the singular repair hold. The independently added duplicate calculation is now a pointer, preserving its history without competing theorem numbers.

## 57.3 Fiber clearance is removed for clear singular-continuous contacts

[Theorem 130 in Note 67](67-removing-the-fiber-clearance-hypothesis.md) proves that a normalized maximizing hull's singular-continuous curvature gives zero mass to floating normals whose exposed point is strictly clear of both closed swept niches. It requires no candidate neighborhood, full-turn premise, input smoothness or positive fiber gap.

### Two-corner graph measures

[Note 65](65-two-corner-pinch-measures.md) derives, for a=c_x', b=c_y', z=b/a,

\[
(Dz)_{\rm na}
=\frac{-q\,\sigma_{f,\rm na}+p\,\sigma_{g,\rm na}}{a^2}
+\frac{q-p+2p^2+2q^2}{a^2}\,dt.
\]

Exact quotient differences handle jumps. With graph orientation included, the source terms have positive signs at an active lower corner and negative signs at an upper corner. The nonnegative gap between the two graphs controls their source curvature on its zero-contact set by BV locality. Theorem 122 treats strict transverse charts; Lemma 129 in Note 67 permits the coefficient signs to be required only at actual contact points. Countably many rational charts suffice.

This does not assert nonzero horizontal speed for every corner graph or a sharp density bound of one.

### Vanishing-sensitivity repair

[Note 66](66-zero-sensitivity-singular-repair.md) handles the complementary zero-coefficient case. At suitable density scales, its circular replacement gains retained hull area G_r>=c m(r)^2r while the uniform hallway error is e_r=o(m(r)^2r). A connected old-niche comparison retains the old body and clear added region. Scaling by 1/(1+e_r) restores the actual motions, with exact gain

\[
\frac{G_r-|S|(2e_r+e_r^2)}{(1+e_r)^2}>0.
\]

The scaling cost is paid. It is not an assertion that an infeasible support variation has zero cost. Atomic versions retain their separate trace hypotheses.

### Stationary blocking corners

Lemma 128 in Note 67 uses retained extreme endpoints of a stationary corner. If an opposite interior corner coincides with it, the fixed-point tests force both one-sided traces to p=-1,q=1. BV locality excludes source singular-continuous curvature on that level set.

Theorem 130 combines these mechanisms with the earlier inactivity, positive-gap and oblique-ceiling arguments. Countable blocker images are discarded only for nonatomic source measures, not for atoms.

## 57.4 What remains of singular-continuous curvature

[Corollary 131](67-removing-the-fiber-clearance-hypothesis.md) leaves, up to a curvature-null set, only outer points that themselves coincide with canonical inner corners. That is the source **outer point**, not merely its associated inner corner pinching a fiber elsewhere.

The residual outer/inner-corner coincidence set is not proved null. Hidden/coincident edge atoms, pinned interior-quarter normals and the sharp bound on the absolutely continuous density are separate unresolved matters. The new AF calibration does not turn these contact exclusions into a completed ordinary-area comparison.

## 57.5 The two available routes, with their missing statements

Attainment and selection of any prescribed maximizing hull are available. The remaining sufficient routes are now:

**Direct geometric enclosure.** Prove |S|<=tilde Q(h_conv S) for an actual maximizing body in a common incoming unit-span normalization, or prove a suitable area-dominating surrogate comparison. AF3 supplies the sharp value and profile equality case. AF4 rules out proving this by feasibility alone. A surrogate requires additional equality recovery for body uniqueness.

**Structural enclosure.** Derive the complete open-quarter curvature domination and both contact inequalities for a relevant maximizing hull. WG3 supplies full turns; the weak profile/no-clipping theorem supplies actual area equality with the functional; the sharp calibration finishes. Proving the conditions in different normalizations is not enough.

For either route, one attained maximizer suffices for the optimal value. Exact uniqueness requires every maximizer or an equality-preserving argument recovering each original body.

The finite necessary optimality equation still has the form

\[
\nabla F_n=\kappa_n r_n-\sum_j\mu_{n,j}\nabla c_{n,j}+E_n^T\lambda_n,
\qquad\mu_{n,j}\geq0.
\]

Only the selection penalty is known to vanish. Bounded normal work does not remove the contact multipliers, and all incident admissible charts must be considered. Neither the new analytic theorem nor the width gate supplies those missing geometric variations.

## 57.6 Audit and concurrent-edit reconciliation

For AF1–AF3, the audit checked the sign in the complex gauge identity, all four fixed-width trace conditions, weak upper semicontinuity, the momentum inverses, both Hamiltonian quadrant transit formulas, the full-period lower bound, the width-one boundary, and the explicit large-width optimizer. The candidate cubic follows from an injective tangent identity on the stated interval. Function-space symmetries are never called feasible body symmetrizations.

AF4 expands the functional and ordinary-area changes independently. The reflected factor two and the positive Dirichlet remainder are retained. The earlier actual area comparison is used only on its verified protected family; the counterexample is not generalized to an unverified body.

The WG calculation retains affine-reflection terms, distinct axis derivative traces and the moment inequality directions. The auxiliary rectangle belongs to the symmetral rather than being assumed in K.

The numbered contact work checks graph orientation, quotient jumps, one-sided level-set locality, countable chart covers, and the distinction between singular-continuous and atomic mass. These files were added concurrently and preserved. WG and AF labels are separate from the numbered sequence; the duplicate projection proof is consolidated by a pointer. This reconciliation is not independent verification of the full combined chain.

## 57.7 Execution

All changes are Markdown under docs/ambidextrous. Every research commit includes `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra or manuscript build was used. The existing manuscript, Lean sources, dependencies and workflows are unchanged. The PR remains open and draft because the unrestricted geometric comparison and independent proof review are unfinished.
