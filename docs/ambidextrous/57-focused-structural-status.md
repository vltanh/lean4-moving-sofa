# 57. Focused structural status through Notes 64–65

**The unrestricted proof is not closed.** The current pass removes an independent hypothesis from the sharp theorem: full quarter turns follow from the curvature and contact conditions. It also eliminates the projection-endpoint source-corner case from the prior singular-curvature residual list.

This remains the research-entry ledger. Note 51 is the preceding broad inventory; older ledgers are historical snapshots. These are written arguments with self-review, not independent refereeing or Lean verification. The full earlier proof chain has not been independently audited.

## 57.1 The independent full-turn obligation is removed

[Theorem 119](64-width-gate-from-curvature-and-contact.md) applies to any unit-span convex hull satisfying curvature-measure domination on the open quarters and both contact inequalities. It proves

\[
\boxed{w_K(t)\geq(2-\sqrt2)|\cos t|+|\sin t|.}
\]

The argument uses the centrally symmetric auxiliary body

\[
C=\tfrac12(K+((0,1)-K)).
\]

Its widths equal those of K, and its quarter curvature bounds and upper-half contact condition are inherited from the two original halves. The two quarter-moment inequalities and endpoint contact traces show that both horizontal faces of C contain [-d,d], where d=1-1/sqrt(2). Hence C contains [-d,d] times [0,1], giving the width estimate.

**C is not asserted to be feasible.** Its only use is a width comparison. No symmetry of a maximizing sofa or feasibility-preserving Minkowski interpolation is presumed.

For a body of area greater than sqrt(2), the canonical endpoint magnitudes exceed pi/4 by the two-strip bound. The new width estimate is strictly greater than one throughout pi/4<=|t|<pi/2. The outgoing unit-strip conditions therefore force both endpoints to be full quarter turns. This is Corollary 120, not a separate maximizer-specific assumption.

Consequently [Corollary 123](31-closed-curvature-class-theorem.md) strengthens the branch's sharp geometric theorem to arbitrary original two-turn motions. It needs only, in one common unit-span normalization,

\[
\sigma_K\leq dt\text{ on the open quarters},
\qquad p\leq q\text{ for }h_K\text{ and }h_K^\rho.
\]

It gives area at most M and exact uniqueness. Those two support conditions remain unproved for unrestricted maximizers; the new argument does not supply them.

Only endpoint traces of the contact inequalities are used to obtain the width gate. The full inequalities are still required by the sharp adaptive-functional argument. Establishing just endpoint traces would therefore not complete the proof.

## 57.2 One singular-contact residual case is also removed

[Lemma 121](65-active-corners-stay-inside-the-projection.md) gives a direct estimate for a lower canonical corner c at 0<t<pi/2 in a hull with projection [x_-,x_+] contained in 0<=y<=1:

\[
\begin{aligned}
x_+-c_x&\geq\frac{1-(1-c_y)\sin t}{\cos t},\\
c_x-x_-&\geq\frac{1-(1-c_y)\cos t}{\sin t}.
\end{aligned}
\]

If c_y>=0, its abscissa is strictly inside the projection, with respective margins tan((pi/2-t)/2) and tan(t/2). If its abscissa is at or beyond a projection endpoint, then c_y<0: the entire quadrant misses the incoming strip. Reflection gives the upper-turn version above y=1.

Thus such a source corner is strictly inactive and cannot obstruct the previous singular-curvature improvements when their outer-clearance hypothesis holds. Corollary 122 removes the projection-endpoint item left unnecessarily in Theorem 117.

The residual singular-continuous curvature in that theorem's floating active regime is now localized, up to the previously specified null sets, to:

- outer points that are themselves canonical inner corners;
- actual collapsed source-corner fibers without an oblique touching affine ceiling.

**These two remaining sets are not proved null.** Hidden edge atoms and the sharp bound on the absolutely continuous density remain separate unresolved issues. The source-corner estimate must not be confused with a proof that every outer/inner corner coincidence is harmless.

## 57.3 Previous global contact and improvement results retained

### Width-one outer/inner coincidence

Theorem 109 in Note 59 shows that the nonatomic curvature restricted to width-one directions is dominated by dt. Theorem 110 in Note 60 identifies regular single-inner-wall outer contacts with such directions. Atoms are deliberately excluded from that assertion; the unit square refutes including them. Outside the width-one set, the remaining diffuse outer coincidence is an actual canonical corner, not an arbitrary wall contact.

### Actual singular-curvature improvements

Theorems 105 and 107 in Notes 56 and 58 replace a short support interval by the solution of f_c''+f_c=1 with matching endpoint values. Positivity of the Green kernel and convex gluing apply directly to nonsmooth supports.

For a clear exposed-edge atom, the retained added area is at least c epsilon and the possible old-body loss is O(epsilon squared). At a clear nonatomic singular-density point, good radii give

\[
|S_c|-|S|\geq c m(r)^2r-Cm(r)r^2>0,
\qquad m(r)/r\to\infty.
\]

These are genuine feasible improvements under their stated clearance conditions. They do not assume candidate proximity or full endpoints. The replacements can create endpoint atoms and are not advertised as repairing the whole hull at once.

Note 61 shows that a strictly inactive source corner removes the fiber-gap requirement altogether. Note 63 proves roof continuity, so a positive gap at an interior source coordinate supplies the neighborhood gap needed by the replacement. Note 65 now handles source coordinates at projection endpoints by a strict vertical-inactivity estimate.

### Oblique pinching contacts

Theorem 114 in Note 62 bounds source curvature at an affine-ceiling pinch with -cot(t)<k<tan(t). For the nonnegative clearance H_ell=ell(c_x)-c_y,

\[
H_\ell''=A_k\sigma_f+B_k\sigma_g+b_kdt,
\qquad A_k<0,\quad B_k<0.
\]

Taking an infimum over a uniform family of ceilings before applying level-set locality gives absolute continuity on the zero-contact set, with a chart-dependent density bound. A countable chart cover is used. This is not the sharp density bound one, and it does not include parallel or corner/corner pinches.

## 57.4 Finite optimality still has constraint terms

Notes 52–55 provide the uniform inner radius, mesh-independent support-variation estimate, finite polyhedral contact charts, area-derivative bounds, and an admissible inward saturation with controlled first-order cost.

On an incident feasible chart the selected maximum satisfies

\[
\nabla F_n=\kappa_n r_n-\sum_j\mu_{n,j}\nabla c_{n,j}+E_n^T\lambda_n,
\qquad\mu_{n,j}\geq0.
\]

Only the selection penalty is known to vanish. The contact-constraint terms are not removed by their bounded normal work. The finite pinching counterexample in Note 53 still defeats that formal inference. Artificial chart walls and physical constraints must also be distinguished, using every incident admissible chart.

The new width gate does not make a previously inadmissible variation admissible. It changes the logical target: derive the two support conditions, then obtain full endpoints as a consequence, rather than separately solving an endpoint-angle problem first.

## 57.5 The exact remaining route to closure

Attainment and selection of an arbitrary prescribed maximizing hull are available in the earlier notes. Corollary 123 now reduces the sufficient structural conclusion to:

1. curvature-measure domination on every open quarter, including elimination/control of the residual singular contacts and atoms and the sharp density bound;
2. both contact-order inequalities in the same unit-span normalization.

A proof of these conditions for one attained maximizer identifies the optimal value M. A proof for every maximizer, or an equality-preserving comparison, gives exact uniqueness. Full turns then follow from Note 64 and are no longer an independent hypothesis in this sufficient route.

The two conditions themselves remain substantial unproved claims. Neither the local repair theorems, the measure-localization statements, the non-sharp global bound, nor vanishing selection penalties have been substituted for them. The unrestricted proof is not a completed argument awaiting compilation.

## 57.6 Audit in this pass

**Core use:** the sharp functional and its equality theorem were read together with the weak-profile argument. The new implication uses Theorem 65 as an existing written result; this pass does not claim independent verification of every prior lemma.

**Width argument:** the central symmetral preserves widths exactly. The reflection identity for the contact expression includes its derivative signs and the affine sine term. The moment estimate uses the actual vertical displacements rather than merely bounding each horizontal displacement by one. Rightmost upper and lower traces are kept distinct, so allowed axis atoms are not silently discarded. The rectangle lies in the auxiliary body, not necessarily the original hull.

**Endpoint interpretation:** the new argument excludes partial endpoints only after the canonical reduction and the two-strip bound place them above pi/4. It does not claim all arbitrary convex bodies have this width gate.

**Source corners:** both support estimates are inequalities over the containing rectangle. No differentiability or particular support maximizer is needed. Strictly inactive source quadrants stay outside the strip under the small circular replacements. This removes that residual case without treating corner-to-corner coincidences elsewhere as resolved.

## 57.7 Execution

All changes are Markdown under docs/ambidextrous. Every commit includes `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was used. The existing manuscript, Lean sources, dependencies, and workflow definitions are unchanged. The PR remains open and draft, with no merge or unrestricted-completion claim.
