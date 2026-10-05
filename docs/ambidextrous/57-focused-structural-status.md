# 57. Focused structural status through Notes 59–63

**The unrestricted proof is not closed.** The current continuation stays on the global contact/variation bottleneck. It does not improve the coarse numerical bound or enlarge only the protected-candidate neighborhood. Its new results classify diffuse outer contacts, remove inactive-corner obstructions, and establish a measure bound at oblique pinches.

This remains the research-entry ledger rather than adding another numbered status file. Note 51 is the preceding full inventory. All results are written proofs with self-review, not independent verification. The entire earlier proof chain has not been independently audited in this pass.

## 57.1 New global contact-measure results

### Width-one coincidence needs no new diffuse-curvature proof

[Theorem 109](59-width-level-curvature.md) proves, for every convex hull, that the nonatomic part of its curvature measure obeys

\[
\sigma_{K,\mathrm{na}}|_{\{w_K=1\}}\leq dt|_{\{w_K=1\}}.
\]

The proof is a direct Stieltjes-measure localization on a level set of the width function. It neither assumes maximality nor differentiates curvature as if it were a function. Atoms are deliberately excluded from this assertion: the unit square is an explicit counterexample to including them.

[Theorem 110](60-classifying-outer-contact-obstructions.md) identifies why this matters. At almost every nonatomic-curvature normal, an outer boundary point touching a single inner wall must have width one in that normal. Outside the width-one set, a coincident outer contact must instead be an actual canonical inner corner. Such a blocking corner uses support normals separated from the normal of the touched outer point.

This narrows the obstruction; it does not prove that the corner-coincidence set has zero curvature measure.

### A pinch unrelated to the changed corner is not an obstruction

[Proposition 112 and Corollary 113](61-inactive-corners-do-not-obstruct-repair.md) weaken the clearance assumptions of the earlier singular repair. If the changed corner is strictly below the lowest surviving point at its abscissa, every old point of the body survives the short circular replacement. A fiber may be collapsed at another height; that does not matter. With the existing outer-clearance hypotheses, the added hull area then gives a genuine improvement without a positive fiber-gap assumption.

The proof keeps all partial terminal-angle constraints. A first draft's overbroad wording about endpoint quadrants was corrected: only the axis-angle quadrants are discarded above the incoming baseline, not a partial terminal angle.

### Oblique affine-ceiling pinches cannot carry singular source curvature

[Theorem 114](62-oblique-pinch-measure-bound.md) concerns a lower canonical corner meeting a local affine ceiling ell(x)=a+kx for the body. At an oblique contact,

\[
-\cot t<k<\tan t.
\]

Let H_ell(t)=ell(c_x(t))-c_y(t), which is nonnegative by connected feasibility. Its distributional second derivative retains both source curvature measures:

\[
H_\ell''=A_k\sigma_f+B_k\sigma_g+b_k(t)\,dt,
\quad A_k=k\cos t-\sin t<0,\quad B_k=-k\sin t-\cos t<0.
\]

On a uniform contact chart, take the infimum over the whole family of valid ceilings. A common semiconcavity estimate gives, on its zero set Z,

\[
(\sigma_f+\sigma_g)|_Z\leq(C/\eta)\,dt|_Z.
\]

A countable chart cover excludes atoms and singular-continuous curvature from these contacts without an invalid uncountable union of null sets. The bound is not the sharp density cap one.

The ceiling can be an opposite-motion single wall or an upper supporting line of the hull. Parallel inner/inner coincidence has width **two**, not width one; the strict two-coefficient argument does not extend to that limit. Corner/corner pinches need not admit a touching affine ceiling and remain distinct.

### Roof continuity makes the remaining fiber condition pointwise

[Lemma 115](63-roof-continuity-and-singular-residual.md) proves continuous clipped niche roofs without input smoothness. Nearly axis-parallel constraints have uniformly small positive height; truncating them gives Lipschitz roofs converging uniformly. The proof also gives a local one-half Holder modulus.

Consequently surviving fiber endpoints are continuous on the projection interior. A positive gap at one point supplies the neighborhood clearance used in Note 58. Compactness alone would not imply this; a simple cross-shaped compact set records that failed inference.

[Theorem 117](63-roof-continuity-and-singular-residual.md) assembles the results: for a maximizing hull, remaining singular-continuous curvature at floating active normals is localized, up to a null set, to

- outer points that are themselves canonical inner corners;
- source corners whose abscissae are projection endpoints;
- actual collapsed source-corner fibers without an oblique touching affine ceiling.

These residual classes have **not** been proved null. The theorem localizes the problem rather than claiming global absolute continuity.

## 57.2 Earlier maximizer-specific improvements retained

[Theorem 105](56-atomic-improvement-away-from-obstructions.md) excludes an exposed-edge atom when a compact edge subsegment is strictly clear of both sweeps and the corresponding corner band has the stated clearance. It uses a convex outward solution of f_c''+f_c=1 on a short interval: retained added area is at least c epsilon and old-area loss is O(epsilon squared).

[Theorem 107](58-singular-curvature-away-from-obstructions.md) excludes nonatomic singular-density points under its outer/fiber conditions. At good scales, with central curvature mass m(r),

\[
|S_c|-|S|\geq c m(r)^2r-Cm(r)r^2>0,
\qquad m(r)/r\longrightarrow\infty.
\]

Notes 61–63 now remove false inactive-corner obstructions, prove pointwise-to-uniform fiber clearance, and exclude the oblique pinching class. Masked edge atoms and the remaining corner configurations are not eliminated.

These are actual feasible area improvements at general bodies, not stationary equations with unproved variations. The replacements can create endpoint atoms and are not described as repairing the entire hull at once.

## 57.3 Finite variations and their nonvanishing constraints

Notes 52–55 continue to provide a uniform inner radius, mesh-independent Hausdorff support-variation control, finite polyhedral contact charts with quadratic area, a uniform interior-window area-derivative bound, and an admissible inward saturation with controlled first-order cost.

On an incident feasible chart the selected maximum satisfies

\[
\nabla F_n=\kappa_n r_n-\sum_j\mu_{n,j}\nabla c_{n,j}+E_n^T\lambda_n,
\qquad\mu_{n,j}\geq0.
\]

The selection penalty tends to zero; the contact-constraint terms have not been shown to do so. Pairing the admissible inward direction gives only bounded normal work,

\[
\sum_j\mu_{n,j}Dc_{n,j}[v_n]\leq2|C_n|+\kappa_n R.
\]

Bounded work is not vanishing work. The finite pinching example from Note 53 remains a counterexample to deleting the normal terms on purely formal grounds. Artificial chart walls must also be distinguished from physical constraints; all incident admissible charts matter.

The new contact-measure theorems classify some geometry behind these terms. They do not assert that all multipliers vanish or that a bounded weak limit is absolutely continuous.

## 57.4 The sharp theorem and what is still missing

The existing [Theorem 65](31-closed-curvature-class-theorem.md) gives the exact candidate value and body uniqueness under full canonical quarter turns, curvature-measure domination on the open quarters, and the two contact-order inequalities. The explicit adaptive functional and its equality kernel remain the sharp part of that argument.

For unrestricted optimality, the unproved structural conclusions remain:

1. full-quarter endpoint angles, or an alternative sharp comparison for partial endpoints;
2. domination of the complete open-quarter curvature measure by dt, including remaining atoms/corner configurations and the sharp bound on absolutely continuous curvature;
3. both contact-order inequalities.

A structural theorem for one attained maximizer would settle the value. The corresponding result for every maximizer, or an equality-preserving comparison, is needed for exact uniqueness. Arbitrary-hull selection preserves this logical distinction but does not prove the missing geometry.

The current progress does not justify calling the unrestricted proof nearly complete. It removes identifiable contact obstructions and states the remaining ones more precisely.

## 57.5 Audit of this continuation

**Level sets:** exceptional one-sided accumulation points are countable. Stieltjes restriction is proved on compact subsets before using inner regularity. Atoms are not silently included in the width-one bound.

**Outer contacts:** only extreme points are assumed to belong to S; the whole hull is not assumed to avoid a niche. The touched outer normal is distinguished from the two normals defining a blocking corner.

**Pinch measures:** all coefficients and signs are derived in distributions. Infima are taken over a uniform family before applying level-set locality, avoiding an uncountable-union error. A countable rational chart cover globalizes only the stated oblique contact class. Width-one outer/inner contact and width-two inner/inner contact are separate cases.

**Inactivity and continuity:** partial terminal constraints remain in the roof supremum. The axis truncation uses a height estimate despite unbounded individual slopes. Positive pointwise gap is promoted to neighborhood gap only after proving roof continuity. The repair's old-body containment is checked separately from its positive added-area gain.

**Dependencies:** the new elementary measure/contact lemmas have written proofs here. Their maximizer consequences additionally use the prior canonical reduction and singular-density repair. This is not an independent audit of every earlier theorem or a formal verification.

## 57.6 Execution

Every change is Markdown under docs/ambidextrous. All commits include `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was used. The PR remains open and draft, with no merge or unrestricted-completion claim.
