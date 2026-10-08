# 51. Current status: an explicit unrestricted bound and a singular-curvature local theorem

**The unrestricted optimality and uniqueness problem is not closed.** This is the current ledger. Notes 7, 24, 34, and 43 are historical status snapshots. The new work proves an explicit bound applying to every competitor and extends the protected local comparison to arbitrary curvature measures.

All proofs are written and self-reviewed, not independently refereed or Lean-verified. No novelty or best-known-bound claim is made. The elementary bounds here do not depend on a claimed solution of the remaining structural theorem.

## 51.1 New unrestricted result

[Theorem 89](46-explicit-unrestricted-gap.md) proves, for every compact connected ambidextrous body in the posed problem,

\[
\boxed{|S|<2\sqrt2-1-\frac1{20000}.}
\]

Thus, for the attained unrestricted maximum V from Note 25,

\[
M\leq V<2\sqrt2-1-\frac1{20000}.
\]

The strict assertion for V uses attainment; the per-body bound and the corresponding non-strict supremum bound do not need it.

The proof has three independently checkable stages:

1. [Note 44](44-diagonal-global-upper-bound.md) exactly solves the incoming-strip/two-diagonal-position relaxation. In diagonal coordinates it is a rectangle with opposite corner rectangles removed. A three-rectangle decomposition gives area at most 2sqrt(2)-1. If both outer extents exceed two, connectedness confines the body to a single unit square instead; the disconnected union is not counted as a body.
2. [Note 45](45-diagonal-equality-is-not-a-sofa.md) identifies the relaxation's unique equality envelope and excludes it at a further required angle by a three-point support test.
3. [Note 46](46-explicit-unrestricted-gap.md) proves a quantitative placement estimate for near equality. Three explicit squares, each of area 1/16384, lie inside every sufficiently near-equality envelope. A body missing area at most 1/20000 must meet all three. Any three such points violate a unit hallway at one of the required angles arctan(3/4), arctan(4/3).

This is a finite analytic certificate, not a numerical evaluation of the finite-angle optimization values. It assumes neither full-quarter endpoints nor any curvature/contact regularity. The previously proved angle reduction and the elementary two-strip bound justify visiting the required finite angles for a body large enough to contradict the displayed constant.

The constant is deliberately conservative and does not equal M. Solving this relaxation does not solve the moving problem.

## 51.2 New local result: singular measures are now allowed

[Theorem 92](48-singular-protected-optimality.md) strengthens Theorem 83. Its inputs are arbitrary convex support functions uniformly close to h_* and equal to h_* outside fixed protected angular windows. The windows remain away from the axis normals and switching neighborhoods. The four quarters may be changed independently.

There is no input C², H², C¹-smallness, absolute-continuity, or upper-curvature hypothesis. Uniform support distance plus convexity controls both derivative traces on compact interior windows. The input can have exposed-edge atoms or singular-continuous curvature.

The actual feasible envelope has area at most M, with equality only for the candidate. The proof uses the following measure-level chain:

```text
uniformly close convex support, with protected angular support
  -> semiconvex derivative-trace control
  -> a semiconcave wall obstacle
  -> a C¹,¹ greatest convex minorant
  -> repaired support curvature between zero and one as a measure
  -> verified two-wall roof and strictly positive actual area gain
  -> the existing sharp theorem for the repaired hull
```

The measure identity underlying the gain is

\[
\int u\,d\sigma_f=\int u+\int u'^2-\int u^2,
\]

where u is the nonnegative repair increment. It includes all singular curvature mass. On a middle window the actual gain is still integral (1-q-u)u plus one half of integral u'^2; the other wall and side-only formulas retain their respective signs.

The unchanged axis neighborhoods preserve a unit-height rectangle of width greater than one. Hence any competitive body with one of these hulls is forced to use full endpoints by the existing width gate. The local result therefore also bounds such bodies when their original motions were not specified as full turns.

This is **not** unrestricted Hausdorff-local optimality. The exact agreement outside the protected windows is a substantive condition. Nor has every global maximizer been put into this neighborhood.

## 51.3 New examples and a negative approximation result

[Note 49](49-atomic-and-cantor-examples.md) constructs actual feasible bodies with:

- a non-axis edge atom of mass 2epsilon, created by a cutoff multiple of |sin(t-t_0)|;
- singular-continuous curvature, created by a moment-matched Cantor measure and a smooth compensating density.

Both types keep the candidate's exposed faces and can preserve strict contact order. Their areas tend to M from below. Their strict deficits are proved by the measure repair, not estimated numerically. They rule out high-area feasibility as a substitute for a maximizer-specific singular-curvature argument.

[Theorem 94](50-curvature-domination-is-not-dense.md) proves that curvature domination by dt on an open quarter is closed in uniform support distance. A violating hull has the explicit separating estimate

\[
\|h-k\|_\infty\geq
\frac{\int\phi\,d\sigma_h-\int\phi}
{\|\phi+\phi''\|_1}
\]

for an appropriate nonnegative compactly supported test phi and every dominated k. An interior atom of mass m gives a lower bound m²/80 under the stated window-size condition.

Thus general smoothing/density cannot impose the missing curvature cap while staying arbitrarily close to a fixed violating hull. The improving repair changes the hull by a nonzero amount; it is not contradicted by this closedness result.

## 51.4 Existing results still in use

The strongest sharp global theorem on a specified class remains Theorem 65: full canonical quarter turns, curvature-measure domination on open quarters, and the two contact inequalities imply area at most M and exact uniqueness. The adaptive functional's maximum and equality kernel remain the algebraic ingredients.

The earlier unrestricted reductions, attainment, connected niche separation, effective selection of every maximizing hull, quantitative finite-angle completion, and feasible rounding/perimeter estimates remain available. Notes 35–37 remain a regular critical-point calculation, not an unrestricted measure theorem. Notes 40–42 are now extended to singular protected inputs by Notes 47–48.

The frozen-switch counterexample, raw-partition nonconcavity example, and earlier signed-area and visible-edge obstructions remain valid. No failed route has been reclassified as a global proof.

## 51.5 What still prevents identification of V with M

The new unrestricted constant does not localize every maximizer near h_*. The new measure repair works in a specified local contact neighborhood, not across arbitrary switching/axis changes, clipping, or partial endpoints. These two results cannot simply be combined by omitting those distinctions.

To apply Theorem 65 to the unrestricted optimum, the remaining argument must still establish or replace:

- full-quarter endpoints for relevant maximizers;
- curvature-measure domination, including singular and contact-degenerate configurations outside the protected neighborhood;
- both contact-order inequalities, using admissible variations and controlled errors in the selected finite-angle limit.

A structural proof for one maximizer would give V=M. Exact uniqueness needs it for every maximizer or an equality-preserving comparison that recovers each original body. Attainment and arbitrary-maximizer selection are already proved, but they do not themselves supply the structural inequalities.

## 51.6 Self-review of this pass

**Finite relaxation:** the diagonal transformation is orthonormal; the incoming strip has u+v width sqrt(2), not width one. Removed corner rectangles and the central bridge are decomposed with the correct inequalities. Connectedness is used only where two positive-separated components occur. Equality is proved for the finite relaxation, then separately tested against another angle.

**Quantitative gap:** individual rectangle losses control both outer extents and strip-center displacement. The three square areas exceed the maximum allowed missing area. The witness inequalities use points of the body to lower-bound supports, not an unjustified claim that every chosen witness is a support maximizer. Both possible diagonal-axis orderings correspond to angles actually visited by the same lower-turn witness.

**Measure repair:** transformed curvature is treated as a pushed-forward signed measure. A contact between a semiconcave obstacle and its convex minorant forces equal one-sided slopes, excluding derivative jumps there. The repaired curvature bound is obtained as a measure statement. The hull-area expansion retains the singular measure pairing, and the actual two-wall roof is checked independently of the one-wall conjugacy identity.

**Examples and closure:** moment cancellation makes the singular-continuous perturbation vanish with its derivative near the window endpoints. The density compensation is taken only where the reference curvature has a positive margin. The closedness obstruction is proved by distributional tests, not by an informal claim about mollification.

## 51.7 Execution and provenance

Only Markdown under docs/ambidextrous was changed. Every research commit includes `[skip ci]`. No CI was requested or used, and no Lean/Lake compilation was attempted. No dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Repository review used source contents and PR discussion, not workflow results.

The finite-angle viewpoint is consistent with the classical hallway-intersection approach; the candidate and sharp functional program remain attributed to Romik's construction, Baek's method, and this repository's uniqueness work. This pass does not claim a comprehensive literature or priority audit. The PR remains open and draft because unrestricted closure and independent proof review are unfinished.
