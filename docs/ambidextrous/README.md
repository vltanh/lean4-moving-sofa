# Ambidextrous sofa research

**The width-at-most-two exclusion now has a stronger pen-and-paper proof. The unrestricted optimality and uniqueness proof remains open.** The new ordinary-area bound is 41/25, replacing the previous computer-assisted bound 411/250 for the width gate.

Start with **[Theorem AW-W: analytic width exclusion](analytic-width-theorem.md)**. Its two ingredients are the [loss partition and mixed-area inequality](analytic-width-loss-partition.md) and the [analytic localization lemma](analytic-width-localization.md). The [review](analytic-width-review.md) records the dependency checks, corrections, and the distinction between discovery and proof.

These are written, self-reviewed arguments, not independently refereed or Lean-verified results. No novelty or best-known-bound claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Original base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`; the base branch has since advanced. The existing manuscript, Lean sources, dependencies and workflow definitions are unchanged.

## The analytic replacement

Let S be a compact connected ambidextrous body in a common incoming orientation, contained in a unit-height strip, and let W be its horizontal width. Theorem AW-W proves

$$
\boxed{W\leq2\quad\Longrightarrow\quad |S|<41/25=1.64<411/250<M_A,}
$$

where

$$
M_A=1+4Y^2+\arctan Y,
\qquad4Y^3+3Y-1=0,\quad Y>0.
$$

The proof does not assume curvature bounds, symmetry, contact order, full-quarter endpoints, or enclosure by the adaptive functional. It even permits incoming vertical span smaller than one.

### How the search tree disappears

Use the complementary orientations with cosine/sine pairs

$$
(\sqrt{3/5},\sqrt{2/5}),\qquad
(\sqrt{2/5},\sqrt{3/5}).
$$

A body of area greater than 8/5 must visit both angles for both turns, by the endpoint two-strip bound. Both motions keep independent placements.

Partition the 2-by-1 rectangle into two outside horizontal bands and a middle band. Count lower-turn outer-wall loss only in the upper half of the outside bands and lower-turn inner-niche loss only in the lower half of the middle band. Count the reflected upper-turn losses in the opposite halves. These counted regions are disjoint, even when the relaxed envelope has empty fibers.

For each pair of lower-turn hallways, an analytic localization lemma shows that loss at most 9/50 would force all three types of loss triangles into their assigned regions. Its proof uses one convex two-variable lower bound, four explicitly minimized boundary quadratics, and concavity in the far parameter tails. No parameter-box enumeration is retained.

The two differently sloped inner triangles satisfy the universal mixed-area estimate

$$
|\Delta_1\cup\Delta_2|\geq\frac6{11}(|\Delta_1|+|\Delta_2|).
$$

It follows from planar Brunn--Minkowski through mixed-area monotonicity and the exact normalized mixed area 6/5. The resulting convex loss surrogate reduces to two variables and has global minimum

$$
\frac{6\sqrt6}{109}\left(2-\frac{c+s-1}{cs}\right)^2
>\frac9{50}.
$$

Thus each independent turn removes more than 9/50 in the counted regions, giving ordinary area less than 2-18/50=41/25.

The averaging step concerns the convex surrogate, not physical symmetrization of a sofa. The triangle containment is proved before whole-triangle areas are used. A separate [exact diagonal example](analytic-width-diagonal-obstruction.md) explains why the two diagonal positions alone would be insufficient.

## What is and is not computational now

The proof of AW-W needs no Python, certificate bytes, replay, interval search, generated list, or rational matrix certificate. All directions, scalar functions, derivatives and rational inequalities are displayed in the mathematical notes. Standard planar Brunn--Minkowski is its only non-elementary classical input.

Local exploratory numerical evaluations helped select the partition and angle pair; scratch arithmetic checked the scalar fractions. Those are part of discovery, not proof dependencies. The [review](analytic-width-review.md) states this explicitly rather than claiming that no computer was involved in discovering the argument.

The old [computer-assisted covering](computer-assisted/README.md), its [theory](computer-assisted/THEORY.md), and [recorded result](computer-assisted/RESULT.json) are retained for provenance. They were not rerun in this analytic pass. Their 1.644 bound is superseded by the analytic 1.64 bound, not retracted. The old directions and certificate do not enter the new theorem.

## Remaining closure roadmap

The earlier reductions give an attained global maximum and a common incoming unit-span representative of every competitive body. AW-W now supplies, without computer assistance, **W>2 for every global maximizer**.

The existing [wide curvature theorem CW4](curvature-only-wide-hulls.md) states that a unit-span ambidextrous common hull with W>=2 and

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on all four open coordinate quarters}
$$

has area at most M_A, with equality exactly for Romik's candidate up to congruence. It does not separately assume contact order, full turns, or aligned horizontal faces.

The remaining sufficient route is therefore:

```text
an arbitrary attained global maximizer
  -> common incoming unit-span normalization
  -> W > 2                              [AW-W, analytic]
  -> curvature domination or a valid sharp comparison
                                          [NOT PROVED]
  -> CW4 and exact equality recovery
  -> unrestricted optimality and uniqueness
```

The new width proof does not establish that curvature statement. Obstructed outer/inner-corner contacts, hidden or coincident edge atoms, and the sharp absolutely continuous density bound remain unresolved. A comparison for one attained maximizer determines the value; uniqueness requires every maximizer or an equality-preserving recovery.

## The ordinary-area issue remains separate

[AF3](adaptive-functional-global-calibration.md) bounds the auxiliary functional on every normalized real H^1 profile of width at least one and identifies its equality kernel. For an actual hull h, however,

$$
M_A-|S|=[M_A-\widetilde{\mathcal Q}(h)]
       -[|S|-\widetilde{\mathcal Q}(h)].
$$

The second bracket can be positive. [AF4](adaptive-functional-enclosure-counterexample.md) proves this near the candidate; [the narrow convex example](narrow-curvature-enclosure-counterexample.md) records a different clipping error. AW-W excludes narrow bodies by direct ordinary-area losses; it does not turn those false enclosure statements into true ones.

The coupled repair and singular-contact arguments retain their stated admissibility hypotheses. Vanishing selection penalties do not eliminate contact normal-cone terms. This branch is not a completed unrestricted proof merely awaiting compilation.

## Earlier work and reading map

| Source | Role |
|---|---|
| [AW-W](analytic-width-theorem.md) | Stronger analytic width exclusion and the actual-angle reduction. |
| [LP1–LP2](analytic-width-loss-partition.md) | Disjoint losses, independent motions, and the mixed-area triangle estimate. |
| [AL1](analytic-width-localization.md) | Global parameter localization with four rational boundary checks. |
| [Analytic review](analytic-width-review.md) | Audit, discovery disclosure, and precise proof dependencies. |
| [Historical computer certificate](computer-assisted/README.md) | Preserved algorithms, hashes, execution record and reproduction instructions. |
| [CW4](curvature-only-wide-hulls.md) | Sharp geometric theorem after the missing global curvature reduction. |
| [AF3](adaptive-functional-global-calibration.md), [AF4](adaptive-functional-enclosure-counterexample.md) | Auxiliary calibration and failure of universal ordinary-area enclosure. |
| [PR #8 audit](stability-pr8-transfer-audit.md), [width deficit](stability-width-gap-certificate.md), [error absorption](stability-error-absorption-check.md) | Scope of Gerver-stability transfer and quantitative deficit tools. |
| [Signed roof](curvature-only-signed-roof.md), [coupled repair](ordinary-area-repair-coercivity.md), [ordered faces](narrow-separated-face-area-bound.md) | Earlier geometric comparisons with explicit hypotheses. |
| [Notes 1–24](24-current-proof-ledger.md), [25–51](51-current-proof-status.md), [52–67](57-focused-structural-status.md) | Historical foundations, partial reductions, contact analysis and negative findings. |

The earlier foundations include canonicalization, unit-span normalization, correct turning signs, connected niche separation, a bounding box, attainment and selection of any prescribed maximizing hull. The analytic width proof does not require an audit or import of the full later functional chain.

## Execution and provenance

Only Markdown changed in this continuation. No CI, Lean/Lake compilation, dependency installation, or manuscript build was used. Every commit includes `[skip ci]`. Existing computer-assisted code and recorded results remain untouched; their README points to the new analytic theorem.

The finite-position approach follows the tradition of Kallus and Romik, [*Improved upper bounds in the moving sofa problem*](https://arxiv.org/html/1706.06630v2). The candidate is Romik's [explicit construction](https://arxiv.org/html/1606.08111v3). Baek's sharp-majorant approach, the repository's uniqueness manuscript, and the inspected PR #8 notes motivate the broader program. No priority or best-known-bound claim is made. PR #3 remains open and draft because unrestricted closure and independent review are unfinished.
