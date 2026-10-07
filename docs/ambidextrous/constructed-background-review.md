# Review: constructive tail backgrounds, finite strip admission, and an actual-body negative test

**Both unrestricted frontiers remain open.** This continuation constructs a sharp tail background for an explicitly testable subclass, gives a finite sufficient strip criterion for completing partial turns, and derives necessary parallel-volume bounds for actual maximizers. The entire convex-template rounding family is then ruled out as a universal local-improvement mechanism near the reference. None of these statements is promoted to a solution of either unrestricted problem.

Baseline: `9307910d73167a19f92c1785433aa27febacd375`. All changes are under docs/ambidextrous. The new proofs are written and self-reviewed, not independently refereed or kernel-verified. No earlier mathematical dependency has been verified merely by reading its file or running the new arithmetic checker.

## 1. What the constructive background does accomplish

[CB](complementary-tail-background.md) begins with an input cap U, not an assumed background. It requires height one, a half-height rectangle and niche, width W>2, and curvature at most one outside two short intervals adjacent to the top normal. At the two outer cut normals, h must be differentiable and dominated on the respective tail by the half-curvature arc with the same starting value and derivative.

The last condition is an explicit smooth-fit barrier. It cannot be omitted: otherwise independently repairing a tail can introduce a positive curvature atom at its join with the unchanged middle. Such an atom would violate the asserted global upper curvature bound.

On each tail, the projective lower convex envelope of `(1/2-h)/cos(t-midpoint)` constructs the least half-curvature majorant. It gives a genuine convex background B with the same axis supports. The smooth-fit barrier proves the outer derivative joins agree. The top atom only increases. The crucial identity is

$$e=h_B-h_U\ge0,\qquad e(2\rho_B-1)=0.$$

Thus the background density may be less than one half where B agrees with U, but is exactly one half where it enlarges U. The old CT surplus is zero, not unjustifiably declared positive. This avoids HC's counterexample to dropping the lower-density condition for an unrelated preselected background.

The narrow-window bound in CB derives the tail contact signs, separation of the two inner-tail intervals, a positive common-face length for the individual background, and a half-height niche. They are not additional unproved assertions about the constructed B. Monotone change of variables remains valid if its outer tangency has flat abscissa intervals: those intervals and their images contribute zero to the relevant area integrals.

The single-cap conclusion is

$$\Psi(B)-\Psi(U)\ge\int_a^b(1-A_U(x))dx,$$

where [a,b] is the constructed B's top face. For two inputs, if the two constructed face intervals agree, those budgets pay cross-clipping and give actual envelope area at most M using SR/AF on the regular backgrounds.

**The remaining admission requirements are real.** A general competitor can have a middle curvature atom, fail the smooth-fit barrier, lack the half-height geometry, or produce two different output faces. No automatic matching of those face intervals is proved. No original partial-turn body is silently enclosed by the full envelope. CB therefore replaces an existence assumption by a construction on its domain, not on the entire global domain.

## 2. Finite strip tests and their exact limits

[FS](finite-strip-bridge-criterion.md) uses support subadditivity to bound all widths between two normals a,b by

$$\frac{A\sin(b-\theta)+B\sin(\theta-a)}{\sin(b-a)}$$

when w(a)<=A and w(b)<=B. With c=cos(b-a), s=sin(b-a)>0 and A,B<=1, its maximum is at most one exactly when an endpoint-maximum case or the interior-maximum inequality holds:

$$B\le Ac\quad\text{or}\quad A\le Bc\quad\text{or}\quad A^2+B^2-2cAB\le s^2.$$

A finite chain passing these tests certifies the whole SI strip bridge, so the same body obtains both full turns without area change. A particularly simple condition is

$$w((\alpha+\pi-\gamma)/2)\le\cos((\pi-\alpha-\gamma)/2).$$

This supplies a checkable completion test, not an assertion that all competitive partial-turn bodies have the required width slack. Two unit endpoint widths never certify a nonzero interval by this test alone. In fact a width-one disk passes every true strip condition but its constant width-one data fail the two-strip interpolation criterion on every nonzero short interval. This low-area example is not a competitive counterexample; it makes clear that failure of FS is not failure of an actual bridge, and refinement is not guaranteed to make these sufficient tests complete.

The unsafe-width-bump case for actual competitive bodies is still unresolved. Full-turn completion also does not, by itself, imply the background hypotheses or an area bound.

## 3. A new necessary condition on actual maximizers

[PV](actual-maximizer-parallel-volume.md) works directly on an actual feasible set S, with its original full or partial motions. For every compact convex C of diameter at most one, `(S+tC)/(1+t)` preserves all those motions by a pointwise depth inequality. At an attained unrestricted maximizer, or an attained full-turn maximizer, this gives

$$|S+tC|\le(1+t)^2|S|.$$

In particular `|S+rD|<=(1+2r)^2|S|` for the unit disk D. Applying compactly supported maps `x -> x+rX(x)` and the exact planar determinant expansion proves that S is a set of finite distributional perimeter and

$$P(S)\le4|S|.$$

This is actual-body regularity, not a hull curvature estimate. It neither identifies all topological boundary points with reduced-boundary points nor supplies the background construction globally. For classical piecewise smooth bodies the anisotropic first variations give the further necessary conditions `P_C(S)<=2|S|`.

## 4. That variation family does not identify the optimum

[RT](convex-template-rounding-obstruction.md) bounds the actual reference perimeter from its explicit circular tangencies and central corner arc, retaining the distinction from finite staircase source length. It proves

$$4M-P(\Sigma)>92/2625.$$

The reference's even normal measure then bounds every diameter-one convex template at once:

$$P_C(\Sigma)\le P(\Sigma)/2.$$

Thus

$$\left.\frac{d}{dt}\left|(\Sigma+tC)/(1+t)\right|\right|_{0+}<-46/2625.$$

This is a uniform bound on the derivative coefficient, not a claimed uniform finite step size or a theorem excluding all larger finite steps. For the prescribed small asymmetric double-tip cuts, the removed and new boundary lengths tend to zero, so the same family still has strictly negative first-order coefficients uniformly in C. Those bodies are known to be suboptimal. Therefore PV's necessary first-order conditions cannot be treated as sufficient optimality conditions or as an automatic improving operation on the remaining cut examples.

The proof is analytic and does not use an assumed sharp ambidextrous optimum. More selective body deformations remain possible; only this particular entire family has been pruned.

## 5. Exact checks actually executed

The standard-library script [check_constructed_background.py](computer-assisted/check_constructed_background.py) ran under an external five-second limit in approximately 0.0216 seconds internally. It has 44 named check calls, some repeated for different input values. They include 45 depth instances, 24 determinant identities, five window guards, five complementary cases, 125 rational two-strip cases with 1,625 intermediate-angle checks, and three negative controls.

The [record](computer-assisted/constructed-background-checks.json) states that continuum background admission, arbitrary partial-turn completion and unrestricted optimality are not verified by the script. Executed bytes match Git blob `41d3aaef44a80b656f39b5bcb3aee2d24d79c9dd` and SHA-256 `69935151a2823dbbe93fa11b26f39ed6d49d22021be8af2ce91d115f8a21ce8d`.

The finite tests are supplementary to the displayed hand proofs. In particular they do not verify the convex-envelope regularity theorem or the complete historical SR/AF and motion chains.

## 6. Bounded exploratory work, including unresolved directions

The complete sources and outputs are retained in the session bundle. Each primary invocation was capped at five seconds; none used an optimizer or an adaptive refinement campaign.

- `probe_rounding.py` sampled the explicit reference boundary at two prescribed resolutions and tested a disk, seven segment directions and seven equilateral-triangle directions. All first-order values were negative; runtime was about 0.0063 seconds. RT replaces that sampled observation by the hand bound for all templates.
- `probe_partial_cuts.py` tested eight prescribed affine cut hulls. None exhibited a positive sampled intermediate width bump. Its nominal reference envelope area was about 1.645225, already above the exact reference value because of finite-angle/spatial approximation. Small apparent partial-versus-full gains are therefore not certified gains. Runtime was about 0.317 seconds, plus a short imported reference setup. No global bridge theorem or feasible body above M was inferred.
- `probe_regular_average.py` tested seven prescribed circular-flank regular-cap pairs, and `probe_regular_average_general.py` tested twelve prescribed piecewise-curvature pairs. The tentative inequality `area(E(U,V))<=2 Psi((U+V)/2)` had no sampled violation. Two cases in the second run had negative surviving fibers and are not admissible two-turn bodies. The respective runtimes were about 0.365 and 0.562 seconds. There is no certified error direction, and absence of a violation is not a theorem. MCA already refutes a broader cap-averaging enclosure on rough inputs; none of these tests rescinds that negative result.

Restricted regular-background averaging is recorded only as an unproved possible direction. Even proving that restricted comparison would still need a valid rough-input admission and clipping transfer. No averaging identity is used in CB or FS.

## 7. Final boundary of this continuation

The full-turn construction remains conditional on regular middles, half-height geometry, smooth fit and matching output faces. The partial-turn result remains conditional on actual intermediate width slack. PV/RT show why one broad family of feasible perturbations does not remove those missing hypotheses.

Thus neither the unrestricted full-turn upper bound nor the uncovered partial-turn comparison has been closed. The prior weighted value and admitted case theorems remain written inputs with their existing qualifications. These new results do not warrant a numerical percentage or a claim that completion is imminent.

All substantive findings were committed with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation, manuscript build, long search or background execution was used. PR #3 remains open and draft.
