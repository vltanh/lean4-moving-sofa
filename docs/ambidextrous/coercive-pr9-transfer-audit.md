# PR #9 transfer: zero-deficit rigidity does not replace geometric enclosure

This audit is pinned to PR #9, branch `research/coercive-extremal-framework`, commit `5016a36b071e66f82a7de9e327f7a63a8fad1e8c`. The ambidextrous branch was read at `e20a4bc7d7aa6b3f6a722fcf682e1b4b065b6c39`. Later development in either branch is not automatically covered by this snapshot.

## 1. What the linked branch actually supplies

The inspected files are [ROADMAP.md](https://github.com/vltanh/lean4-moving-sofa/blob/5016a36b071e66f82a7de9e327f7a63a8fad1e8c/docs/coercive-extremal/ROADMAP.md), [DEPENDENCIES.md](https://github.com/vltanh/lean4-moving-sofa/blob/5016a36b071e66f82a7de9e327f7a63a8fad1e8c/docs/coercive-extremal/DEPENDENCIES.md), and its README. They explicitly describe planning and a dependency refactor, not a completed new Lean theorem. The PR's four changed files at this snapshot are documentation. No source or theorem from it is being merged, compiled, or treated as verified here.

The proposed Gerver route is

$$
K\text{ maximizing}\ \Longrightarrow\ K\in\mathcal K^i
\ \Longrightarrow\ \mathcal A(K)\leq Q(\xi_K)\leq M_G
\ \Longrightarrow\ d_H(K,K_G+(s,0))=0.
$$

The first implication uses already developed **one-turn maximizer geometry**. The last implication replaces the old CapKernel equality calculation by zero-deficit coercivity. These are separate jobs. In particular the route does not deduce membership in the geometric domain from a bound on the auxiliary functional alone.

The dependency document also forbids importing the global stability/qualitative-entry layer into the low coercivity layer: that entry currently uses uniqueness. This is the relevant noncircularity rule for the present problem too.

## 2. The corresponding ambidextrous proof obligation

Write M_A for Romik's area, and let Q_A denote the adaptive functional of AF3. That theorem already supplies

$$
Q_A(h)\leq M_A
$$

on its stated normalized H^1 domain, with a characterized equality set. It does **not** supply an ordinary-area comparison. For an actual body S and its hull h,

$$
M_A-|S|=[M_A-Q_A(h)]-[|S|-Q_A(h)].
$$

AF4 shows that the second bracket can be positive. AX1 and SAT1 show that the proposed corrected global-repair enclosure can fail even after full canonical saturation. SAC2 computes a positive actual deficit of order tau^(3/2) for that saturated family, while its hull derivative energy is of order tau. These failures are not repaired by changing the proof of zero-energy rigidity.

The one-turn implication `maximizing -> Ki` must therefore not be transplanted with the word "ambidextrous" substituted. Nor may near-optimal ambidextrous bodies be placed near Romik by using Gerver's already established uniqueness or by assuming the desired Romik uniqueness.

## 3. A precise transferable assembly rule

The following elementary rule records exactly when a coercive theorem would complete this problem. It is not a claimed construction of its missing inputs.

Suppose an area functional A on an admissible class attains its supremum and a candidate S_* is feasible with area M. Suppose that **every** maximizing S admits data xi such that

$$
A(S)\leq Q(\xi)\leq M,
$$

and that equality throughout implies S is congruent to S_*. Then S_* is optimal and all maximizers are congruent to it. Indeed, maximality gives A(S)>=M, so all the inequalities are equalities. A result for just one maximizing S proves the value but not uniqueness of all maximizers.

A distance estimate d(xi,xi_*)^2<=C(M-Q(xi)) can supply equality of the auxiliary data. Exact body equality is a further requirement: hull equality alone is insufficient for nonconvex bodies. Containment in the identified regular-closed candidate envelope and equal area is one valid recovery mechanism, as in Lemma 4.

For quantitative stability, the comparison must cover near-maximizers, and the distance to the original nonconvex body must also be controlled. None of those additional hypotheses follows just from a maximizer-only assembly.

## 4. What is pursued rather than re-proving the functional maximum

The user-requested proof target is the ordinary-area comparison, not another zero-deficit corollary. The latest anchor lemma AB1 supplies geometric information discarded by the earlier freely varying repair increments: the two reflected changes share the same original horizontal exposed points, so

$$
u+u^\rho\leq\sin t,\qquad v+v^\rho\leq\cos t.
$$

The proposed derivative-free budget AB.4 is a concrete alternative worth testing against these constraints and the exact near-axis counterexamples. It still requires two independent validations: a sharp analytic bound on a covering data domain, and a correct ordinary-area inequality. A successful first validation will not be reported as the second.

Any new computer calculation will be labelled as discovery, a falsifying example, or a complete certificate according to what was actually checked. A complete covering with unresolved boxes is not called complete, and sampled agreement is not a continuum theorem.

## 5. Execution and scope

No CI, Lean/Lake invocation, or manuscript build was performed for this audit. No changes were made to PR #9, the existing Lean libraries, or the manuscript. All continuation commits use `[skip ci]`. The earlier proof chain remains self-reviewed rather than independently verified. The unrestricted ambidextrous optimality and uniqueness theorem is not established by this transfer audit.
