# Active roadmap: geometric admission to the two-wing certificate

Baseline: `f6a06beae3bbdfaf6e15547a93eb765a0661463e` in PR #3. This is the active plan requested by the user. It supersedes informal progress percentages, not the historical mathematical findings. **Unrestricted optimality and uniqueness are not proved.** The existing two-wing arguments are written, self-reviewed results, not independently checked infrastructure.

The goal is an ordinary-area comparison for every relevant maximizing body, followed by a sharp bound with an equality case. A short final implication is not evidence that its missing hypotheses are easy.

## 1. The intended conclusion and quantifiers

For an arbitrary attained maximizer S, seek data xi with

$$
|S|\leq\mathcal W(\xi)\leq M,
$$

where M is the area of the feasible Romik candidate. Equality must identify S itself up to congruence, not just its convex hull or selected witnesses. A result for one attained maximizer establishes the optimal value; uniqueness requires every maximizer or a separate equality-preserving comparison.

No auxiliary bound is called an area theorem before its geometric comparison is proved. No candidate-neighborhood assumption is inferred from the desired optimality or uniqueness.

## 2. Critical-path gates

| Gate | Deliverable and acceptance criterion | Baseline status |
|---|---|---|
| R0: audit the current certificate | Recheck the exact two-wing quadratic, first variation, reference geometry and equality conditions from the written definitions. Any correction gets its own commit. | Written proofs exist in TW/WS/WC; independent verification pending. |
| R1: normalization and coverage | State the posed motion class, attainment input, common incoming strip and actual-hull saturation; retain containment needed for equality. | Earlier notes provide these reductions and 2<W<4 for competitive maximizers. They do not imply curvature domination. |
| R2: terminal angles | Either justify all angles used by the wing construction, or include an explicit ordinary-area correction for missing angles and terminal strips. | Open. Full turns cannot be inserted by convention. |
| R3: canonical wing construction | Define actual convex safe pieces from both witnesses; prove common-strip and required directional-width constraints, nonemptiness, and support relations to the core. | Open for arbitrary maximizers. Convexity alone is insufficient. |
| R4: cut slack | First test extension of TW.2 to nonnegative cut slacks. Prove a global sign/equality theorem on the actual enlarged domain, or give a valid counterexample and specify the extra geometric premise needed. | Immediate target. A generic negative eigenvector need not satisfy convexity or the shared strip. |
| R5: ordinary-area core | Prove containment in wings plus a correctly oriented core, or a replacement area inequality retaining all overlaps, clipping and nonsimple-curve corrections. | Open; central geometric task. |
| R6: value assembly | Apply R2–R5 and an audited sharp certificate to an attained maximizer; compare with the feasible candidate. | Conditional on preceding gates. |
| R7: exact equality recovery | Track equality in every enlargement, loss and data inequality; recover the original closed body using a proved regular-closed envelope. | Existing conditional mechanism; global admission/equality transfer still needed. |

R2–R5 are linked, not an assertion that there is only one remaining lemma. R4 is tested first because it can reveal an invalid domain extension before a long geometric argument is built around it.

## 3. Immediate R4 experiment

The current domain has two compact convex bodies R,D in one strip 0<=y<=1, directional widths at most one, and the constructed inward points Q_R in R and Q_D in D. These memberships imply the two cut-width equalities and harmonic support on each inward angular gap.

The first test will **remove the inward memberships while retaining convexity, the common strip and all directional-width inequalities**. The cut points in the proposed extended functional remain defined by TW.2. This is a precise relaxation, not yet a geometric area formula.

Steps:

1. Define the cut-width deficits and distinguish them from the displacement between the old fixed-width cut point and the intersection of the actual inward support lines.
2. Test homothetic, polygonal and smooth support perturbations with checked domain membership. An exact counterexample in this simple subfamily settles the naive extension negatively.
3. If that test survives, derive the endpoint/arc quadratic with independent inward and outward cut traces. Test exact algebra and signs before proposing a global factorization.
4. If it fails, record the failing direction, what geometric material it represents, and whether a corrected functional or a maximality statement is needed. Do not keep attempting the same false inequality under a renamed variable.

The original conditional certificate remains distinct from its proposed relaxation. Failing the relaxation neither disproves Romik optimality nor establishes failure of the original theorem.

## 4. Positive and negative acceptance tests

Any claimed geometric admission must handle, or explicitly exclude by a proved area improvement, the saturated axis-cut and shadow-clipping families. Both are fully feasible near-candidate tests. Saturation and shared anchor constraints alone did not fix the old repair comparisons.

For the reference pair, check the core orientation and endpoint determinants directly. For slack data, check whether the prescribed inward point is actually in the body; that is the hypothesis being relaxed, not something to assume later in the area argument.

A computer-assisted theorem requires exact arithmetic or certified enclosures, a proved covering of the claimed class and zero unresolved boxes. Floating-point optimization, finite samples and symbolic checks are labelled diagnostics or discovery. An unexecuted checker is source, not a completed verification.

## 5. Change control

Each substantive finding is committed separately with `[skip ci]`. The change log below records any alteration to the critical path, the reason, and the precise statement affected. Failed attempts stay available. Existing notes are corrected where needed rather than leaving a false theorem advertised in the index.

A gate is closed only when its stated deliverable and scope are proved. The count of notes, commits or lines does not measure closeness to a proof. There is no numerical completion percentage in this roadmap.

Work outside these gates is deferred unless a proved dependency or explicit counterexample makes it necessary. In particular, no further coarse width estimates, local curvature-repair variants or stability refinements are pursued just because they are available.

## 6. Execution boundary

No CI, Lean/Lake compilation, dependency installation or manuscript build is authorized for this pass. Local algebra and numerical diagnostics are allowed; their status is reported accurately. Existing manuscript, Lean sources, dependencies and workflows stay unchanged. A mathematics result being written does not mean its Lean source has been checked.

PR #3 remains draft until unrestricted admission and independent review are addressed. Completion of the mathematical proof, not merely closing the GitHub PR, is the target.

## 7. Decision log

- **Plan committed:** start with R4's precise slack-domain test, with R0 checks on the formulas it uses. Keep R2/R3/R5 explicit rather than calling them routine consequences of a calibrated functional.
