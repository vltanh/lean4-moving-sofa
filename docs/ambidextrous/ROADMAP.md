# Active roadmap: geometric admission to the two-wing certificate

Baseline: `f6a06beae3bbdfaf6e15547a93eb765a0661463e` in PR #3. This is the active plan requested by the user. It supersedes informal progress percentages, not historical mathematical findings. **Unrestricted optimality and uniqueness are not proved.** Written results are self-reviewed, not independently verified infrastructure.

The goal is an ordinary-area comparison for every relevant maximizing body, followed by a sharp bound with an equality case. A short final implication is not evidence that its missing hypotheses are easy.

## 1. Current result and the exact unresolved part

The first R4 investigation produced [CS1–CS2](two-wing-cut-slack.md) and [SQ1](two-wing-slack-quadratic.md).

- The actual inward supporting-line intersections are retained as independent data. Their differences from the old fixed-width cut points are explicitly the four nonnegative cut slacks.
- Completing both actual corners preserves the common strip, every constrained width and every core support. It changes only the two positively counted wing areas.
- The first variation pays **one half** of tan(beta) times the total cut slack, not the coefficient from the old fixed-vertex formula.
- SQ1 proves the sharp bound and exact equality for arbitrary cut slacks when **both wings span the common strip**. The negative quadratic slack terms are paid by the positive first-order slack terms. All finite identities are displayed and checked exactly.

This is a completed **subcase of R4**, not the whole gate. The original WC2 covers its old cut-vertex domain, including unequal heights. SQ1 covers a different enlarged-cut domain with equal full heights. Neither result currently covers arbitrary cut slack and arbitrary unequal wing heights simultaneously. Nor has it been proved that the canonical wings of every maximizer have full height.

## 2. The intended conclusion and quantifiers

For an arbitrary attained maximizer S, seek data xi with

$$
|S|\leq\widehat{\mathcal W}(\xi)\leq M,
$$

where M is the area of the feasible Romik candidate and the chosen functional matches the actual cut data. Equality must identify S itself up to congruence, not just its hull or selected witnesses. A result for one attained maximizer establishes the value; uniqueness requires every maximizer or a separate equality-preserving comparison.

No auxiliary bound is called an area theorem before its geometric comparison is proved. No candidate-neighborhood assumption is inferred from the desired optimality or uniqueness.

## 3. Critical-path gates

| Gate | Deliverable and acceptance criterion | Current status |
|---|---|---|
| R0: audit the certificate | Recheck the quadratic, first variation, reference geometry and equality conditions from the definitions. Corrections get separate commits. | CS/SQ rational algebra has 16 executed identity checks and three rejected sign/formula mutations. This is not an independent audit of TW/WS/WC or global geometry. |
| R1: normalization and coverage | State the motion class, attainment input, common incoming strip and actual-hull saturation; preserve containment needed for equality. | Earlier notes give these reductions and 2<W<4 for competitive maximizers, not curvature domination. |
| R2: terminal angles | Justify all angles used by the wing construction, or include an explicit ordinary-area correction for missing angles and terminal strips. | Open. Full turns cannot be inserted by convention. |
| R3: canonical wings | Construct actual convex safe pieces from both witnesses; prove nonemptiness, strip/width constraints and the needed support relations. | Open for arbitrary maximizers. Both wings having full height is not assumed. |
| R4: arbitrary cut slack | Prove a sharp comparison/equality theorem on a domain covering the actual wing data, or identify the additional maximality property needed. | SQ1 closes the full-height subcase. Unequal-height wings with arbitrary cut slack remain open. |
| R5: ordinary-area core | Prove containment in the wings plus a correctly oriented core, or a replacement retaining nonsimple-curve, clipping and endpoint corrections. | Open. Pairwise disjointness is not needed for the upper inequality; it must not be confused with simplicity/orientation. |
| R6: value assembly | Apply R2–R5 and an audited sharp certificate to an attained maximizer; compare with the candidate. | Conditional on preceding gates. |
| R7: equality recovery | Track equality in every enlargement and area inequality; recover the original closed body from a regular-closed reference envelope. | Conditional mechanism exists; global admission and equality transfer remain open. |

R2–R5 are linked global obligations. They are not described as one routine lemma.

## 4. The next acceptance test

Continue R4 with the **unequal-height vertical traces retained explicitly**, rather than assuming the full-height equations U=V=-z_0 used in SQ.7. The parameters are the nonnegative distances of the two tops and bottoms from the common strip boundaries, together with the four cut-width slacks. Their geometric constraints must be kept.

The target is either a nonnegative total deficit, including the first-order width losses, or a valid counterexample in the actual convex-body domain. A negative quadratic remainder from independently minimized arc traces is not such a counterexample: the linear slack may pay for it, and arbitrary interpolants need not be convex or meet every width constraint.

If the enlarged certificate fails, record the exact failed statement and return to R3/maximality for the missing property. Do not introduce a new auxiliary functional without specifying its ordinary-area comparison.

In parallel with this acceptance test, only a directly useful R3 or R5 lemma should be pursued. Full-height wing admission may be an alternative, but must be proved rather than inferred from the candidate.

## 5. Positive and negative acceptance tests

Every geometric admission must handle, or exclude by a proved area improvement, the saturated axis-cut and shadow-clipping families. They remain mandatory tests, not already established applications of SQ1. Saturation and shared anchor constraints did not fix the older repair comparisons.

For reference data, verify core orientation and endpoint determinants. For slack data, distinguish width deficits from whether an intersection of two inward supporting lines lies inside the wing. A diameter-one disk has zero cut-width deficit but lacks that inward vertex; CS1 supplies the correct auxiliary completion instead of ignoring the distinction.

A computer-assisted theorem requires exact arithmetic or certified enclosures, a proved covering of its claimed class and no unresolved boxes. Symbolic identities and floating-point searches are labelled according to their actual scope. An unexecuted checker is source, not verification.

## 6. Change control and decision log

Every substantive finding is committed separately with `[skip ci]`. Failed attempts remain recorded. A gate is closed only when its stated deliverable and scope are proved. Counts of notes, commits or lines do not measure closeness to a proof; no numerical completion percentage is assigned.

- **Plan committed:** R4 first, with R0 checks of the formulas it uses; R2/R3/R5 stay explicit.
- **Domain correction:** cut widths equal to one do not force the old inward membership. Introduce actual inward intersections and the four displacement formulas CS.2.
- **Positive R4 subcase:** complete actual corners, then use CS2 plus SQ.9 to prove SQ1 for wings both spanning the strip. In mean-slack variables, the guaranteed positive cost is y(3-y)(s_R+s_D)/4. Equality forces zero cut slack and then the reference pair.
- **Negative control:** SQ.9 is negative when both mean slacks are equal and their differences vanish. Thus claiming joint concavity of the enlarged functional would be false at this algebraic level. The proved total deficit retains its first-order slack.
- **R5 simplification:** containment and a simple clockwise core suffice for |S|<=|R|+|D|+|C| by subadditivity. Disjointness is not a premise of that upper bound. No signed-area assertion for a nonsimple core follows.
- **Exploratory limits:** direct numerical checks on disk/rectangle subfamilies did not falsify the relaxation but give no global bound. Minimizing the enlarged free-trace remainder with unequal heights produced negative values; this does not provide an actual feasible convex-wing counterexample or settle that gate. No unrestricted claim is drawn from either experiment.

Work outside the gates is deferred unless a proved dependency or explicit obstruction makes it necessary. In particular, additional coarse width bounds, protected local repairs and stability refinements are not pursued simply because they are available.

## 7. Reproduction and execution boundary

Run

```sh
python docs/ambidextrous/computer-assisted/check_two_wing_slack.py
```

with SymPy already available to reproduce the exact rational-identity checks. [The recorded run](computer-assisted/two-wing-slack-checks.json) lists all 16 identities, the three rejected mutations, source hashes and versions. The executed source matches the fetched Git blob. No floating-point calculation participates in those identity checks; the positivity arguments and geometric scope are supplied by the written proof, not inferred from the checker.

No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Existing manuscript, Lean source, dependencies and workflows remain unchanged. PR #3 stays draft while unrestricted admission and independent review remain unfinished. Closing the mathematical proof, not merely closing the PR, is the goal.
