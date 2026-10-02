# Uniqueness of the optimal moving sofa: research record

## Result and status

**Start with [the completed paper argument, note 16](uniqueness/16-uniqueness-proof.md).**

The theorem proved by that argument is equality of shapes:

```text
If S is a closed connected moving sofa and |S|=|G|,
then U(S)=G for a Euclidean isometry U.
```

This is equality of actual sets, not merely almost everywhere and not uniqueness of Romik's parameters. The argument is closed relative to the previously established inputs listed in note 16. The formerly proposed extensions in notes 05–06 are proved in the replacement notes 10–14. [Note 15](uniqueness/15-final-proof-audit.md) checks the remaining signs, end cells, top derivatives, and reflection.

**Verification boundary:** this is the author's pen-and-paper proof. It has not been independently reviewed or formalized in Lean. It is not a kernel-checked uniqueness theorem of this repository. Historical CI results for the earlier equality lemmas do not validate the new paper proof.

The research after `865eb1f` is paper-first. Positive results, negative results, and repairs are committed separately with `[skip ci]`. No CI runner, new Lean declarations, new axioms, changes to the challenge, or workflow changes were used for this paper phase.

## Main proof chain

```text
original maximizing sofa
  subset its OWN monotonization
  -> a rotated copy of that SAME set with right-angle motion
  subset its right-angle monotonization
  = a translate of G
  -> the original closed equal-area subset is exactly G after isometry.
```

The three new ingredients beyond the earlier cap equality calculation are:

1. A support-function penalty selects polygon approximations of the specified cap. Uniform finite-angle approximation, recovery caps, and compactness prove convergence without pretending the polygons are exact unpenalized maximizers.
2. Floating-facet errors are O(lambda delta); the two pinned-strip errors are O(lambda). The boundary-vector identity and endpoint-safe weak limits carry the required inequalities to the specified maximizer.
3. A new analytic maximum-deficit argument proves the arm bootstrap for every interval length L<5/3. With L=pi/2 it gives f(t)>=1+t/2 and g(t)>=1+(L-t)/2, replacing the eleven-step iteration.

Mamikon equality then forces h_K-h_{C(G)}=a cos(t), which identifies the cap up to horizontal translation. Gerver's regular-closedness upgrades the final containment and equal area to equality of sets.

## Current proof notes

| Note | Contribution |
| --- | --- |
| [10: Local variations](uniqueness/10-local-variation-audit.md) | Exact sine hats, including redundant facets and extreme cells; a counterexample to the full-circle O(delta) estimate. |
| [11: Analytic arm bootstrap](uniqueness/11-analytic-arm-bootstrap.md) | Maximum-deficit proof of strict arm inequalities for L<5/3, without finite numerical iteration. |
| [12: Compact selection](uniqueness/12-compact-selection-proof.md) | Compact families, uniform niche/cap approximation, recovery, and convergence to a specified maximizer. |
| [13: Every right-angle maximizer](uniqueness/13-every-right-angle-maximizer.md) | Exact finite-angle geometry, vanishing error budget, endpoint-safe curvature limits, and injectivity. |
| [14: Fixed-angle maximizer](uniqueness/14-fixed-angle-maximizer.md) | Pinned-strip feasibility, assigned/actual support comparison, two-sided endpoint estimates, and a motion of the same sofa. |
| [15: Final audit](uniqueness/15-final-proof-audit.md) | Explicit checks of the common triangle, line algebra, reflection, limit order, and a counterexample to global C^1 support regularity. |
| [16: Uniqueness proof](uniqueness/16-uniqueness-proof.md) | Complete theorem statement, explicit old inputs, all new lemmas, and the exact-set conclusion. |

## Earlier notes retained as the research history

| Note | Contribution and relationship to the final proof |
| --- | --- |
| [01: Mamikon equality](uniqueness/01-mamikon-equality.md) | Square-gap identity and the complete first-order equality kernels. Used in the final proof. |
| [02: Cap rigidity](uniqueness/02-cap-rigidity.md) | Equality in the four cap terms forces a horizontal translation. Used in the final proof. |
| [03: Obstructions](uniqueness/03-global-reduction-obstructions.md) | Failed exact-maximizer selection and equal-area set inference; conditional recovery lemma. |
| [04: Penalized selection](uniqueness/04-penalized-selection.md) | Abstract selection argument, with all geometric approximation hypotheses supplied in note 12. |
| [05: Proposed right-angle extension](uniqueness/05-right-angle-selection.md) | Historical proposal. Replaced by notes 10–13, including the analytic bootstrap. |
| [06: Proposed angle reduction](uniqueness/06-shape-preserving-angle.md) | Historical proposal. Replaced by notes 12, 14 and 15. |
| [07: Regular closedness](uniqueness/07-regular-closedness.md) | G is the closure of its interior, from the existing envelope facts. Used in the final proof. |
| [08: Candidate full proof](uniqueness/08-candidate-uniqueness-proof.md) | Historical assembly with explicitly proposed reduction lemmas. Superseded by note 16. |
| [09: Initial adversarial review](uniqueness/09-adversarial-review.md) | Records the geometry-free perturbation counterexample and initial uncertainty; continued in note 15. |

No noncongruent maximizing sofa has been constructed. The counterexamples in this record concern invalid proof methods, not counterexamples to shape uniqueness.

## Commits closing the paper argument

| Commit | Result |
| --- | --- |
| `7b3377f` | Exact support variations and the failed full-circle estimate. |
| `cbd9f8d` | Analytic replacement for the eleven-step arm bootstrap. |
| `6efb70e` | Complete uniform approximation and specified-cap selection. |
| `80d8324` | Every maximizing right-angle cap satisfies injectivity. |
| `2f751ce` | Fixed-angle endpoint estimates and a shape-preserving motion. |
| `d127155` | Final mathematical audit and the top-regularity counterexample. |
| `0b6e5c9` | Complete paper proof, note 16. |

## Existing Lean equality foundation

The earlier commit `865eb1f4e936a976d1405cb59f7a83ffc00fe32b` contains the formal equality-case foundation. Import `MovingSofa.Optimality.Equality` to use it. That development does not itself prove geometric uniqueness.

For a quadratic functional f with midpoint m, `ConvexDomain.quadratic_deficit_identity` proves

```text
f(x)-f(y) = -Df(x;y) + 4*(f(m)-(f(x)+f(y))/2).
```

For `upperQL`, `mamikonSegmentEquality_iff` extracts the three separate convexity equalities for `mamikonS`, `mamikonR`, and `mamikonL`. `upperQL_eq_gerver_iff` characterizes Gerver-value triples by zero first variation and those midpoint equalities. `ki_upperQL_eq_gerver_of_sofaArea_eq` and `ki_maximizer_equality_conditions` connect them to an IsKi cap attaining Gerver's sofa area.

Those Lean modules and seven regression examples were checked at `865eb1f`; the old standard-axiom audit imports them. The original optimality proofs and axiom allowlist are unchanged. None of that historical verification certifies the subsequently written analytic or geometric arguments.

Independent review should read note 16 together with the full reductions in notes 12–14. Notes 02, 07 and 11 are shorter components that can be checked separately. Formalization remains separate from the completed paper argument.
