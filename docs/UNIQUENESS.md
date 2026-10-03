# Uniqueness of the optimal moving sofa: research record

## Current source status

**Code entry point:** [SofaSubmission/Final.lean](../SofaSubmission/Final.lean).
**Exact-reference status:** [note 21](uniqueness/21-reference-dependency-audit.md).
**Detailed inventory:** [formal-conjectures obligations](../drafts/formal-conjectures/OBLIGATIONS.md).

The local source now gives explicit proof bodies for all six paper reductions
P1-P6 and the model bridges B1-B3. The last two intentional variational admissions
were replaced by the specified-cap curvature and pinned-bound arguments.
These scripts remain UNCOMPILED; no Lean, CI, Comparator or independent checker
was run in the current continuation.

The current final source states uniqueness of canonical maximizers and its
specialization to the concrete paper Gerver witness. **The exact upstream
theorem naming the other concrete `gerversSofa` formula is not finished under
the requested ban on decision-kernel certificate evaluation.** A proposed
reference-proof dependency was found to use `decide +kernel` and was removed.
The generic theorem has not been relabeled as the exact upstream theorem.

The canonical motion definitions are shared in `SofaSubmission/Model.lean`.
The paper retains its pair-coordinate definitions, with ordinary Lean bridges
for coordinates, volume, identity-start placement and the supremum. The source
exporter and all insertion fragments have been deleted.

## New source work

| Source | Contribution |
| --- | --- |
| [MirrorMaximality](../SofaUniqueness/MirrorMaximality.lean) | Reflection preserves the actual cap's area and maximality, with the plus/minus arm convention. |
| [MirroredCurvature](../SofaUniqueness/MirroredCurvature.lean) | Push the first-half curvature inequality to the second half, including normal pi. |
| [PaperReductions](../SofaUniqueness/Draft/PaperReductions.lean) | P2 and P4 now have bodies; positivity is proved at the appropriate callers. |
| [ShapeUniqueness](../SofaUniqueness/Draft/ShapeUniqueness.lean) | The actual containment chain, both monotonizations, and recovery of the original closed set. |
| [Final](../SofaSubmission/Final.lean) | Canonical maximizers are congruent; explicit equivalence with the concrete paper Gerver set; existence as well as uniqueness. |
| [ReferenceEquations](../SofaUniqueness/ReferenceEquations.lean) | Ordinary algebra eliminates A and B from the full upstream four-equation system; this is not a global root theorem. |
| [ReferenceBoundary](../SofaUniqueness/ReferenceBoundary.lean) | Exclude phi=0 and phi=theta by differentiation and the equations, without certificate evaluation. |
| [Shared comparison](../comparator.shared-uniqueness.json) | Unexecuted independent statement/definition comparison for the shared theorem, with only the three standard axioms permitted. |

The actual source selection uses a fixed squared penalty on persistent finite
dyadic support samples with bounded total weight. Convergence of their support
distance controls the summed floating errors. The earlier notes' continuous
vanishing-penalty construction is retained as research history, not silently
identified with this implementation.

## Paper argument and its verification boundary

[Note 20](uniqueness/20-complete-paper-proof.md) contains the assembled paper
argument for the statement

```text
If S is a nonempty closed connected moving sofa and |S|=|G|,
then U(S)=G for a Euclidean isometry U.
```

It is a manuscript relative to the existing optimality and Gerver-geometry
inputs explicitly listed there. It has not been independently reviewed or
kernel-checked. The later written Lean scripts do not turn the manuscript into
a verified result until they elaborate and pass the dependency checks.

The intended set-preserving chain is

```text
original maximizing sofa
  subset its OWN monotonization
  -> a rotated copy of that SAME set with right-angle motion
  subset its right-angle monotonization
  = a translate of the paper Gerver sofa
  -> closedness and regular-closedness recover the original set exactly.
```

The scalar arm argument gives f(t)>=1+t/2 and g(t)>=1+(L-t)/2 for L=pi/2.
Mamikon equality forces the upper-support difference to be a cos(t), and the
bottom segment determines the lower supports. Regular-closedness of the target
then upgrades actual containment and equal area to equality of sets.

## Paper notes

| Note | Contribution and status |
| --- | --- |
| [01: Mamikon equality](uniqueness/01-mamikon-equality.md) | Square-gap identity and the first-order equality kernels. |
| [02: Cap rigidity](uniqueness/02-cap-rigidity.md) | Matching the four cap terms forces horizontal translation. |
| [03: Obstructions](uniqueness/03-global-reduction-obstructions.md) | Counterexamples to exact-maximizer selection and equal-area set inference. |
| [04: Penalized selection](uniqueness/04-penalized-selection.md) | Abstract continuous-penalty selection argument. |
| [05: Proposed right-angle extension](uniqueness/05-right-angle-selection.md) | Historical proposal, developed in notes 10-13. |
| [06: Proposed angle reduction](uniqueness/06-shape-preserving-angle.md) | Historical proposal, developed in notes 12, 14, 15 and 19. |
| [07: Regular closedness](uniqueness/07-regular-closedness.md) | The paper Gerver sofa is the closure of its interior. |
| [08: Candidate full proof](uniqueness/08-candidate-uniqueness-proof.md) | Historical assembly, superseded as an entry point by note 20. |
| [09: Initial review](uniqueness/09-adversarial-review.md) | Perturbation counterexample and early correctness risks. |
| [10: Local variations](uniqueness/10-local-variation-audit.md) | Exact sine hats, redundant facets and extreme cells. |
| [11: Analytic arm bootstrap](uniqueness/11-analytic-arm-bootstrap.md) | Maximum-deficit argument instead of finite numerical iteration. |
| [12: Compact selection](uniqueness/12-compact-selection-proof.md) | Uniform approximation and the continuous-penalty construction. |
| [13: Every right-angle maximizer](uniqueness/13-every-right-angle-maximizer.md) | Local geometry, summed errors and endpoint-safe curvature limits. |
| [14: Fixed-angle maximizer](uniqueness/14-fixed-angle-maximizer.md) | Pinned-strip feasibility, support comparison and endpoint bounds. |
| [15: Mathematical audit](uniqueness/15-final-proof-audit.md) | Common triangle, reflection, order of limits and the top-regularity counterexample. |
| [16: Earlier assembly](uniqueness/16-uniqueness-proof.md) | Earlier version importing angular scalar estimates. |
| [17: Quantitative cap rigidity](uniqueness/17-quantitative-cap-rigidity.md) | Explicit L2-to-Hausdorff coercivity for caps in Ki. |
| [18: Failed uniform threshold](uniqueness/18-failed-uniform-angle-threshold.md) | Exact counterexample to using the smaller angular threshold everywhere. |
| [19: Exact angle reduction](uniqueness/19-exact-angle-reduction.md) | Rational/polynomial certificates and a motion of the same sofa. |
| [20: Assembled paper argument](uniqueness/20-complete-paper-proof.md) | Old inputs, six new propositions and the exact-set conclusion; unreviewed manuscript. |
| [21: Reference dependency audit](uniqueness/21-reference-dependency-audit.md) | Why the attempted exact-reference shortcut was rejected, and what remains. |

Note 17 additionally gives the paper stability estimate

```text
d_H(K,C(G)+(a,0))^2 <= 6 (|G|-A_L(K)) for K in Ki,
where a=h_C(G)(pi)-h_K(pi).
```

It is not a quantitative theorem for arbitrary moving sofas before the
reductions. The listed counterexamples concern proof methods, not alternative
optimal sofas. No noncongruent maximizing sofa has been constructed.

## Recent source commits

| Commit | Result |
| --- | --- |
| `e90e1d6` | Reflection of the specified cap maximizer. |
| `f846c01` | Mirrored second curvature inequality, including pi. |
| `cadd23e` | Replaced P2 and P4 admissions by source proof bodies. |
| `76530c0` | Discharged positivity in the shape-preserving chain. |
| `62603ce` | Rejected the decision-kernel reference dependency and restored the Mathlib-only configuration. |
| `a15e9a1` | Algebraic reduction of the upstream reference equations. |
| `c8667a5` | Excluded degenerate reference-parameter boundaries. |
| `1c6888f` | Added unexecuted source-interface regressions. |

The discarded reference-specialization prototype is retained in Git history;
its existence there is not a claim that it meets the stricter restrictions.
All commits in this continuation use `[skip ci]`.

## Historical checked equality foundation

Commit `865eb1f4e936a976d1405cb59f7a83ffc00fe32b` contained the earlier checked
quadratic-deficit and Mamikon equality-case foundation, including its IsKi-cap
application and seven regression examples. Those checks do not validate any
of the subsequent uniqueness scripts, the model bridge, the proposed comparison
configuration, or the exact-reference integration. No later validation has been
represented as performed.
