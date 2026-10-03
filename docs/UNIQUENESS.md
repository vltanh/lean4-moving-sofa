# Uniqueness of the optimal moving sofa: research record

## Current source status

**Exact theorem:** [SofaSubmission/Final.lean](../SofaSubmission/Final.lean).
**Concrete correspondence:** [Bridge/ReferenceShape.lean](../SofaUniqueness/Bridge/ReferenceShape.lean).
**Parameter/path argument:** [note 22](uniqueness/22-reference-correspondence.md).
**Dependency inventory:** [formal-conjectures obligations](../drafts/formal-conjectures/OBLIGATIONS.md).

The source now contains the exact formal-conjectures declaration
`MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`, using that
repository's literal integral-defined reference. The full-domain parameter
existence/uniqueness theorem and the concrete motion/optimality facts used by
the corollary have local explicit proof bodies; catalog placeholders are not
imported as proof assumptions. The six paper reductions P1-P6 and model bridges
B1-B3 likewise have written proof bodies.

**The source is UNCOMPILED.** No Lean, Lake, CI, Comparator or independent checker
was run for this development. Written scripts are not a claim of successful
elaboration, a computed axiom closure, independent mathematical verification,
upstream acceptance, or Palomar certification. Source/API/tactic errors,
mathematical errors and version-porting problems may remain.

The canonical motion definitions are shared in `SofaSubmission/Model.lean`.
The paper retains its pair-coordinate presentation and uses ordinary Lean
coordinate, volume and motion bridges. The former source exporter and generated
insertion fragments remain deleted. The rejected external decision-certificate
reference dependency also remains removed.

## Exact-reference correspondence

The main new result states

```lean
coordinates '' MovingSofa.gerversSofa = MovingSofa.gerverSofa P
```

for every valid paper witness P in its established parameter box. This is exact
set equality under coordinates, not merely area equality or congruence. It does
not use the new sofa shape-uniqueness theorem.

Global uniqueness of the reference's four constants is proved on the FULL
upstream domain. Algebra reconstructs A,B from the two angles; elementary
localization gives `0<phi<1/20`; two residuals with complementary monotonicity
separate distinct angle roots. The explicit conversion from the already
constructed paper solution gives existence. Only afterward does uniqueness
identify every reference solution with that witness and yield its small box.

The reference radius is the actual contact curve's derivative density.
Integrability and equality almost everywhere at the four junctions are proved
before applying one-sided FTC. This identifies the literal X,Y integrals and
then proves `R_t p(t)=x(t)`, accounting for translation BEFORE versus AFTER
rotation. The canonical orientation and both endpoint hallways are checked
separately. See [note 22](uniqueness/22-reference-correspondence.md) for the full
argument and its source map.

| Source | Contribution |
| --- | --- |
| [ReferenceUniqueness](../SofaUniqueness/ReferenceUniqueness.lean) | Global analytic uniqueness on the full parameter domain, not boxed uniqueness. |
| [ReferenceFromPaper](../SofaUniqueness/ReferenceFromPaper.lean) | Explicit inverse coefficient/translation map and an actual reference witness. |
| [ReferenceExistence](../SofaUniqueness/ReferenceExistence.lean) | The exact four-tuple existence-and-uniqueness proposition. |
| [ReferenceContacts](../SofaUniqueness/ReferenceContacts.lean) | Reference integrals as actual contact coordinates and their normalizations. |
| [ReferencePath](../SofaUniqueness/ReferencePath.lean) | Correct path convention and exact coordinate shape equality. |
| [ReferenceDefs](../SofaSubmission/ReferenceDefs.lean) | Literal upstream chosen constants, integral path and reference set, with proved parameter theorem. |
| [ReferenceShape](../SofaUniqueness/Bridge/ReferenceShape.lean) | Exact canonical-to-paper concrete set correspondence. |
| [ReferenceFacts](../SofaSubmission/ReferenceFacts.lean) | Concrete upstream motion and optimal volume, derived without shape uniqueness. |
| [Final](../SofaSubmission/Final.lean) | Shared maximizer uniqueness, paper-witness corollary, existence, and exact upstream target. |
| [Exact comparison configuration](../comparator.reference-uniqueness.json) | Unexecuted comparison of the exact target, parameter theorem, and concrete definitions. |

## Core shape-uniqueness source

The actual set-preserving chain is

```text
original maximizing sofa
  subset its OWN monotonization
  -> a rotated copy of that SAME set with right-angle motion
  subset its right-angle monotonization
  = a translate of the paper Gerver sofa
  -> closedness and regular-closedness recover the original set exactly.
```

The source implementation uses a fixed squared penalty on persistent finite
dyadic support samples of bounded total weight. Convergence of support distance
controls the summed floating errors. The earlier notes' continuous
vanishing-penalty construction is retained as research history, not silently
identified with this implementation.

`SelectedCurvature` and `MirroredCurvature` give both curvature inequalities for
the specified maximizer, including normals zero and pi with the correct arm
conventions. `PinnedLimit` gives the specified smaller-angle cap's pinned bounds.
`PaperReductions` discharges the necessary positivity premises at their callers.
`ShapeUniqueness` keeps actual containment and recovers the original closed set.

The scalar arm argument gives `f(t)>=1+t/2` and `g(t)>=1+(L-t)/2` for L=pi/2.
Mamikon equality forces the support difference to be `a cos(t)`; the bottom
segment determines the lower supports. Regular-closedness upgrades containment
and equal finite area to exact equality of sets.

## Paper argument and retained notes

[Note 20](uniqueness/20-complete-paper-proof.md) contains the assembled paper
argument relative to the existing optimality and Gerver-geometry inputs. It
has not been independently reviewed or kernel-checked. Later written Lean
scripts do not retroactively certify that manuscript.

| Note | Contribution and status |
| --- | --- |
| [01: Mamikon equality](uniqueness/01-mamikon-equality.md) | Square-gap identity and first-order equality kernels. |
| [02: Cap rigidity](uniqueness/02-cap-rigidity.md) | Matching four cap terms forces horizontal translation. |
| [03: Obstructions](uniqueness/03-global-reduction-obstructions.md) | Counterexamples to exact-maximizer selection and equal-area set inference. |
| [04: Penalized selection](uniqueness/04-penalized-selection.md) | Abstract continuous-penalty selection argument. |
| [05: Proposed right-angle extension](uniqueness/05-right-angle-selection.md) | Historical proposal, developed in notes 10-13. |
| [06: Proposed angle reduction](uniqueness/06-shape-preserving-angle.md) | Historical proposal, developed in notes 12, 14, 15 and 19. |
| [07: Regular closedness](uniqueness/07-regular-closedness.md) | The paper Gerver sofa is the closure of its interior. |
| [08: Candidate full proof](uniqueness/08-candidate-uniqueness-proof.md) | Historical assembly, superseded as an entry point by note 20. |
| [09: Initial review](uniqueness/09-adversarial-review.md) | Perturbation counterexample and early correctness risks. |
| [10: Local variations](uniqueness/10-local-variation-audit.md) | Exact sine hats, redundant facets and extreme cells. |
| [11: Analytic arm bootstrap](uniqueness/11-analytic-arm-bootstrap.md) | Maximum-deficit argument instead of finite numerical iteration. |
| [12: Compact selection](uniqueness/12-compact-selection-proof.md) | Uniform approximation and continuous-penalty construction. |
| [13: Every right-angle maximizer](uniqueness/13-every-right-angle-maximizer.md) | Local geometry, summed errors and endpoint-safe curvature limits. |
| [14: Fixed-angle maximizer](uniqueness/14-fixed-angle-maximizer.md) | Pinned-strip feasibility, support comparison and endpoint bounds. |
| [15: Mathematical audit](uniqueness/15-final-proof-audit.md) | Common triangle, reflection, order of limits and top-regularity counterexample. |
| [16: Earlier assembly](uniqueness/16-uniqueness-proof.md) | Earlier version importing angular scalar estimates. |
| [17: Quantitative cap rigidity](uniqueness/17-quantitative-cap-rigidity.md) | Explicit L2-to-Hausdorff coercivity for caps in Ki. |
| [18: Failed uniform threshold](uniqueness/18-failed-uniform-angle-threshold.md) | Exact counterexample to using the smaller angular threshold everywhere. |
| [19: Exact angle reduction](uniqueness/19-exact-angle-reduction.md) | Rational/polynomial estimates and a motion of the same sofa. |
| [20: Assembled paper argument](uniqueness/20-complete-paper-proof.md) | Old inputs, six propositions and exact-set conclusion; unreviewed manuscript. |
| [21: Reference dependency audit](uniqueness/21-reference-dependency-audit.md) | Historical rejection of a decision-certificate dependency. |
| [22: Exact reference correspondence](uniqueness/22-reference-correspondence.md) | Analytic global parameter theorem, literal integral/path identification and exact upstream endpoint. |

Note 17 gives the paper cap-stability estimate

```text
d_H(K,C(G)+(a,0))^2 <= 6 (|G|-A_L(K)) for K in Ki,
where a=h_C(G)(pi)-h_K(pi).
```

It is not a quantitative theorem for arbitrary sofas before the reductions.
The counterexamples concern proof methods, not alternative optimal sofas.
No noncongruent maximizing sofa has been constructed.

## Historical milestones and verification

The committed history retains the explicit curvature/pinned proofs, the rejected
reference dependency, the analytic replacement, intermediate corrections and
the exact-reference integration. Research commits use `[skip ci]`. Rejected
prototypes in Git history are not active proof dependencies.

The source examples and both comparison configurations are unexecuted. The
exact-reference configuration compares against an independent statement fixture
and allows only `propext`, `Quot.sound`, `Classical.choice`, with an independent
checker enabled; this is configuration, not a checker result. Challenge
placeholders are not imported by the solution.

Commit `865eb1f4e936a976d1405cb59f7a83ffc00fe32b` contained the historical checked
quadratic/Mamikon equality foundation. Those old checks do not validate any of
the subsequent uniqueness, parameter, bridge or exact-reference source. The
root's Lean 4.35.0-rc3 and the inspected upstream's 4.33.1 remain untested against
one another. Mathematical review, elaboration, definition comparison and the
requested full dependency/source-method checks are still verification work.
