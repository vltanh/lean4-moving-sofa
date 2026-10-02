# Uniqueness of the optimal moving sofa: research record

## Result and verification boundary

**Start with [the complete paper proof, note 20](uniqueness/20-complete-paper-proof.md).**

The theorem is

```text
If S is a nonempty closed connected moving sofa and |S|=|G|,
then U(S)=G for a Euclidean isometry U.
```

This is equality of actual sets, not merely almost everywhere and not uniqueness of Romik's parameters. The paper argument is closed relative to the existing optimality and Gerver-geometry inputs explicitly listed in note 20. It proves the additional specified-maximizer, variation, limit, injectivity, rigidity, and exact-set recovery steps rather than adding them as assumptions.

**This is a pen-and-paper proof, not an independently reviewed or Lean-checked uniqueness theorem.** Historical checks of the earlier equality lemmas do not validate the paper proof. No new formal uniqueness declaration is being claimed.

The paper-research commits use `[skip ci]`. Positive results and counterexamples to failed approaches are retained separately. The research does not use CI as an execution environment, and it does not change the challenge, the optimality proofs, or the axiom allowlist.

## Proof chain

```text
original maximizing sofa
  subset its OWN monotonization
  -> a rotated copy of that SAME set with right-angle motion
  subset its right-angle monotonization
  = a translate of G
  -> the original closed equal-area subset is exactly G after isometry.
```

The selection argument maximizes A_n-lambda_n P, with P the squared upper-support distance from the specified cap. It proves convergence to that cap; it never calls the selected polygons exact unpenalized maximizers. Floating defects are O(lambda_n delta_n), pinned defects are O(lambda_n), and both the total error and the endpoint-safe weak limits are proved explicitly.

The new maximum-deficit lemma proves f(t)>=1+t/2 and g(t)>=1+(L-t)/2 for L=pi/2, without the eleven-step numerical bootstrap. Mamikon equality then forces h_K-h_C(G)=a cos(t). Finally G=closure(interior G) upgrades actual containment and equal area to equality of sets.

## Additions in the final continuation

[Note 17](uniqueness/17-quantitative-cap-rigidity.md) strengthens rigidity to the cap stability estimate

```text
For every K in K^i, with a=h_C(G)(pi)-h_K(pi),
d_H(K,C(G)+(a,0))^2 <= 6 (|G|-A_L(K)).
```

Its proof explicitly controls the singular sine denominator at the last tangent endpoint and needs no smooth boundary assumption. This is a result for caps in K^i, not a claimed quantitative stability theorem for arbitrary moving sofas.

[Note 18](uniqueness/18-failed-uniform-angle-threshold.md) records a failed simplification: the threshold d_0=11/10 cannot be used at every angle. At omega=arcsec(11/5), it gives (d_0 sin omega)^2=24/25<1, and the other required geometric inequality fails too.

[Note 19](uniqueness/19-exact-angle-reduction.md) repairs that shortcut with the two thresholds 5/4 and 11/10. Exact positive-coefficient cubic expansions establish the required inequalities, replacing the earlier imported angular scalar/numerical estimates. It constructs the additional motion with explicit continuous placements and transfers any temporary reflection back to the original set.

[Note 20](uniqueness/20-complete-paper-proof.md) is the consolidated proof, with the old inputs stated separately and all six new propositions assembled into the exact-set conclusion. It supersedes note 16 as the reading entry point.

## Current proof notes

| Note | Contribution |
| --- | --- |
| [10: Local variations](uniqueness/10-local-variation-audit.md) | Exact sine hats, including redundant facets and extreme cells; counterexample to a full-circle O(delta) estimate. |
| [11: Analytic arm bootstrap](uniqueness/11-analytic-arm-bootstrap.md) | Maximum-deficit proof of strict arm inequalities for L<5/3, without finite numerical iteration. |
| [12: Compact selection](uniqueness/12-compact-selection-proof.md) | Compact families, uniform niche/cap approximation, recovery, and convergence to a specified maximizer. |
| [13: Every right-angle maximizer](uniqueness/13-every-right-angle-maximizer.md) | Local finite-angle geometry, vanishing error budget, endpoint-safe curvature limits, and injectivity. |
| [14: Fixed-angle maximizer](uniqueness/14-fixed-angle-maximizer.md) | Sections 1-7 give pinned-strip feasibility, assigned/actual support comparison, and endpoint estimates. The geometric continuation is proved with exact constants in note 19. |
| [15: Mathematical audit](uniqueness/15-final-proof-audit.md) | Common triangle, line algebra, reflection, limit order, and a counterexample to global C^1 support regularity. |
| [17: Quantitative cap rigidity](uniqueness/17-quantitative-cap-rigidity.md) | Explicit L2-to-Hausdorff coercivity and the squared-distance bound by six times the area deficit. |
| [18: Failed uniform threshold](uniqueness/18-failed-uniform-angle-threshold.md) | Exact counterexample to using the smaller angular threshold throughout. |
| [19: Exact angle reduction](uniqueness/19-exact-angle-reduction.md) | Rational/polynomial angular certificates, a fixed triangle in the niche, and a motion of the same sofa. |
| [20: Complete paper proof](uniqueness/20-complete-paper-proof.md) | Main theorem, established inputs, six propositions, and equality of the original set with a copy of G. |

## Earlier notes retained as research history

| Note | Contribution and relationship to the final proof |
| --- | --- |
| [01: Mamikon equality](uniqueness/01-mamikon-equality.md) | Square-gap identity and complete first-order equality kernels. Used in the proof. |
| [02: Cap rigidity](uniqueness/02-cap-rigidity.md) | Equality in the four cap terms forces horizontal translation; strengthened in note 17. |
| [03: Obstructions](uniqueness/03-global-reduction-obstructions.md) | Failed exact-maximizer selection and equal-area set inference; conditional recovery lemma. |
| [04: Penalized selection](uniqueness/04-penalized-selection.md) | Abstract selection argument; its geometric approximation hypotheses are supplied in note 12. |
| [05: Proposed right-angle extension](uniqueness/05-right-angle-selection.md) | Historical proposal, replaced by notes 10-13. |
| [06: Proposed angle reduction](uniqueness/06-shape-preserving-angle.md) | Historical proposal, replaced by notes 12, 14, 15 and 19. |
| [07: Regular closedness](uniqueness/07-regular-closedness.md) | G is the closure of its interior, from the existing envelope facts. Used in the proof. |
| [08: Candidate full proof](uniqueness/08-candidate-uniqueness-proof.md) | Historical assembly; superseded by the proofs in notes 16 and 20. |
| [09: Initial adversarial review](uniqueness/09-adversarial-review.md) | Geometry-free perturbation counterexample and initial uncertainty; continued in note 15. |
| [16: Earlier complete assembly](uniqueness/16-uniqueness-proof.md) | Earlier assembly importing Chapter 4 scalar estimates. Note 20 replaces that entry point and uses the exact proof in note 19. |

The counterexamples concern invalid proof methods, not alternative optimal sofas. No noncongruent maximizing sofa has been constructed.

## Commit trail

| Commit | Result |
| --- | --- |
| `7b3377f` | Exact support variations and the failed full-circle estimate. |
| `cbd9f8d` | Analytic replacement for the eleven-step arm bootstrap. |
| `6efb70e` | Uniform approximation and specified-cap selection. |
| `80d8324` | Every maximizing right-angle cap satisfies injectivity. |
| `2f751ce` | Fixed-angle endpoint estimates and a shape-preserving motion. |
| `d127155` | Mathematical audit and the top-regularity counterexample. |
| `0b6e5c9` | Earlier assembled paper proof, note 16. |
| `20b4691` | Quantitative cap rigidity and singular-endpoint control. |
| `9eeb150` | Failure of the uniform smaller angular threshold. |
| `f42b666` | Exact angular certificates and explicit shape-preserving motion. |
| `3b9f3e0` | Consolidated complete proof, note 20. |

## Existing Lean equality foundation

Commit `865eb1f4e936a976d1405cb59f7a83ffc00fe32b` contains the formal equality-case foundation. Import `MovingSofa.Optimality.Equality` to use it. That development does not itself prove geometric uniqueness.

For a quadratic functional f with midpoint m, `ConvexDomain.quadratic_deficit_identity` proves

```text
f(x)-f(y) = -Df(x;y) + 4*(f(m)-(f(x)+f(y))/2).
```

For `upperQL`, `mamikonSegmentEquality_iff` extracts the separate equalities for `mamikonS`, `mamikonR`, and `mamikonL`. `upperQL_eq_gerver_iff` characterizes Gerver-value triples by zero first variation and those midpoint equalities. `ki_upperQL_eq_gerver_of_sofaArea_eq` and `ki_maximizer_equality_conditions` connect them to an IsKi cap attaining Gerver's area.

Those Lean modules and seven regression examples were checked at the earlier commit. None of that historical verification certifies the subsequent analytic or geometric paper arguments. Independent mathematical review and formalization remain distinct from completion of the written proof.
