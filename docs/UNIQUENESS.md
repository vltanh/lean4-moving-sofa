# The uniqueness of Gerver's sofa

This document describes the second part of the repository, [`MovingSofaUniqueness/`](../MovingSofaUniqueness): a proof that
Gerver's sofa is, up to rigid motions, the only moving sofa of maximum area. It uses the definitions
and results of the first part, [`MovingSofaOptimality/`](../MovingSofaOptimality), the formalization of Baek's paper.

## The theorem

Every moving sofa whose area equals the area of Gerver's sofa is mapped onto Gerver's sofa, as a set,
by a rotation about the origin followed by a translation.

- [`gerver_sofa_unique`](../Challenge.lean#L188) in [`Challenge.lean`](../Challenge.lean) states it in Mathlib's vocabulary, and
  [`Solution.lean`](../Solution.lean) proves it; Comparator checks the pair, with the four theorems of Baek's paper.
- In the library ([`MovingSofaUniqueness/Main.lean`](../MovingSofaUniqueness/Main.lean)):
  - [`image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L142): the theorem, for the library's moving sofas and Gerver's sofa;
  - [`volume_eq_gerver_iff`](../MovingSofaUniqueness/Main.lean#L178): a moving sofa has the area of Gerver's sofa if and only if a
    rigid motion maps it onto Gerver's sofa;
  - [`isGlobalMax_iff`](../MovingSofaUniqueness/Main.lean#L188): the moving sofas of maximum area are exactly the moving sofas that a
    rigid motion maps onto Gerver's sofa;
  - [`globalMax_congruent`](../MovingSofaUniqueness/Main.lean#L161) and [`exists_globalMax_unique_up_to_rigid`](../MovingSofaUniqueness/Main.lean#L200): a moving sofa of maximum
    area exists, and any two are congruent.
- A [`Rigid`](../MovingSofaUniqueness/Rigid.lean#L25) map is a rotation by an angle about the origin followed by a translation;
  [`Rigid.norm2_sub`](../MovingSofaUniqueness/Rigid.lean#L80) shows that it preserves Euclidean distances. The conclusion is an equality
  of sets, not an equality up to a null set.
- The characterization of the maximizers keeps the hypothesis that the set is a moving sofa: a moving
  sofa starts in the horizontal side of the hallway, so a rigid image of Gerver's sofa, rotated by a
  right angle for example, need not be one.

`lake build` compiles the proof with no `sorry`, and [`scripts/Audit.lean`](../scripts/Audit.lean) checks that every
declaration of both libraries uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## Where the argument comes from

Baek's paper proves that Gerver's sofa has maximum area; it does not prove that the maximum is
attained only by Gerver's sofa. Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
states the uniqueness as `volume_eq_sofaConstant_iff_congruent_gerversSofa` in the category
`research open`. We know of no earlier proof, but we have not searched the literature
systematically.

The argument was written by ChatGPT Pro (OpenAI) at the request of The-Anh Vu-Le, on 2026-10-02:
the informal proof is [note 20](uniqueness/20-complete-paper-proof.md), and notes 01–19 are the investigation behind it.
ChatGPT Pro also wrote a Lean draft that it could not compile. Claude Opus 5.5 (Anthropic) made the
draft compile and completed it; the README's credits describe how. No human has reviewed the
argument. Lean's kernel checks every step of the formal proof, from the definitions of the
optimality library.

## The argument and its Lean form

The proof starts from a moving sofa S with |S| = |G|, where G is Gerver's sofa. By Baek's
Theorem 1.5.1 it has a rotation angle ω ∈ [arcsec(11/5), π/2]. A translate of S lies in its own
monotonization, which is a moving sofa of the same area, so its cap maximizes the cap-area functional
A_ω. If ω < π/2, a rotated copy of the same monotone sofa has a right-angle motion; monotonizing once
more gives a right-angle monotone sofa T of area |G| that contains a rigid image of S. Its cap
satisfies the injectivity condition, so equality in Baek's upper bound 𝒬 forces T to be a horizontal
translate of G. Since S is closed, G is the closure of its interior, and the areas are equal, the
rigid image of S is all of G.

| Note 20 | Statement | Lean |
| --- | --- | --- |
| Inputs 1–5 | Baek's Theorems 1.1.1 and 1.5.1, Proposition 2.3.1, Theorems 2.3.2, 2.4.1–2.4.3, 2.5.10 and 3.5.2–3.5.6, Lemmas 3.4.5–3.4.8, Chapters 6–8, and the structure of G | [`MovingSofaOptimality`](../MovingSofaOptimality) |
| Proposition 1 | polygon caps converging to a specified maximizer of A_ω, each maximizing a penalized finite objective | [`exists_selectedCapSequence`](../MovingSofaUniqueness/Selection/SelectedCaps.lean#L100), from [`exists_penalizedMax`](../MovingSofaUniqueness/Selection/PolygonSelection.lean#L118) |
| Proposition 2 | the variation defects of the selected polygons, (11) and (12) | [`floating_defect_le`](../MovingSofaUniqueness/Variation/FloatingVariation.lean#L121), [`pinned_defect_le`](../MovingSofaUniqueness/Variation/PinnedVariation.lean#L25) |
| Proposition 3 | every maximizing right-angle cap satisfies the injectivity condition | [`isKi_of_maximal_area`](../MovingSofaUniqueness/Reductions.lean#L99), from [`curvatureBounds_of_isMaxCap`](../MovingSofaUniqueness/Reductions.lean#L89) (the bounds (16)) and [`injectivity_of_curvatureBounds`](../MovingSofaUniqueness/Reductions.lean#L95) |
| Proposition 4 | the specified maximizing monotone sofa has a right-angle motion | [`pinnedBounds_of_isMaxCap`](../MovingSofaUniqueness/Reductions.lean#L116) (the bounds (19)) and [`right_angle_motion_of_pinned`](../MovingSofaUniqueness/Reductions.lean#L122), from [`consumed_of_pinned`](../MovingSofaUniqueness/AngleExtension.lean#L23) |
| Proposition 5 | a maximizing cap in 𝒦^i is Gerver's cap up to a horizontal translation | [`ki_sofa_eq_gerver_translate`](../MovingSofaUniqueness/Reductions.lean#L134), from [`ki_maximizer_equality_conditions`](../MovingSofaUniqueness/Rigidity/EqualityConditions.lean#L194), [`capKernel_of_triple_midpoint`](../MovingSofaUniqueness/Rigidity/MamikonCapKernel.lean#L82) and [`CapKernel.eq_horizontal_translation`](../MovingSofaUniqueness/Rigidity/CapKernel.lean#L51) |
| Proposition 6 | G is the closure of its interior | [`regularClosed_gerver`](../MovingSofaUniqueness/Reductions.lean#L129), from [`gerver_regularClosed`](../MovingSofaUniqueness/RegularClosed/GerverRegularClosed.lean#L29) |
| Proof of the theorem | the containment chain and the recovery of S | [`maximizer_contained_in_gerver`](../MovingSofaUniqueness/Main.lean#L106), [`image_eq_gerver_of_volume_eq`](../MovingSofaUniqueness/Main.lean#L142), with [`eq_of_subset_of_measure_eq`](../MovingSofaUniqueness/SetRecovery.lean#L57) |

The directories of [`MovingSofaUniqueness/`](../MovingSofaUniqueness) follow the propositions: `Selection` (Proposition 1), `Variation`
(Proposition 2 and the pinned bounds of Proposition 4), `Curvature` (Proposition 3), `AngleExtension.lean`
(Proposition 4), `Rigidity` (Proposition 5) and `RegularClosed` (Proposition 6).

## How the formalization differs from note 20

The statements are note 20's. Some proofs take a different route, all described in the modules'
documentation:

- **The selection (Propositions 1 and 2).** Note 20 maximizes A_n − λ_n ∫(h_K − h_{K*})² with λ_n → 0,
  using a uniform approximation e_n of A_ω by A_n. The formalization uses a fixed squared penalty on
  persistent dyadic samples of the support function, with total weight at most 1, and no box
  constraint. The recovery polygon has penalty zero at every stage, and the selected polygons have a
  subsequence converging to the specified cap, so neither λ_n → 0 nor uniform approximation is
  needed.
- **Positive area.** The selection needs the specified cap to have positive sofa area. At a right
  angle this follows by comparison with Gerver's cap; at a smaller angle from |S| = |G| ≥ 2.2.
- **The arm inequalities (Proposition 3).** From the curvature bounds (16), the proof compares the
  arm functions with the lower sequence of Baek's Lemma 6.5.5, as the library does for balanced caps,
  instead of using note 20's maximum-deficit argument. This gives the strict inequalities that the
  injectivity condition needs.
- **Regular closedness (Proposition 6).** Gerver's rotation path stays strictly below the top of the
  cap (`GerverStrictHeight.lean`), which removes note 20's case of a single height-one contact.

## What the formalization found

- **In the argument:** no gap. The 54 proofs of ChatGPT Pro's Lean draft that did not compile failed
  for reasons of Lean: lemma names and argument orders, changes of Mathlib's API, implicit arguments,
  and tactics that did not close their goals.
- **In the draft's statements:** five helper lemmas of `MamikonDisplacement.lean` were false as
  written. Their hypotheses were declared as section variables that the statements do not mention,
  so Lean omitted them, and the lemmas claimed their conclusions for an arbitrary curve. The
  hypotheses are now included; the lemmas' callers already supplied them.
- **Review of the statements:** a separate agent compared the statements with note 20 and found no
  weakening, no vacuous definition and no hidden assumption. It suggested the equivalences and the
  isometry lemma above, which were then added.

## Not formalized

- The quantitative stability estimate of [note 17](uniqueness/17-quantitative-cap-rigidity.md): the uniqueness theorem does not need it.
- The connection with formal-conjectures' statement, whose moving sofas are defined in
  `EuclideanSpace ℝ (Fin 2)` with motions starting at the identity, and whose Gerver's sofa is defined
  from Gerver's four constants. The third part of the repository, [`MovingSofaUniquenessFC/`](../MovingSofaUniquenessFC), is a
  draft of it, not yet compiled.

## The notes

| Note | Content |
| --- | --- |
| [01](uniqueness/01-mamikon-equality.md) | The square-gap identity and the equality kernels of Mamikon's terms |
| [02](uniqueness/02-cap-rigidity.md) | Matching the four cap terms forces a horizontal translation |
| [03](uniqueness/03-global-reduction-obstructions.md) | Counterexamples to two shortcuts: exact-maximizer selection and equal-area set inference |
| [04](uniqueness/04-penalized-selection.md) | The penalized selection of a specified maximizer |
| [05](uniqueness/05-right-angle-selection.md), [06](uniqueness/06-shape-preserving-angle.md) | First proposals for the right-angle extension and the angle reduction |
| [07](uniqueness/07-regular-closedness.md) | Gerver's sofa is the closure of its interior |
| [08](uniqueness/08-candidate-uniqueness-proof.md), [16](uniqueness/16-uniqueness-proof.md) | Earlier assemblies of the proof, superseded by note 20 |
| [09](uniqueness/09-adversarial-review.md), [15](uniqueness/15-final-proof-audit.md) | Reviews of the argument by ChatGPT Pro, and the counterexamples they found |
| [10](uniqueness/10-local-variation-audit.md) | Local variations: sine hats, redundant facets, extreme cells |
| [11](uniqueness/11-analytic-arm-bootstrap.md) | The maximum-deficit argument for the arm inequalities |
| [12](uniqueness/12-compact-selection-proof.md), [13](uniqueness/13-every-right-angle-maximizer.md), [14](uniqueness/14-fixed-angle-maximizer.md) | Compact selection, every right-angle maximizer, and the fixed-angle maximizer |
| [17](uniqueness/17-quantitative-cap-rigidity.md) | A quantitative form of cap rigidity (not formalized) |
| [18](uniqueness/18-failed-uniform-angle-threshold.md), [19](uniqueness/19-exact-angle-reduction.md) | A failed uniform angle threshold, and the exact angle reduction |
| [20](uniqueness/20-complete-paper-proof.md) | **The proof**: the inputs from Baek's paper, six propositions and the theorem |
| [21](uniqueness/21-reference-dependency-audit.md), [22](uniqueness/22-reference-correspondence.md) | Work toward formal-conjectures' statement (see [`MovingSofaUniquenessFC/`](../MovingSofaUniquenessFC)) |

The notes are ChatGPT Pro's working record. Statements in them about the state of the Lean code
("uncompiled", "admissions") describe the draft and are out of date.
