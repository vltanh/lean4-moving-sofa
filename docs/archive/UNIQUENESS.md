# The uniqueness of Gerver's sofa

This document describes the second part of the repository, [`MovingSofaUniqueness/`](../../MovingSofaUniqueness): a proof that
Gerver's sofa is, up to rigid motions, the only moving sofa of maximum area. It uses the definitions
and results of the first part, [`MovingSofaOptimality/`](../../MovingSofaOptimality), the formalization of Baek's paper.

## The theorem

Every moving sofa whose area equals the area of Gerver's sofa is mapped onto Gerver's sofa, as a set,
by a rotation about the origin followed by a translation.

- [`Baek.gerver_sofa_unique`](../../Challenge.lean#L351) in [`Challenge.lean`](../../Challenge.lean) states it in Mathlib's vocabulary, with the
  definitions of Baek's paper, and [`Solution.lean`](../../Solution.lean) proves it; Comparator checks the pair.
- In the library, [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L233) states it for the library's moving
  sofas and Gerver's sofa. A [`MovingSofaUniqueness.Rigid`](../../MovingSofaUniqueness/Rigid.lean) map is a rotation by an angle about the
  origin followed by a translation. The conclusion is an equality of sets, not an equality up to a null
  set.
- With Baek's theorem, it says that the moving sofas of maximum area are exactly the moving sofas that
  a rotation and a translation map onto Gerver's sofa. Not every rigid image of Gerver's sofa is a
  moving sofa: a moving sofa starts in the horizontal side of the hallway.
- Formal-conjectures' statement of the uniqueness,
  [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../../Challenge.lean#L396), follows from it
  through the bridge of [`docs/BRIDGE.md`](BRIDGE.md).

`lake build` compiles the proof with no `sorry`, and [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every
declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).

## Where the argument comes from

Baek's paper proves that Gerver's sofa has maximum area; it does not prove that the maximum is
attained only by Gerver's sofa. Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
states the uniqueness as `volume_eq_sofaConstant_iff_congruent_gerversSofa` in the category
`research open`. We know of no earlier proof, but we have not searched the literature
systematically.

The argument was written by ChatGPT Pro 6 (OpenAI) at the request of The-Anh Vu-Le, on 2026-10-02:
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
| Inputs 1–5 | Baek's Theorems 1.1.1 and 1.5.1, Proposition 2.3.1, Theorems 2.3.2, 2.4.1–2.4.3, 2.5.10 and 3.5.2–3.5.6, Lemmas 3.4.5–3.4.8, Chapters 6–8, and the structure of G | [`MovingSofaOptimality`](../../MovingSofaOptimality) |
| Proposition 1 | polygon caps converging to a specified maximizer of A_ω, each maximizing a penalized finite objective | [`MovingSofaUniqueness.exists_selectedCapSequence`](../../MovingSofaUniqueness/Selection.lean#L956), from [`MovingSofaUniqueness.exists_penalizedMax`](../../MovingSofaUniqueness/Selection.lean#L556) |
| Proposition 2 | the variation defects of the selected polygons, (11) and (12) | [`MovingSofaUniqueness.floating_defect_le`](../../MovingSofaUniqueness/Variation.lean#L284), [`MovingSofaUniqueness.pinned_defect_le`](../../MovingSofaUniqueness/Variation.lean#L599) |
| Proposition 3 | every maximizing right-angle cap satisfies the injectivity condition | [`MovingSofaUniqueness.isKi_of_maximal_area`](../../MovingSofaUniqueness/Main.lean#L88), from [`MovingSofaUniqueness.curvature_of_maximal_positive`](../../MovingSofaUniqueness/Curvature.lean#L1470) (the bounds (16)) and [`MovingSofaUniqueness.injectivity_of_curvature`](../../MovingSofaUniqueness/Curvature.lean#L708) |
| Proposition 4 | the specified maximizing monotone sofa has a right-angle motion | [`MovingSofaUniqueness.maximal_monotone_has_right_angle`](../../MovingSofaUniqueness/Main.lean#L164), from [`MovingSofaUniqueness.pinned_bounds_of_maximal_positive`](../../MovingSofaUniqueness/Variation.lean#L831) (the bounds (19)) and [`MovingSofaUniqueness.right_angle_motion_of_pinned_bounds`](../../MovingSofaUniqueness/AngleExtension.lean#L185) |
| Proposition 5 | a maximizing cap in 𝒦^i is Gerver's cap up to a horizontal translation | [`MovingSofaUniqueness.ki_sofa_eq_gerver_translate`](../../MovingSofaUniqueness/Main.lean#L103), from [`MovingSofaUniqueness.ki_maximizer_equality_conditions`](../../MovingSofaUniqueness/Rigidity.lean#L881), [`MovingSofaUniqueness.capKernel_of_triple_midpoint`](../../MovingSofaUniqueness/Rigidity.lean#L974) and [`MovingSofaUniqueness.CapKernel.eq_horizontal_translation`](../../MovingSofaUniqueness/Rigidity.lean#L197) |
| Proposition 6 | G is the closure of its interior | [`MovingSofaUniqueness.gerver_regularClosed`](../../MovingSofaUniqueness/RegularClosed.lean#L349) |
| Proof of the theorem | the containment chain and the recovery of S | [`MovingSofaUniqueness.maximizer_contained_in_gerver`](../../MovingSofaUniqueness/Main.lean#L196), [`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](../../MovingSofaUniqueness/Main.lean#L233), with [`MovingSofaUniqueness.eq_of_subset_of_measure_eq`](../../MovingSofaUniqueness/Rigid.lean#L59) |

The modules of [`MovingSofaUniqueness/`](../../MovingSofaUniqueness) follow the propositions:
[`Selection.lean`](../../MovingSofaUniqueness/Selection.lean) (Proposition 1), [`Variation.lean`](../../MovingSofaUniqueness/Variation.lean) (Proposition 2 and the pinned
bounds (19)), [`Curvature.lean`](../../MovingSofaUniqueness/Curvature.lean) (Proposition 3), [`AngleExtension.lean`](../../MovingSofaUniqueness/AngleExtension.lean) (Proposition 4),
[`Rigidity.lean`](../../MovingSofaUniqueness/Rigidity.lean) (Proposition 5) and [`RegularClosed.lean`](../../MovingSofaUniqueness/RegularClosed.lean) (Proposition 6);
[`Rigid.lean`](../../MovingSofaUniqueness/Rigid.lean) holds the rigid maps and the recovery of a set from its area, and
[`Main.lean`](../../MovingSofaUniqueness/Main.lean) assembles the theorem.

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
  cap ([`MovingSofaOptimality.GerverParams.path_snd_lt_one`](../../MovingSofaUniqueness/RegularClosed.lean#L36)), which removes note 20's case of a single height-one
  contact.

## What the formalization found

- **In the argument:** no gap. The 54 proofs of ChatGPT Pro's Lean draft that did not compile failed
  for reasons of Lean: lemma names and argument orders, changes of Mathlib's API, implicit arguments,
  and tactics that did not close their goals.
- **In the draft's statements:** five helper lemmas on the displacement functions of Mamikon's formula
  (now in [`Rigidity.lean`](../../MovingSofaUniqueness/Rigidity.lean)) were false as written. Their hypotheses were declared as section variables that the statements do not mention,
  so Lean omitted them, and the lemmas claimed their conclusions for an arbitrary curve. The
  hypotheses are now included; the lemmas' callers already supplied them.
- **Review of the statements:** a separate agent compared the statements with note 20 and found no
  weakening, no vacuous definition and no hidden assumption.

## Not formalized

- The quantitative stability estimate of [note 17](uniqueness/17-quantitative-cap-rigidity.md): the uniqueness theorem does not need it.

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
| [21](uniqueness/21-reference-dependency-audit.md), [22](uniqueness/22-reference-correspondence.md) | The correspondence with formal-conjectures' definitions, formalized in [`MovingSofaBridge/`](../../MovingSofaBridge) ([`docs/BRIDGE.md`](BRIDGE.md)) |

The notes are ChatGPT Pro's working record. Statements in them about the state of the Lean code
("uncompiled", "admissions") describe the draft and are out of date.
