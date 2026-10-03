# MovingSofaUniquenessFC: formal-conjectures' statements

Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
states the moving sofa problem with definitions of its own. This library proves its four statements
with exactly those definitions:

- `MovingSofa.GerversSofa.ABφθSpec.existsUnique`: Gerver's system for the constants A, B, φ, θ has
  exactly one solution on its domain 0 ≤ φ ≤ θ ≤ π/4, A, B ≥ 0, so Gerver's sofa is well defined;
- [`MovingSofa.isMovingSofa_gerversSofa`](../Challenge.lean#L345): Gerver's sofa is a moving sofa;
- [`MovingSofa.sofaConstant_eq_volume_gerversSofa`](../Challenge.lean#L349): its area is the sofa constant (marked solved in
  formal-conjectures);
- [`MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../Challenge.lean#L353): a moving sofa has area the sofa
  constant if and only if an isometry maps Gerver's sofa onto it (marked open in formal-conjectures).

The definitions are in [`ChallengeDefs.lean`](../ChallengeDefs.lean), copied verbatim from formal-conjectures
(`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob `59b6ed7eb42e11b208b09539c245da4d3f11ed00`)
with one change: the topology instance on `E(2)`, anonymous there, has an explicit name, because
Lean's generated name depends on the library that declares it. [`Challenge.lean`](../Challenge.lean) states the four
theorems with a verbatim copy of these definitions, and Comparator checks them with the five
theorems of the other two parts.

## How the definitions differ, and how the proof bridges them

| | formal-conjectures | this repository |
| --- | --- | --- |
| The plane | `EuclideanSpace ℝ (Fin 2)` | `ℝ × ℝ` |
| A motion | a continuous path in the affine isometries `E(2)`, starting at the identity | a continuous angle and translation, starting from a translate of the set |
| The optimal area | the supremum `sofaConstant` | the area of Gerver's sofa |
| Gerver's sofa | from Gerver's four constants, through a rotation path defined by integrals (translate, then rotate) | from Romik's 22 parameters and rotation path (rotate, then translate) |

1. **The motion models agree.** The coordinate map from `EuclideanSpace ℝ (Fin 2)` to `ℝ × ℝ` preserves
   volume and is a homeomorphism. An identity-start path of isometries has determinant one throughout
   and a continuous rotation angle, by path lifting for the circle; conversely, the library's motions
   give such paths. So the two notions of moving sofa agree, up to the initial translation, and the
   two suprema are equal (`Bridge/Motions.lean`).
2. **Gerver's constants.** Eliminating A and B from Gerver's four equations leaves two equations in φ
   and θ (`ReferenceEquations.lean`). The proof excludes φ = 0, φ = θ and large angles, shows that
   every solution has φ < 1/20, and separates any two solutions by the signs of the partial derivatives of
   the two remaining equations (`ReferenceBoundary.lean` to `ReferenceUniqueness.lean`). All the
   estimates are proved by elementary inequalities; no numerical certificate is used. Existence comes
   from the library's solution of Romik's system (`ReferenceModel.lean` to `ReferenceExistence.lean`).
3. **The two Gerver sofas are the same set.** The radius function of formal-conjectures' path is the
   radius of Romik's path almost everywhere, so its integrals are Romik's contact curves
   (`ReferenceRadius.lean`, `ReferenceContacts.lean`); rotating formal-conjectures' path by the angle
   gives Romik's path (`ReferencePath.lean`); and the coordinate map sends formal-conjectures' Gerver
   sofa onto the library's (`coordinates_gerversSofa_eq_paper`, `Bridge/ReferenceShape.lean`).
4. **Assembly.** Baek's Theorem 1.1.1 and the uniqueness theorem of [`MovingSofaUniqueness`](../MovingSofaUniqueness)
   transported through 1 and 3 give the four statements (`ReferenceFacts.lean`, `Extremal.lean`,
   `Uniqueness.lean`, `Final.lean`).

## Provenance

ChatGPT Pro 6 (OpenAI) drafted this library, without a compiler, in pull request #1. Claude Opus 5.5
(Anthropic) ported it to the repository's layout, made every statement compile, and had its 78 failing
proofs proved again by seven sub-agents. The seven helper lemmas of `ReferenceDerivativeSigns.lean` were
false as drafted, because their hypothesis, declared as a section variable, was not part of their
statements; it is now included (the same slip affected five lemmas of the uniqueness proof). A separate
agent checked every inequality and derivative formula of the analytic argument numerically (40-digit
arithmetic, dense grids, and three independent searches for the solutions of Gerver's system) and
compared the definitions with formal-conjectures' file.

Formal-conjectures pins Lean v4.33.1; this repository uses v4.35.0-rc3.
