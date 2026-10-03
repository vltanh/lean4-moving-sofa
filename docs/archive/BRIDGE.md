# The bridge to formal-conjectures

Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
states the moving sofa problem with definitions of its own, different from Baek's. The third part of
the repository, [`MovingSofaBridge/`](../../MovingSofaBridge), proves that the two sets of definitions
describe the same objects. Formal-conjectures' statements then follow from Baek's theorem and from
the uniqueness theorem, both proved with Baek's definitions.

## The two sets of definitions

| | formal-conjectures | Baek's paper |
| --- | --- | --- |
| The plane | `EuclideanSpace ℝ (Fin 2)` | `ℝ × ℝ` |
| A moving sofa | moved by a continuous path in the affine isometries `E(2)` that starts at the identity, so the sofa starts in the horizontal side of the hallway | moved by a continuous rotation angle and translation that start at a translation |
| The optimal area | the sofa constant, a supremum | the area of Gerver's sofa |
| Gerver's sofa | Gerver's four constants `A, B, φ, θ`, the unique solution of a system of four equations; a rotation path defined by integrals; each hallway translated, then rotated | Romik's 22 parameters, a solution of Romik's equations (27)–(44); a rotation path glued from five explicit phases; each hallway rotated, then translated |

[`Challenge.lean`](../../Challenge.lean) restates formal-conjectures' definitions verbatim, in the namespace
`FormalConjectures.MovingSofa` (formal-conjectures itself uses the namespace `MovingSofa`), with one
other change: its anonymous topology instance on `E(2)` gets an explicit name, because Lean
generates a name that depends on the library that declares it. The definitions are those of
`FormalConjectures/Wikipedia/MovingSofa.lean`, Git blob `59b6ed7eb42e11b208b09539c245da4d3f11ed00`.
The Challenge states four of its theorems. It leaves out the test lemmas, and the theorem
`MovingSofa.sofaConstant_eq`, which states `sofaConstant_eq_volume_gerversSofa` inside
formal-conjectures' `answer` marker, a notation that Mathlib does not have.

## The bridge theorems

The coordinates of a point `p` of `EuclideanSpace ℝ (Fin 2)` are `(p 0, p 1)`. The Challenge states
three theorems, in the namespace `Bridge`:

- [`Bridge.isMovingSofa_iff`](../../Challenge.lean#L363): a set is a moving sofa of formal-conjectures if and only if it lies in the
  horizontal side of the hallway and its coordinates form a moving sofa of Baek's paper;
- [`Bridge.sofaConstant_eq`](../../Challenge.lean#L371): the sofa constant is the supremum of the areas of Baek's moving sofas;
- [`Bridge.gerversSofa_eq`](../../Challenge.lean#L379): in coordinates, formal-conjectures' Gerver's sofa is Baek's Gerver's sofa.

[`Solution.lean`](../../Solution.lean) derives formal-conjectures' statements from these and from Baek's theorems, in a few
lines each:

- [`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](../../Challenge.lean#L392): the sofa constant is the
  supremum of the areas of Baek's moving sofas, which is the area of Baek's Gerver's sofa
  ([`Baek.gerver_sofa_optimal`](../../Challenge.lean#L344)), which is the area of formal-conjectures' Gerver's sofa, since the
  coordinates preserve area;
- [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](../../Challenge.lean#L388): formal-conjectures' Gerver's sofa lies in
  the horizontal side, and its coordinates form Baek's Gerver's sofa, a moving sofa;
- [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](../../Challenge.lean#L396): the coordinates
  of a moving sofa of formal-conjectures with area the sofa constant form a moving sofa of Baek's
  with the area of Gerver's sofa, which [`Baek.gerver_sofa_unique`](../../Challenge.lean#L351) maps onto Gerver's sofa by a
  rotation and a translation; the same rotation and translation, as an element of `E(2)`, map the
  sofa onto formal-conjectures' Gerver's sofa.

The bridge uses no result about optimal sofas: neither Baek's theorem nor the uniqueness theorem.

## How the bridge is proved

1. **The motions** ([`MovingSofaBridge/Motion.lean`](../../MovingSofaBridge/Motion.lean)). The coordinate map
   preserves area. A rotation followed by a translation is an element of `E(2)`, continuous in the
   angle and the translation. Conversely, a continuous path in `E(2)` that starts at the identity
   consists of rotations (the determinant of its linear part stays `1`) whose angle lifts to a
   continuous real function, by path lifting through the covering of the circle. A moving sofa of
   Baek's paper starts at a translate of itself; when the sofa lies in the horizontal side, a straight
   slide inside that side reaches the translate. This proves [`MovingSofaBridge.isMovingSofa_iff`](../../MovingSofaBridge/Motion.lean#L590), and
   [`MovingSofaBridge.sofaConstant_eq`](../../MovingSofaBridge/Motion.lean#L627) follows.
2. **Gerver's four constants are unique** ([`MovingSofaBridge/GerverConstants.lean`](../../MovingSofaBridge/GerverConstants.lean)).
   Formal-conjectures defines the constants as the unique solution of the system `ABφθSpec` on the
   domain `0 ≤ φ ≤ θ ≤ π/4`, `A, B ≥ 0`, and its definitions use that uniqueness. The angles determine
   `A` and `B`; every solution has `0 < φ < 1/20` and `φ < θ`; on that triangle the third equation
   decreases strictly in `φ` and increases in `θ`, while a combination of the second and third
   decreases in `φ` and strictly in `θ`. So two solutions coincide ([`MovingSofaBridge.GerverConstants.spec_unique`](../../MovingSofaBridge/GerverConstants.lean#L1283)).
   The proof uses only elementary inequalities for the sine and cosine, and no numerical certificate.
3. **Gerver's constants and Romik's parameters** ([`MovingSofaBridge/RomikParams.lean`](../../MovingSofaBridge/RomikParams.lean)).
   Formulas read the four constants off Romik's parameters and rebuild the parameters from the
   constants. A solution of Romik's system in the box `φ ∈ [0.039, 0.04]`, `θ ∈ [0.68, 0.69]` gives a
   solution of Gerver's, so Gerver's system has exactly one solution
   ([`MovingSofaBridge.GerverConstants.spec_existsUnique`](../../MovingSofaBridge/RomikParams.lean#L357)), and the parameters rebuilt from it solve
   Romik's system ([`MovingSofaBridge.GerverConstants.romik_solution`](../../MovingSofaBridge/RomikParams.lean#L374)).
4. **The two Gerver's sofas** ([`MovingSofaBridge/GerverSofa.lean`](../../MovingSofaBridge/GerverSofa.lean)). The radius
   function in formal-conjectures' integrals is the speed of a contact point of Romik's rotation path,
   except at the four phase boundaries, so the integrals are the coordinates of the contact points.
   They give the coordinates of Romik's path in the rotating frame: rotating formal-conjectures' path
   by the angle gives Romik's path. With formal-conjectures' rotation of `ℝ²` written in coordinates,
   the two sets are equal, including the two special hallways at the ends
   ([`MovingSofaBridge.gerversSofa_eq`](../../MovingSofaBridge/GerverSofa.lean#L537)).

[`MovingSofaBridge.GerverConstants.Spec`](../../MovingSofaBridge/GerverConstants.lean#L46) is a copy of formal-conjectures' `ABφθSpec`: the definitions of
the Challenge, in [`ChallengeDefs.lean`](../../ChallengeDefs.lean), need the uniqueness of the constants, so the
library proves it before they are defined.

## Provenance

ChatGPT Pro 6 (OpenAI) drafted the bridge, without a compiler, in pull request #1. Claude Opus 5.5
(Anthropic) made it compile, had its failing proofs proved again by sub-agents, and then reorganized
it into the four modules above. A separate agent checked every inequality and derivative formula of
the uniqueness of the constants numerically (40-digit arithmetic, dense grids, and three independent
searches for the solutions of Gerver's system) and compared the definitions with formal-conjectures'
file. Formal-conjectures pins Lean v4.33.1; this repository uses v4.35.0-rc3.
