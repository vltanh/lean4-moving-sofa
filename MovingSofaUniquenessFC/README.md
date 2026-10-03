# MovingSofaUniquenessFC: the connection with formal-conjectures (pending)

This directory is the third part of the repository. It is a **draft**: the files are not compiled,
are not part of any Lake library, and are not covered by `lake build`, the axiom audit, the Challenge
or Comparator. They contain `sorry`s and unchecked proofs.

## Goal

Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
states the uniqueness of the optimal sofa as `MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`.
Its definitions differ from those of this repository:

- the plane is `EuclideanSpace ℝ (Fin 2)`, and a motion is a path of affine isometries starting at the
  identity, while here the plane is `ℝ × ℝ` and a motion is a continuous angle and translation that
  may start from a translate of the set;
- the optimal area is the supremum `sofaConstant`, while here it is the area of Gerver's sofa;
- Gerver's sofa is defined from Gerver's four constants, while here it is defined from Romik's
  rotation path ([`MovingSofaOptimality/Gerver/Defs.lean`](../MovingSofaOptimality/Gerver/Defs.lean)).

The files here aim to prove that statement from [`MovingSofaUniqueness`](../MovingSofaUniqueness) by translating between the
two sets of definitions, and by identifying the two descriptions of Gerver's sofa.

## State

The files were written by ChatGPT Pro without a compiler, in pull request #1, and moved here
unchanged when the repository was reorganized. Their imports and names still refer to the old layout:

| Old | New |
| --- | --- |
| `MovingSofa.*` (modules and namespace of the optimality library) | `MovingSofaOptimality.*` |
| `MovingSofa.Paper.IsMovingSofa`, `MovingSofa.Paper.hallway` | `MovingSofaOptimality.IsMovingSofa`, `MovingSofaOptimality.hallway` |
| `SofaUniqueness.Draft.*`, `SofaUniqueness.*` (the uniqueness proof) | `MovingSofaUniqueness.*`; the module map is in the commit that moved the files |
| `SofaUniqueness.Draft.ShapeUniqueness` | `MovingSofaUniqueness.Main` |
| `SofaSubmission.*`, `SofaUniqueness.Bridge.*`, `SofaUniqueness.Reference*` | `MovingSofaUniquenessFC.*` (this directory) |

The namespace `MovingSofa` of formal-conjectures' own definitions, used in files such as
[`Model.lean`](Model.lean) and [`ReferenceDefs.lean`](ReferenceDefs.lean), is not the old name of the optimality library and stays as it is:
since the library's namespace is now `MovingSofaOptimality`, the two no longer clash.

[`NOTES.md`](NOTES.md) and [`OBLIGATIONS.md`](OBLIGATIONS.md) are ChatGPT Pro's notes on this part, and
[`docs/uniqueness/21-reference-dependency-audit.md`](../docs/uniqueness/21-reference-dependency-audit.md) and
[`docs/uniqueness/22-reference-correspondence.md`](../docs/uniqueness/22-reference-correspondence.md) its notes on the correspondence of the two
descriptions of Gerver's sofa.

When this part compiles, it becomes a Lake library, and its final theorem can join the Challenge.
