# Maximizer-first optimality and uniqueness

## Status and scope

This refactor starts from `paper/uniqueness-arxiv` at
`1ade045936f32cf76572ee668ed8aa1627772bde`. Its new and changed Lean proofs are
**uncompiled and not kernel-checked in this work**. No Lean build, Lean audit,
Comparator run, or CI/workflow dispatch is to be performed for this change.
All commits use `[skip ci]`. Existing verification statements about the base
commit do not certify this refactor.

The objective is a non-circular organization of the uniqueness development:

1. Start with an actual maximizer of the fixed-angle cap functional, without
   assuming that its value is Gerver's area.
2. Use penalized selection and the curvature estimates to put every
   right-angle maximizer in the injectivity domain.
3. Compare with Gerver's cap as a competitor and with Baek's quadratic upper
   bound. The two comparisons determine the optimal value; the Mamikon
   equality argument determines the maximizing cap.
4. Use the pinned-bound argument for fixed-angle maximizers of area at least
   `11/5`, followed by the right-angle bound, to recover global optimality.
5. Only then infer maximality from equality with Gerver's area, follow the
   original sofa through its monotone envelopes, and recover equality of sets.

## Insulation of Baek's formalization

`MovingSofaOptimality/` is a read-only upstream dependency for this work. In
particular, its `Main.lean`, `gm_area_le`, and `theorem1_1_1` are neither moved
nor rewritten. Baek's route tables and recorded exceptions remain unchanged.
The definitions and statements in `Challenge.lean`, `ChallengeDefs.lean`,
`Solution.lean`, the bridge, and the toolchain are not part of this refactor.

The new route belongs to `MovingSofaUniqueness`, not to the library recording
Baek's proof. It still uses Baek's intermediate results, notably the existence
of fixed-angle cap maximizers, the angle reduction for large sofas, and the
quadratic functional and its maximum at Gerver's triple. It must not use
Baek's final sofa-area bound, including through the old uniqueness wrappers.

Module-level and theorem-level dependence are different. `Rigidity.lean`
already imports `MovingSofaOptimality.Main` for intermediate results such as
`corollary8_5_8` and `gerverTriple`. Leaving that import in place preserves
Baek's file organization. The intended independence is that the new proof
terms do not depend on `MovingSofaOptimality.theorem1_1_1` or `gm_area_le`;
it is not a claim that those declarations are absent from the environment.
A later declaration-dependency audit must check the transitive claim.

## Implementation plan

- `MovingSofaUniqueness/Maximizers.lean`: maximizer-level geometry, value, and
  rigidity, in the namespace `MovingSofaUniqueness.MaximizerRoute`. Use the
  primitive hypotheses `IsCap K omega` and
  `forall C, IsCap C omega -> sofaArea omega C <= sofaArea omega K`; this avoids
  importing `Main.lean` to obtain its existing `IsMaxCap` abbreviation.
- `MovingSofaUniqueness/Optimality.lean`: the right-angle bound, the arbitrary
  angle bound, and the global optimality theorem obtained from those principles.
- `MovingSofaUniqueness/Main.lean`: preserve its public statements and route its
  numerical bounds through the new proof. Reuse the maximizer principles in
  the equality-case wrappers. Keep the containment and regular-closed recovery.
- Paper notes: give the revised dependency order, exact manuscript insertion
  points, and a careful attribution statement; do not silently change the
  paper PDF or claim it has been regenerated.

## Mathematical claim

A suitable description is: **a maximizer-first strengthening of Baek's
argument, recovering optimality from his intermediate machinery and
characterizing its equality cases**. It is not a proof independent of Baek's
methods. Uniqueness is not automatic from concavity: the selection,
Mamikon-kernel rigidity, and set recovery are substantive additional steps.

No numerical upper bound for all sofas is assumed before proving the new
upper bound. Existence of fixed-angle maximizers must remain an explicit
input; a statement about every maximizer alone does not imply existence.
