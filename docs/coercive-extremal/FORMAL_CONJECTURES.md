# Formal-conjectures integration plan

The bridge is a permanent interface of the project. The coercive refactor must
preserve it rather than folding it into the new proof.

## Stable external surface

The following statements should remain unchanged unless the upstream
formal-conjectures definitions themselves change:

- \`Challenge.lean\`;
- \`Bridge.isMovingSofa_iff\`;
- \`Bridge.sofaConstant_eq\`;
- \`Bridge.gerversSofa_eq\`;
- \`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa\`;
- \`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa\`;
- \`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa\`.

The bridge should continue to prove equivalence of definitions and models, not
contain moving-sofa optimality or uniqueness arguments itself.

## Existing canonical solution

\`Solution.lean\` should remain as the canonical proof of the Challenge using:

\`\`\`text
MovingSofaOptimality.theorem1_1_1
+ MovingSofaUniqueness.Main
+ MovingSofaBridge
\`\`\`

This preserves the clean provenance:

- optimality is Baek's faithfully formalized theorem;
- uniqueness is the paper's main proof;
- the bridge transports both to formal-conjectures.

## Second solution route

After the coercive extremal theorem is formalized, add:

\`SolutionCoercive.lean\`

with the same Challenge statements and the same bridge, but with the internal
theorem source changed to:

\`\`\`text
coercive optimality
+ coercive uniqueness
+ MovingSofaBridge
\`\`\`

The purpose is not to create a second external theorem. It is to prove the
**same external theorem by an independently audited internal route**.

## Why two solution files are useful

They separate three questions that otherwise get conflated:

1. Does the repository faithfully formalize Baek's proof?
2. Does the new coercive framework independently prove the extremal theorem?
3. Do both internal formulations correspond to the theorem stated by
   formal-conjectures?

The desired answers are established by different artifacts:

- Baek route/audits answer (1);
- coercive route/audit answers (2);
- the shared bridge and comparator-style statement equality answer (3).

## Upstream PR strategy

For an eventual formal-conjectures submission, the target statement remains

\`volume_eq_sofaConstant_iff_congruent_gerversSofa\`.

The repository's bridge is valuable even if formal-conjectures cannot import
this repository directly: it certifies that the local theorem proved with
Baek/Romik definitions is mathematically the same statement as the upstream
theorem using:

- \`EuclideanSpace ℝ (Fin 2)\`;
- paths in affine isometries \`E(2)\`;
- motions starting at the identity;
- the sofa constant;
- Gerver's sofa from \(A,B,\phi,\theta\).

The upstream patch can therefore be developed against the Challenge copy of
those definitions while the bridge remains the regression test that no
translation of meaning has occurred.

## Bridge dependency rule

The bridge should depend only on what is needed to establish equivalence of:

- coordinates;
- hallway sets;
- rigid motions;
- moving-sofa predicates;
- volume;
- optimal-area formulations;
- Gerver parameterizations and sofa sets.

Where convenient, high-level imports in \`MovingSofaBridge\` may eventually be
lowered to smaller modules, but this is optional. It is not necessary to the
coercive proof and should not delay that proof.

The key invariant is stronger:

> Changing which internal theorem proves optimality or uniqueness must not
> require changing the bridge theorem statements.

## Challenge policy

Do not expand \`Challenge.lean\` merely to expose stability. The current
formal-conjectures target is optimality plus uniqueness/congruence, and the
Challenge should remain a stable statement-of-record interface.

If stability is later proposed upstream as a new conjecture/theorem, add it as a
separate statement after the stability formalization is actually compiled and
reviewed, rather than coupling that change to the present extremal refactor.

## Verification plan

Once Lean compilation is permitted, the final integration should check:

1. \`Solution.lean\` proves the current Challenge;
2. \`SolutionCoercive.lean\` proves the same Challenge;
3. the coercive-route audit excludes Baek's final theorem, Main uniqueness, and
   the old CapKernel classification;
4. the bridge theorem statements have not changed;
5. the formal-conjectures theorem obtained from each solution is definitionally
   or propositionally the same external statement already checked by the
   Challenge/Comparator setup.

Until then, this file is only the integration plan. No build or audit success is
claimed.
