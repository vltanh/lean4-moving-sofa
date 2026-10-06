# A second proof of optimality

[Back to the README](../../../README.md)

Baek's proof bounds the area of a moving sofa through one particular cap of each rotation angle, a limit of
maximum polygon caps, and derives two properties of that cap from its balance (steps (3a) and (3b) of Section
1.3 of the manuscript): a rotated copy of its sofa turns by a right angle (Theorem 1.5.2), and, for the right
angle, the cap satisfies the injectivity condition (Theorem 8.1.1 (2)). The uniqueness proof shows both properties for every cap
with the largest sofa area, from the pinned bounds and the curvature bounds, without knowing the largest sofa
area in advance. Gerver's cap competes with every right-angle cap, so a maximizing right-angle cap `K` has

```text
|G| = 𝒜(K_G) ≤ 𝒜(K) ≤ 𝒬(K, B_K, D_K) ≤ 𝒬(K_G, B_G, D_G) = |G|.
```

This determines the largest sofa area, and the equality case shows that the maximizing caps are the horizontal
translates of Gerver's cap. With Baek's existence of a maximizing cap for every rotation angle, it proves Baek's
optimality theorem again, without Baek's Theorem 1.1.1, and the uniqueness theorem follows from this second
proof as from the first. The [manuscript](../../paper/README.md) gave the argument in its Section 8.4 (Lemmas 8.6
and 8.7, Theorem 8.8) until 6 October; it now gives it as a remark at the end of Section 8, with the lemma on the
right-angle motion at the end of Section 6, and Section 11 gives it with the certificate of the stability proof.

## The modules

The three modules do not import [`MovingSofaUniqueness/Main.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/MovingSofaUniqueness/Main.lean), whose results use Baek's theorem, and
their declarations are in the namespace `MovingSofaUniqueness.MaximizerRoute`, beside the declarations of the
same name in `Main`. They use the rest of the library: Baek's results, and the selection, variation, curvature,
angle, rigidity and recovery modules of the uniqueness proof.

| Module | Main declarations | Manuscript |
| --- | --- | --- |
| [`Maximizers.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/MovingSofaUniqueness/Maximizers.lean) | `exists_maximizing_cap` (Baek's Theorems 3.5.5 and 3.5.6); `isKi_of_maximizes`, `right_angle_maximizer_value`, `right_angle_maximizer_eq_gerver`; `maximizing_monotone_has_right_angle` | Fact 2.7, Lemmas 8.6 and 8.7 |
| [`Optimality.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/MovingSofaUniqueness/Optimality.lean) | `right_angle_optimality_and_rigidity`, `right_angle_maximizes_iff_translate_gerver`; `gerver_sofa_optimal`; `cap_area_le_gerver` | Theorem 8.8 |
| [`Alternative.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/MovingSofaUniqueness/Alternative.lean) | `image_eq_gerver_of_volume_eq`, `isMaximal_iff_image_eq_gerver`, `gerver_sofa_optimal_and_unique` | Theorem 1.1 and Corollary 9.4, from Theorem 8.8 |

## The audit

[`scripts/AuditMaximizerRoute.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/scripts/AuditMaximizerRoute.lean) imports both proofs with `import all` and checks every declaration of
the three modules, private and auxiliary ones included. It fails if one of them uses an axiom other than
`propext`, `Classical.choice` and `Quot.sound`, or if, following the proofs through the library without stopping
at numbered results, it reaches

- Baek's Theorem 1.1.1 (`theorem1_1_1`, with its lemma `gm_area_le`);
- the results from which Baek derives steps (3a) and (3b) for Baek's cap from its balance: Theorems 1.5.2,
  4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6, Corollary 6.4.4 and Theorem 8.1.1 (2);
- any declaration of `MovingSofaUniqueness.Main`.

Negative controls check that the traversal finds these results where the first proof uses them. The modules import
Baek's `MovingSofaOptimality/Main.lean` for Corollary 8.5.8, which that file shares with Theorem 1.1.1, so the
check is on the proofs, not on the imports. CI runs the audit after the main one, which also covers the three
modules:

```sh
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/AuditMaximizerRoute.lean
```

## History

Pull request #5 (5 October 2026) added the three modules, the audit and a plan for presenting the second proof in
the manuscript, none of them compiled or run; it left every existing file unchanged. It was merged the same day.
The modules compiled without change and the audit passed. The merge then added the modules to the `import all`
lines of [`scripts/Audit.lean`](https://github.com/vltanh/lean4-moving-sofa/blob/6ed7657/scripts/Audit.lean) (CI checks that the main audit imports every module), extended this audit to the
results behind Baek's steps (3a) and (3b), added it to CI, rewrote the docstrings to refer to the manuscript,
and wrote Section 8.4 of the manuscript (shortened to a remark on 6 October). The plan ([`paper-plan.md`](paper-plan.md)) and the review notes of the
uncompiled draft ([`REVIEW.md`](REVIEW.md)) are kept as they were written, with a note on what has changed.
