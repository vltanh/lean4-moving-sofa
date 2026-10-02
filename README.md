# Optimality of Gerver's sofa, in Lean 4

The moving sofa problem asks for the planar shape of largest area that can be moved around the
right-angled corner of a hallway of unit width. Jineon Baek, *Optimality of Gerver's Sofa*
([arXiv:2411.19826v1](https://arxiv.org/abs/2411.19826v1)), proves that Gerver's sofa, of area
2.21953…, is optimal. This repository formalizes the whole proof in Lean 4 with Mathlib:

- every result the paper proves;
- the results it takes from the literature;
- the structure of Gerver's sofa (Theorem 8.4.1), which the paper states without proof.

## What is proved

- **All numbered results of the paper** (Chapters 1–8), proved along the paper's arguments, and the
  main theorem, Theorem 1.1.1 ([`theorem1_1_1`](MovingSofa/Main.lean#L307)). Where the paper's statements contain slips, the
  intended statements are proved. [`REPORT.md`](REPORT.md) lists every correction; no result had to be weakened.
- **The cited results used in proofs:**
  - Schneider's area formula \|K\| = ½ ∫ h_K dσ_K for planar convex bodies ([`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592),
    in [`MovingSofa/External/`](MovingSofa/External));
  - the existence and uniqueness of the solution of Romik's system of equations that defines Gerver's
    sofa ([`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387), [`GerverParams.romik_unique`](MovingSofa/External/Romik.lean#L393), also in [`MovingSofa/External/`](MovingSofa/External));
  - the facts the paper cites from convex geometry and measure theory, which are proved where they
    are used or come from Mathlib.
- **The structure of Gerver's sofa** (Theorem 8.4.1, and with it Theorems 6.1.2, 8.4.2 and the bound
  \|G\| ≥ 2.2), proved from Romik's equations by rigorous interval arithmetic.
- **Status:** `lake build` succeeds, and the only `sorry`s are the three statements of [`Challenge.lean`](Challenge.lean).
  There are no `axiom`s, and [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Run it with `lake env lean scripts/Audit.lean`; it also prints,
  for each result of the paper, the results from prior work that its proof uses.

## The main results

[`Challenge.lean`](Challenge.lean) states the results in Mathlib's vocabulary only, with its own copies of the
definitions (the hallway, moving sofas, Romik's parameters and Gerver's sofa), so that it can be read
without the rest of the repository. [`Solution.lean`](Solution.lean) proves them from the library.

- [`gerver_params_exists`](Challenge.lean#L160) and [`gerver_params_unique`](Challenge.lean#L164): Romik's system of equations (27)–(44) has exactly
  one solution with φ ∈ [0.039, 0.04] and θ ∈ [0.68, 0.69]. So Gerver's sofa, the shape of the rotation
  path these parameters define, is well defined.
- [`gerver_sofa_optimal`](Challenge.lean#L170): Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
  of Gerver's sofa (Theorem 1.1.1).

[`comparator.json`](comparator.json) configures Lake's Comparator, which checks in a sandbox that [`Solution.lean`](Solution.lean) proves
exactly the statements of [`Challenge.lean`](Challenge.lean) with the standard axioms only:

```sh
sed 's/"enable_nanoda": true/"enable_nanoda": false/' comparator.json > /tmp/comparator-local.json
lake comparator --config=/tmp/comparator-local.json
```

## Audit summary

[`REPORT.md`](REPORT.md) audits the paper against its LaTeX source and the formalization. In short:

- **Errors.**
  - Definition 3.2.5 uses the parallelogram P_ω where the fan F_ω is meant, which makes
    Proposition 3.3.5 and Lemma 3.4.2 false as written (E6).
  - The direction (1) ⇒ (2) of Proposition 5.1.4 is false: an absolutely continuous function need not
    have a bounded density (E11).
  - Several statements have slips that make them false as printed, for example Lemma 8.3.6 (3), whose
    left side is identically 0 (E22), and Proposition 8.4.4 (4), shifted by π/2 (E25).
  - All results survive in their intended form.
- **Gaps.**
  - Theorem 8.4.1 has no proof (E23).
  - The proof of Theorem 6.1.2 misreads Gerver's Theorem 2 (E12).
  - The proofs of Lemma 8.1.7 and Theorem 8.2.4 use 𝒩(K) ⊆ K, which the cap space 𝒦^i does not give;
    the statements hold anyway (E20).
  - These gaps are filled here, and the remaining gaps are minor.
- **Missing hypotheses:** none.
- **Redundant hypotheses:** several, listed in Section 5 of the report; the Lean statements omit them.
- **Use of cited results:** correct, except for Gerver's Theorem 2 (E12). Romik's assertion that the
  solution of his system is unique is used by the paper without proof and is proved here.

## Credits

The statements, the proofs, the numerical verification scripts and the audit were written by Claude
Opus 5.5 (Anthropic), in Claude Code, at the request of The-Anh Vu-Le, who is the author and maintainer
of this repository. Claude coordinated sub-agents that worked on separate chapters; every result was
compiled and checked.

## Building

```sh
lake exe cache get        # download Mathlib's compiled files
lake build                # builds the library, Challenge and Solution
lake env lean scripts/Audit.lean
```

The toolchain is `leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](lean-toolchain)), and Mathlib is pinned in
[`lake-manifest.json`](lake-manifest.json).

Two Lean files are generated by scripts, which reproduce them exactly:

- [`MovingSofa/External/Romik/Num.lean`](MovingSofa/External/Romik/Num.lean): `python3 scripts/romik/mk_num.py`;
- [`MovingSofa/Gerver/AreaBounds.lean`](MovingSofa/Gerver/AreaBounds.lean): `cd scripts/area && python3 gen.py emit ../../MovingSofa/Gerver/AreaBounds.lean`.

Both need Python 3 with SymPy and mpmath.

After changing the code, update the links from the documents to the code with
`python3 scripts/linkify_docs.py`, which reads the `.ilean` files that `lake build` writes. Check the
Markdown tables with `python3 scripts/check_md_tables.py README.md REPORT.md`.

## Layout

| Module | Paper content |
| --- | --- |
| [`MovingSofa/Basic/Plane.lean`](MovingSofa/Basic/Plane.lean) | the plane: unit vectors, dot and cross products, rotations, lines, half-planes, area |
| [`MovingSofa/Basic/ConvexBody.lean`](MovingSofa/Basic/ConvexBody.lean) | §2.1: convex bodies, support functions, edges and vertices, Hausdorff distance, Theorem 2.1.3 |
| [`MovingSofa/Basic/LebesgueStieltjes.lean`](MovingSofa/Basic/LebesgueStieltjes.lean) | §5.1: Lebesgue–Stieltjes measures and integrals |
| [`MovingSofa/Basic/SurfaceArea.lean`](MovingSofa/Basic/SurfaceArea.lean) | the surface area measure σ_K, Proposition 2.1.2, §5.2 |
| [`MovingSofa/Sofa/Defs.lean`](MovingSofa/Sofa/Defs.lean) | Chapter 1 and §2.2–2.3: hallways, moving sofas, supporting hallways, monotone sofas |
| [`MovingSofa/Intro/RotationAngleBound.lean`](MovingSofa/Intro/RotationAngleBound.lean) | Theorem 1.5.1 |
| [`MovingSofa/Monotone/`](MovingSofa/Monotone) | §2.2–2.5: supporting hallways, monotonization, caps and niches |
| [`MovingSofa/Balanced/`](MovingSofa/Balanced) | Chapter 3: nef polygons, polygon caps, maximum polygon caps, balanced maximum sofas |
| [`MovingSofa/Angle/`](MovingSofa/Angle) | Chapter 4: the rotation angle of a balanced maximum sofa (Theorem 1.5.2) |
| [`MovingSofa/Injectivity/`](MovingSofa/Injectivity) | Chapter 6 (except Theorem 6.1.2): the injectivity condition |
| [`MovingSofa/Convex/`](MovingSofa/Convex) | Chapter 7: convex domains, curve area functionals, convex curves, Mamikon's theorem |
| [`MovingSofa/Optimality/`](MovingSofa/Optimality) | Chapter 8, §8.1–8.3 and §8.5: the upper bound 𝒬 and its variation |
| [`MovingSofa/Gerver/Defs.lean`](MovingSofa/Gerver/Defs.lean), [`MovingSofa/Gerver/Bounds.lean`](MovingSofa/Gerver/Bounds.lean) | Gerver's sofa from Romik's parameters, and enclosures of the parameters |
| [`MovingSofa/Gerver/Frame.lean`](MovingSofa/Gerver/Frame.lean), [`MovingSofa/Gerver/StructureCap.lean`](MovingSofa/Gerver/StructureCap.lean), [`MovingSofa/Gerver/Structure.lean`](MovingSofa/Gerver/Structure.lean) | Theorem 8.4.1 (except (2)), Theorem 8.4.2, Theorem 6.1.2 |
| [`MovingSofa/Gerver/Envelope.lean`](MovingSofa/Gerver/Envelope.lean), [`MovingSofa/Gerver/EnvelopeArea.lean`](MovingSofa/Gerver/EnvelopeArea.lean), [`MovingSofa/Gerver/NicheBounds.lean`](MovingSofa/Gerver/NicheBounds.lean), [`MovingSofa/Gerver/Niche.lean`](MovingSofa/Gerver/Niche.lean) | Theorem 8.4.1 (2): the niche of Gerver's sofa and its area |
| [`MovingSofa/Gerver/AreaBounds.lean`](MovingSofa/Gerver/AreaBounds.lean) | the bound \|G\| ≥ 2.2 |
| [`MovingSofa/Gerver/Properties.lean`](MovingSofa/Gerver/Properties.lean) | §8.4: Theorems 8.4.1–8.4.6, Proposition 8.4.4 |
| [`MovingSofa/Main.lean`](MovingSofa/Main.lean) | Definition 8.1.2, Theorem 8.1.1 (2)–(3), Theorem 8.5.7, Corollary 8.5.8, Theorem 1.1.1 |
| [`MovingSofa/External/AreaFormula.lean`](MovingSofa/External/AreaFormula.lean), [`MovingSofa/External/AreaFormula/`](MovingSofa/External/AreaFormula) | Schneider's area formula (Remark 5.1.2 of *Convex Bodies*) |
| [`MovingSofa/External/Romik.lean`](MovingSofa/External/Romik.lean), [`MovingSofa/External/Romik/`](MovingSofa/External/Romik) | Romik's system: existence, uniqueness and enclosures of its solution |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | the statement of record and its proof |
| [`scripts/`](scripts) | the axiom audit, the generators of the two generated files, the documentation tools |

## GitHub configuration

`.github/workflows/lean_action_ci.yml` builds the project on every push and pull request, runs the
axiom audit, and checks that the documentation's links and tables are current. It needs no settings.

## License

Apache-2.0 ([`LICENSE`](LICENSE)).
