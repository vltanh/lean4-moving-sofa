# Optimality and uniqueness of Gerver's sofa, in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml)

The moving sofa problem asks for the planar shape of largest area that can be moved around the
right-angled corner of a hallway of unit width. Jineon Baek, *Optimality of Gerver's Sofa*
([arXiv:2411.19826v1](https://arxiv.org/abs/2411.19826v1)), proves that Gerver's sofa, of area
2.21953…, is optimal. This repository proves in Lean 4 with Mathlib:

- **optimality:** Baek's whole proof, with the results it takes from the literature, and the structure
  of Gerver's sofa (Theorem 8.4.1), which the paper states without proof;
- **uniqueness:** every moving sofa with the area of Gerver's sofa is congruent to it. So Gerver's sofa
  is, up to rigid motions, the only moving sofa of maximum area. Baek's paper does not prove this. The
  argument was written by ChatGPT Pro 6 (OpenAI) for this repository and has not been peer reviewed;
  Lean's kernel checks every step of the formal proof;
- **the bridge to formal-conjectures:** Google DeepMind's formal-conjectures states the problem with
  definitions of its own. They describe the same moving sofas, the same optimal area and the same
  Gerver's sofa as Baek's, so formal-conjectures' statements follow from the first two results,
  including its statement of the uniqueness, which it lists as open.

## The three parts

| Part | Content |
| --- | --- |
| [`MovingSofaOptimality/`](MovingSofaOptimality) | the formalization of Baek's paper, audited in [`REPORT.md`](REPORT.md) |
| [`MovingSofaUniqueness/`](MovingSofaUniqueness) | the uniqueness of Gerver's sofa, with Baek's definitions; described in [`docs/UNIQUENESS.md`](docs/UNIQUENESS.md) |
| [`MovingSofaBridge/`](MovingSofaBridge) | the bridge between formal-conjectures' definitions and Baek's; described in [`docs/BRIDGE.md`](docs/BRIDGE.md) |

[`Challenge.lean`](Challenge.lean) states the main results of the three parts in Mathlib's vocabulary, and
[`Solution.lean`](Solution.lean) proves them.

## What is proved

### Optimality

- **All numbered results of the paper** (Chapters 1–8), proved along the paper's arguments, and the
  main theorem, Theorem 1.1.1 ([`MovingSofaOptimality.theorem1_1_1`](MovingSofaOptimality/Main.lean#L318)). Where the paper's statements contain slips, the
  intended statements are proved. [`REPORT.md`](REPORT.md) lists every correction; no result had to be weakened.
- **The cited results used in proofs:**
  - Schneider's area formula \|K\| = ½ ∫ h_K dσ_K for planar convex bodies ([`MovingSofaOptimality.area_eq_half_integral_supp`](MovingSofaOptimality/External/AreaFormula.lean#L592),
    in [`MovingSofaOptimality/External/`](MovingSofaOptimality/External));
  - the existence and uniqueness of the solution of Romik's system of equations that defines Gerver's
    sofa ([`MovingSofaOptimality.GerverParams.romik_exists`](MovingSofaOptimality/External/Romik.lean#L387), [`MovingSofaOptimality.GerverParams.romik_unique`](MovingSofaOptimality/External/Romik.lean#L393), also in [`MovingSofaOptimality/External/`](MovingSofaOptimality/External));
  - the facts the paper cites from convex geometry and measure theory, which are proved where they
    are used or come from Mathlib.
- **The structure of Gerver's sofa** (Theorem 8.4.1, and with it Theorems 6.1.2 and 8.4.2), and its area,
  between 2.2192 and 2.2199, proved from Romik's equations by rigorous interval arithmetic.

### Uniqueness

- **The theorem:** a moving sofa whose area equals that of Gerver's sofa is mapped onto Gerver's sofa,
  as a set, by a rotation about the origin followed by a translation
  ([`MovingSofaUniqueness.image_eq_gerver_of_volume_eq`](MovingSofaUniqueness/Main.lean#L233)).
- **The proof** monotonizes the sofa, extends its motion to a right angle, shows that the cap of the
  resulting sofa satisfies Baek's injectivity condition, and then uses the equality case of Baek's upper
  bound to identify it with Gerver's cap; regular closedness of Gerver's sofa recovers the original set.
  The library has one module per proposition of the informal proof, [note 20](docs/uniqueness/20-complete-paper-proof.md);
  [`docs/UNIQUENESS.md`](docs/UNIQUENESS.md) maps each step to Lean.

### The bridge to formal-conjectures

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
places moving sofas in `EuclideanSpace ℝ (Fin 2)` and moves them by continuous paths of affine
isometries that start at the identity; it defines the sofa constant as the supremum of their areas, and
Gerver's sofa from Gerver's four constants through a rotation path defined by integrals. Baek's paper
places them in `ℝ × ℝ`, moves them by a continuous rotation angle and translation, and takes Gerver's
sofa from Romik's 22 parameters. The bridge proves that, read in the coordinates `(p 0, p 1)`, the two
describe the same objects:

- [`Bridge.isMovingSofa_iff`](Challenge.lean#L363): a set is a moving sofa of formal-conjectures if and only if it lies in the
  horizontal side of the hallway and its coordinates form a moving sofa of Baek's;
- [`Bridge.sofaConstant_eq`](Challenge.lean#L371): the sofa constant is the supremum of the areas of Baek's moving sofas;
- [`Bridge.gerversSofa_eq`](Challenge.lean#L379): formal-conjectures' Gerver's sofa is Baek's, in coordinates. Along the way,
  formal-conjectures' Gerver's constants are proved unique on their whole domain by elementary
  inequalities, without numerical certificates ([`MovingSofaBridge.GerverConstants.spec_unique`](MovingSofaBridge/GerverConstants.lean#L1283)).

The bridge uses no result about optimal sofas. [`Solution.lean`](Solution.lean) then derives formal-conjectures'
statements from Baek's in a few lines each. [`docs/BRIDGE.md`](docs/BRIDGE.md) describes the proof.

### Status

`lake build` succeeds, and the only `sorry`s are the twelve statements of [`Challenge.lean`](Challenge.lean). There
are no `axiom`s, and [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the three libraries uses only
[`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Run it with `lake env lean scripts/Audit.lean`; it also prints, for
each result of the paper, each step of the uniqueness proof and each bridge theorem, the results from
prior work that its proof uses.

## The main results

[`Challenge.lean`](Challenge.lean) states the results in Mathlib's vocabulary only, with its own copies of the
definitions, so that it can be read without the rest of the repository. It has three namespaces, one
per set of definitions and one for the bridge:

- `Baek`, the definitions of Baek's paper (the hallway, moving sofas, Romik's parameters and Gerver's
  sofa):
  - [`Baek.gerver_params_exists`](Challenge.lean#L328) and [`Baek.gerver_params_unique`](Challenge.lean#L332): Romik's system of equations (27)–(44) has exactly
    one solution with φ ∈ [0.039, 0.04] and θ ∈ [0.68, 0.69], so Gerver's sofa is well defined;
  - [`Baek.gerver_sofa_area`](Challenge.lean#L338): Gerver's sofa has area between 2.2192 and 2.2199. Gerver's value is 2.21953…;
    this ties the shape defined from Romik's parameters to the sofa Gerver found;
  - [`Baek.gerver_sofa_optimal`](Challenge.lean#L344): Gerver's sofa is a moving sofa, and every moving sofa has area at most the
    area of Gerver's sofa (Baek's Theorem 1.1.1);
  - [`Baek.gerver_sofa_unique`](Challenge.lean#L351): every moving sofa with the area of Gerver's sofa is mapped onto Gerver's sofa
    by a rotation about the origin followed by a translation.
- `FormalConjectures.MovingSofa`, the definitions of formal-conjectures, restated verbatim in that
  namespace (formal-conjectures uses `MovingSofa`), with an explicit name for its anonymous topology
  instance on `E(2)`:
  - `FormalConjectures.MovingSofa.GerversSofa.ABφθSpec.existsUnique`: Gerver's system has exactly one solution;
  - [`FormalConjectures.MovingSofa.isMovingSofa_gerversSofa`](Challenge.lean#L388) and [`FormalConjectures.MovingSofa.sofaConstant_eq_volume_gerversSofa`](Challenge.lean#L392): Gerver's sofa is a
    moving sofa whose area is the sofa constant (marked solved in formal-conjectures);
  - [`FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa`](Challenge.lean#L396): a moving sofa has area the sofa
    constant if and only if an isometry maps Gerver's sofa onto it (marked open in formal-conjectures).
- `Bridge`: the three theorems above, [`Bridge.isMovingSofa_iff`](Challenge.lean#L363), [`Bridge.sofaConstant_eq`](Challenge.lean#L371) and [`Bridge.gerversSofa_eq`](Challenge.lean#L379).

The definitions are a verbatim copy of [`ChallengeDefs.lean`](ChallengeDefs.lean), which the libraries and
[`Solution.lean`](Solution.lean) use, and `scripts/sync_challenge_defs.py --check` checks the copy.
[`comparator.json`](comparator.json) configures Lake's Comparator, which checks in a sandbox that [`Solution.lean`](Solution.lean)
proves exactly the twelve statements of [`Challenge.lean`](Challenge.lean) with the standard axioms only:

```sh
lake env lake comparator --config=comparator.json
```

## Palomar

The repository is packaged for the [Palomar](https://palomar-registry.org) registry of machine-checked
proofs. Its entry is PALOMAR-2026-10-02-000008: version 1 registers the optimality part (commit
`d0b42d2`), and version 2 adds the uniqueness theorem (commit `cf4feff`).

- [`Challenge.lean`](Challenge.lean) holds the statements of record;
- [`Solution.lean`](Solution.lean) holds their proofs;
- [`comparator.json`](comparator.json), the only Comparator configuration, selects the twelve compared theorems;
- [`formalization.yaml`](formalization.yaml) records the metadata: sources, scope, divergences from the
  paper, automation and review;
- [`LICENSE`](LICENSE) holds the licence.

The workflow [`.github/workflows/palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs
Palomar's complete mechanical verification on a commit, on demand. It is pinned to a fixed commit of
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission). Run it with
`gh workflow run palomar_preflight.yml --ref main`; it publishes its report as the artifact
`mechanical-report-preflight001`. The preflight does not cover the rendering of the Challenge, which
Palomar runs after verification; see [Building](#building) for the Mathlib pin that rendering needs.

## The moving sofa problem and earlier work

- Leo Moser posed the problem in 1966 (SIAM Review 8, Problem 66-11).
- Hammersley found a sofa of area π/2 + 2/π ≈ 2.2074 and showed that the maximum is at most
  2√2 ≈ 2.83.
- Gerver (*Geometriae Dedicata* 42, 1992) found a sofa of area 2.21953… and conjectured that it is
  optimal.
- Romik (*Experimental Mathematics* 27, 2018) derived Gerver's sofa from a system of differential
  equations and solved it explicitly; the Challenge's definition of Gerver's sofa follows him.
- Kallus and Romik (*Advances in Mathematics* 340, 2018) proved by computer that the maximum is at
  most 2.37.
- Baek's preprint (arXiv:2411.19826, 2024) proves that Gerver's sofa is optimal. This repository
  formalizes version 1 of it.
- That Gerver's sofa is the only optimal sofa, up to rigid motions, is not proved in Baek's paper.
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
  states it as `volume_eq_sofaConstant_iff_congruent_gerversSofa`, in its category `research open`;
  this repository proves that statement. We know of no earlier proof, but have not searched the
  literature systematically.

### Earlier formalizations

Two Lean 4 formalizations of Baek's proof appeared shortly before this one:
[deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), written by AI coding agents
directed by Dean Cureton, and [RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal).
Both prove the statement of Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean),
`sofaConstant = volume gerversSofa`, and their READMEs report that Comparator accepts the proofs with
only the standard axioms. The three differ as follows. The other two columns describe commits
`4d55691` (2026-09-21) and `ca8585c` (2026-09-24), from their READMEs and sources.

| | This repository | deancureton/MovingSofa | RuifengCao/sofa-formal |
| --- | --- | --- | --- |
| Statement | its own [`Challenge.lean`](Challenge.lean): Gerver's sofa is a moving sofa, no moving sofa has a larger area, and every moving sofa of that area is congruent to it; the bridge between the two sets of definitions; and the formal-conjectures statements | the formal-conjectures statement | the formal-conjectures statement |
| Uniqueness of the optimal sofa | proved, also in formal-conjectures' form | not proved | not proved |
| Moving sofas | the motion may start from a translate of the set, as in the paper | the motion starts at the identity | the motion starts at the identity |
| Gerver's sofa | Romik's description: 22 parameters satisfying Romik's equations (27)–(44), with exactly one solution in a stated box; and Gerver's description, proved to give the same set | Gerver's description: four constants satisfying four equations, with exactly one solution on a closed domain | Gerver's description, as in MovingSofa |
| Area of Gerver's sofa | between 2.2192 and 2.2199 | at least 2.2 | the bounds that the proof needs |
| The paper's use of Green's theorem | replaced by direct computations of the areas | a Green-type identity, proved with Jordan curve results from other libraries | replaced by direct computations of the areas |
| Dependencies | Mathlib | Mathlib, jordan_pick and leancert, and vendored copies of Trela's GerverSofaLean, lean-pool and TauCeti | Mathlib |
| Numerical checks | interval arithmetic by `norm_num`, generated by scripts in the repository; Gerver's four constants by analytic inequalities | an integer interval certificate checked by `decide +kernel` | interval arithmetic checked by `decide +kernel` |

Like the earlier two, this repository proves the facts about Gerver's sofa that the paper states
without proof or takes from Gerver and Romik (Theorems 6.1.2, 8.4.1 and 8.4.2). For the niche,
Theorem 8.4.1(2), the proof reduces a two-parameter family of inequalities to one-variable
inequalities verified by interval arithmetic.

## Audit summary

[`REPORT.md`](REPORT.md) audits Baek's paper against its LaTeX source and the formalization. In short:

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
  solution of the system is unique is used by the paper without proof and is proved here.

For the uniqueness proof, [`docs/UNIQUENESS.md`](docs/UNIQUENESS.md) records how the formal proof follows the informal one and
where it departs from it. The formalization found no gap in the argument. It found five helper lemmas
of the Lean draft that were false as written, because hypotheses declared as section variables were
not part of their statements; they are corrected.

## Credits

The-Anh Vu-Le is the author and maintainer of this repository. AI systems wrote the code, the proofs
and the documents at the author's request. No human has reviewed the proofs; Lean's kernel checks every
one of them.

### Formalizing Baek's paper

The statements, the proofs, the numerical verification scripts and the audit were written by Claude
Opus 5.5 (Anthropic, model `claude-opus-5-5`), running in Claude Code 2.1.285.

- **Procedure.** The work followed the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper)
  skill (commit `cbdedac`): state every result first, then prove the paper's results and the results it
  cites, verify, clean up, and audit the paper.
- **Agents.** One coordinating agent and 19 sub-agents, at most 13 of them running at the same time:
  - 17 proved groups of files, each a chapter or part of one, and for Gerver's sofa its separate
    components (Romik's system, the structure of the sofa, the niche, the area);
  - one reviewed every statement against the paper's LaTeX source before any proof was written;
  - one checked every finding about the paper against the LaTeX source for the audit.

  The coordinating agent wrote the statements, divided the work, checked and integrated every result,
  and wrote the documents. It also resumed finished sub-agents three times for follow-up work.
- **Time.** About 3 hours 50 minutes of elapsed time, from 2026-10-01 22:38 to 2026-10-02 02:28 (US
  Central Time), up to the audited formalization (commit `59b35c2`). The sub-agents worked about 18
  hours in total. All agents together made 3,135 tool calls (2,704 of them by sub-agents), generated
  7.5 million output tokens and read 21 million input tokens, plus 1.2 billion tokens from the prompt
  cache. Preparing the Palomar submission came afterwards.

### Proving uniqueness

- **The argument and the Lean draft.** ChatGPT Pro 6 (OpenAI) wrote the informal proof
  ([note 20](docs/uniqueness/20-complete-paper-proof.md) and the notes before it), a Lean draft of it, and a draft of the connection with
  formal-conjectures, all without a compiler, in 151 commits from 2026-10-02 15:01 to 22:43 (US
  Central Time), in pull request #1 of this repository. Its effort was not recorded.
- **The compiled proof.** Claude Opus 5.5 (model `claude-opus-5-5`), running in Claude Code 2.1.287,
  with the same skill (version 1.3.0), made the draft compile and completed it:
  - It checked every module of the draft and replaced the 54 proofs that did not compile by `sorry`;
    every statement compiled.
  - Eight sub-agents, each owning a group of files, proved those 54 again, starting from the draft's
    proofs; a ninth reviewed the statements against note 20. At most nine ran at the same time.
  - The coordinating agent integrated the proofs, removed unused hypotheses, added the theorem's
    statement to the Challenge, reorganized the repository into its three parts, and wrote the
    documents.
- **Time.** About 1 hour of elapsed time, from 2026-10-02 21:55 to 22:56 (US Central Time), up to the
  documented proof (commit `7f967fd`); every proof compiled after 27 minutes. The sub-agents worked
  about 0.9 hours in total. All agents together made 607 tool calls (400 of them by sub-agents),
  generated 0.5 million output tokens and read 1.7 million input tokens, plus 105 million tokens from
  the prompt cache.

### Bridging to formal-conjectures

Claude Opus 5.5 (model `claude-opus-5-5`), in the same Claude Code session, ported ChatGPT Pro 6's draft
of the connection to the repository's layout and completed it:

- Every statement compiled after renaming and a few fixes; the 78 proofs that did not compile were
  replaced by `sorry`.
- Seven sub-agents, each owning a group of files, proved those 78 again, starting from the draft's
  proofs. An eighth checked every inequality and derivative formula of the analytic argument
  numerically and compared the definitions with formal-conjectures' file, and a ninth cleaned up the
  documentation and the warnings. At most eight ran at the same time.
- The coordinating agent moved the definitions of the Challenge into [`ChallengeDefs.lean`](ChallengeDefs.lean), so that
  Comparator can check formal-conjectures' statements, and wrote the documents.
- **Time.** About 1 hour of elapsed time, from 2026-10-02 23:05 to 2026-10-03 00:02 (US Central Time),
  up to the documented proof (commit `dc408ab`). The sub-agents worked about 1.3 hours in total. All
  agents together made 561 tool calls (444 of them by sub-agents), generated 0.6 million output tokens
  and read 1.7 million input tokens, plus 129 million tokens from the prompt cache.

### Consolidating

Claude Opus 5.5 (model `claude-opus-5-5`), in a later session of Claude Code 2.1.287, simplified and
reorganized the uniqueness and bridge libraries:

- the 75 files of the two libraries became 12 modules, one per step of the argument; the
  declarations that no final theorem uses, the regression tests and the lemmas that only renamed
  others were removed (10,428 lines became 8,469);
- the connection with formal-conjectures became the bridge library, which relates the definitions
  only; the Challenge states its three theorems, and the Solution derives formal-conjectures'
  statements from Baek's through them;
- the Challenge's namespaces became `Baek`, `Bridge` and `FormalConjectures.MovingSofa`;
- one sub-agent rewrote the documentation of the uniqueness modules, leaving their code unchanged.
- **Time.** About 1 hour 15 minutes of elapsed time, on 2026-10-03 from 07:48 to 09:03 (US Central
  Time). The sub-agent worked about 0.4 hours. All agents together made about 230 tool calls,
  generated 0.4 million output tokens and read 1.4 million input tokens, plus 85 million tokens from
  the prompt cache.

## Building

```sh
lake exe cache get        # download Mathlib's compiled files
lake build                # builds the three libraries, Challenge and Solution
lake env lean scripts/Audit.lean
```

The toolchain is `leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](lean-toolchain)), and Mathlib is pinned to its
release tag `v4.35.0-rc3`, with the exact revision in [`lake-manifest.json`](lake-manifest.json). Keep Mathlib on
the release tag that matches the toolchain: Palomar renders the Challenge with Verso's release for the
same toolchain, and the render fails when a package that Mathlib and Verso share, such as `plausible`,
is pinned at two different revisions, as it soon is on Mathlib `master`.

Two Lean files are generated by scripts, which reproduce them exactly:

- [`MovingSofaOptimality/External/Romik/Num.lean`](MovingSofaOptimality/External/Romik/Num.lean): `python3 scripts/romik/mk_num.py`;
- [`MovingSofaOptimality/Gerver/AreaBounds.lean`](MovingSofaOptimality/Gerver/AreaBounds.lean): `cd scripts/area && python3 gen.py emit ../../MovingSofaOptimality/Gerver/AreaBounds.lean`.

Both need Python 3 with SymPy and mpmath.

After changing the code, update the links from the documents to the code with
`python3 scripts/linkify_docs.py`, which reads the `.ilean` files that `lake build` writes. Check the
Markdown tables with `python3 scripts/check_md_tables.py README.md REPORT.md docs/UNIQUENESS.md
docs/BRIDGE.md`. After changing `ChallengeDefs.lean`, copy its definitions into the
Challenge with `python3 scripts/sync_challenge_defs.py`.

## Layout

### `MovingSofaOptimality/`: Baek's paper

| Module | Paper content |
| --- | --- |
| [`MovingSofaOptimality/Basic/Plane.lean`](MovingSofaOptimality/Basic/Plane.lean) | the plane: unit vectors, dot and cross products, rotations, lines, half-planes, area |
| [`MovingSofaOptimality/Basic/ConvexBody.lean`](MovingSofaOptimality/Basic/ConvexBody.lean) | §2.1: convex bodies, support functions, edges and vertices, Hausdorff distance, Theorem 2.1.3 |
| [`MovingSofaOptimality/Basic/LebesgueStieltjes.lean`](MovingSofaOptimality/Basic/LebesgueStieltjes.lean) | §5.1: Lebesgue–Stieltjes measures and integrals |
| [`MovingSofaOptimality/Basic/SurfaceArea.lean`](MovingSofaOptimality/Basic/SurfaceArea.lean) | the surface area measure σ_K, Proposition 2.1.2, §5.2 |
| [`MovingSofaOptimality/Sofa/Defs.lean`](MovingSofaOptimality/Sofa/Defs.lean) | Chapter 1 and §2.2–2.3: hallways, moving sofas, supporting hallways, monotone sofas |
| [`MovingSofaOptimality/Intro/RotationAngleBound.lean`](MovingSofaOptimality/Intro/RotationAngleBound.lean) | Theorem 1.5.1 |
| [`MovingSofaOptimality/Monotone/`](MovingSofaOptimality/Monotone) | §2.2–2.5: supporting hallways, monotonization, caps and niches |
| [`MovingSofaOptimality/Balanced/`](MovingSofaOptimality/Balanced) | Chapter 3: nef polygons, polygon caps, maximum polygon caps, balanced maximum sofas |
| [`MovingSofaOptimality/Angle/`](MovingSofaOptimality/Angle) | Chapter 4: the rotation angle of a balanced maximum sofa (Theorem 1.5.2) |
| [`MovingSofaOptimality/Injectivity/`](MovingSofaOptimality/Injectivity) | Chapter 6 (except Theorem 6.1.2): the injectivity condition |
| [`MovingSofaOptimality/Convex/`](MovingSofaOptimality/Convex) | Chapter 7: convex domains, curve area functionals, convex curves, Mamikon's theorem |
| [`MovingSofaOptimality/Optimality/`](MovingSofaOptimality/Optimality) | Chapter 8, §8.1–8.3 and §8.5: the upper bound 𝒬 and its variation |
| [`MovingSofaOptimality/Gerver/Defs.lean`](MovingSofaOptimality/Gerver/Defs.lean), [`MovingSofaOptimality/Gerver/Bounds.lean`](MovingSofaOptimality/Gerver/Bounds.lean) | Gerver's sofa from Romik's parameters, and enclosures of the parameters |
| [`MovingSofaOptimality/Gerver/Frame.lean`](MovingSofaOptimality/Gerver/Frame.lean), [`MovingSofaOptimality/Gerver/StructureCap.lean`](MovingSofaOptimality/Gerver/StructureCap.lean), [`MovingSofaOptimality/Gerver/Structure.lean`](MovingSofaOptimality/Gerver/Structure.lean) | Theorem 8.4.1 (except (2)), Theorem 8.4.2, Theorem 6.1.2 |
| [`MovingSofaOptimality/Gerver/Envelope.lean`](MovingSofaOptimality/Gerver/Envelope.lean), [`MovingSofaOptimality/Gerver/EnvelopeArea.lean`](MovingSofaOptimality/Gerver/EnvelopeArea.lean), [`MovingSofaOptimality/Gerver/NicheBounds.lean`](MovingSofaOptimality/Gerver/NicheBounds.lean), [`MovingSofaOptimality/Gerver/Niche.lean`](MovingSofaOptimality/Gerver/Niche.lean) | Theorem 8.4.1 (2): the niche of Gerver's sofa and its area |
| [`MovingSofaOptimality/Gerver/AreaBounds.lean`](MovingSofaOptimality/Gerver/AreaBounds.lean) | the bound \|G\| ≥ 2.2 |
| [`MovingSofaOptimality/Gerver/Properties.lean`](MovingSofaOptimality/Gerver/Properties.lean) | §8.4: Theorems 8.4.1–8.4.6, Proposition 8.4.4 |
| [`MovingSofaOptimality/Main.lean`](MovingSofaOptimality/Main.lean) | Definition 8.1.2, Theorem 8.1.1 (2)–(3), Theorem 8.5.7, Corollary 8.5.8, Theorem 1.1.1 |
| [`MovingSofaOptimality/External/AreaFormula.lean`](MovingSofaOptimality/External/AreaFormula.lean), [`MovingSofaOptimality/External/AreaFormula/`](MovingSofaOptimality/External/AreaFormula) | Schneider's area formula (Remark 5.1.2 of *Convex Bodies*) |
| [`MovingSofaOptimality/External/Romik.lean`](MovingSofaOptimality/External/Romik.lean), [`MovingSofaOptimality/External/Romik/`](MovingSofaOptimality/External/Romik) | Romik's system: existence, uniqueness and enclosures of its solution |

### `MovingSofaUniqueness/`: the uniqueness of Gerver's sofa

| Module | Content (propositions of [note 20](docs/uniqueness/20-complete-paper-proof.md)) |
| --- | --- |
| [`MovingSofaUniqueness/Rigid.lean`](MovingSofaUniqueness/Rigid.lean) | rigid maps, and the recovery of a closed set from a regular closed superset of the same area |
| [`MovingSofaUniqueness/Selection.lean`](MovingSofaUniqueness/Selection.lean) | Proposition 1: polygon caps converging to a given maximizing cap |
| [`MovingSofaUniqueness/Variation.lean`](MovingSofaUniqueness/Variation.lean) | Proposition 2 and the bounds (19): variations of the selected polygons and their limits |
| [`MovingSofaUniqueness/Curvature.lean`](MovingSofaUniqueness/Curvature.lean) | Proposition 3: curvature bounds and the injectivity condition for every maximizing right-angle cap |
| [`MovingSofaUniqueness/AngleExtension.lean`](MovingSofaUniqueness/AngleExtension.lean) | Proposition 4: the right-angle motion of the same sofa |
| [`MovingSofaUniqueness/Rigidity.lean`](MovingSofaUniqueness/Rigidity.lean) | Proposition 5: equality in Mamikon's terms, and Gerver's cap up to a horizontal translation |
| [`MovingSofaUniqueness/RegularClosed.lean`](MovingSofaUniqueness/RegularClosed.lean) | Proposition 6: Gerver's sofa is the closure of its interior |
| [`MovingSofaUniqueness/Main.lean`](MovingSofaUniqueness/Main.lean) | the theorem |

### `MovingSofaBridge/`: the bridge to formal-conjectures

| Module | Content |
| --- | --- |
| [`MovingSofaBridge/GerverConstants.lean`](MovingSofaBridge/GerverConstants.lean) | Gerver's four constants are unique, by elementary inequalities |
| [`MovingSofaBridge/RomikParams.lean`](MovingSofaBridge/RomikParams.lean) | Gerver's four constants and Romik's parameters; the constants exist |
| [`MovingSofaBridge/Motion.lean`](MovingSofaBridge/Motion.lean) | the two notions of moving sofa agree, and so do the two optimal areas |
| [`MovingSofaBridge/GerverSofa.lean`](MovingSofaBridge/GerverSofa.lean) | the two Gerver's sofas are the same set |

### Other files

| File | Content |
| --- | --- |
| [`Challenge.lean`](Challenge.lean), [`Solution.lean`](Solution.lean) | the statements of record and their proofs |
| [`ChallengeDefs.lean`](ChallengeDefs.lean) | the definitions that the Challenge copies |
| [`docs/`](docs) | the uniqueness proof ([`docs/UNIQUENESS.md`](docs/UNIQUENESS.md), and ChatGPT Pro's notes in [`docs/uniqueness/`](docs/uniqueness)) and the bridge ([`docs/BRIDGE.md`](docs/BRIDGE.md)) |
| [`scripts/`](scripts) | the axiom audit, the generators of the two generated files, the documentation tools |

## GitHub configuration

`.github/workflows/lean_action_ci.yml` builds the project on every push and pull request, runs the
axiom audit, and checks that the documentation's links and tables are current. It needs no settings.

## License

Apache-2.0 ([`LICENSE`](LICENSE)).
