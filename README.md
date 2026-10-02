# Optimality of Gerver's sofa, in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml)

The moving sofa problem asks for the planar shape of largest area that can be moved around the
right-angled corner of a hallway of unit width. Jineon Baek, *Optimality of Gerver's Sofa*
([arXiv:2411.19826v1](https://arxiv.org/abs/2411.19826v1)), proves that Gerver's sofa, of area
2.21953…, is optimal. This repository formalizes the whole proof in Lean 4 with Mathlib:

- every result the paper proves;
- the results it takes from the literature;
- the structure of Gerver's sofa (Theorem 8.4.1), which the paper states without proof.

## What is proved

- **All numbered results of the paper** (Chapters 1–8), proved along the paper's arguments, and the
  main theorem, Theorem 1.1.1 ([`theorem1_1_1`](MovingSofa/Main.lean#L318)). Where the paper's statements contain slips, the
  intended statements are proved. [`REPORT.md`](REPORT.md) lists every correction; no result had to be weakened.
- **The cited results used in proofs:**
  - Schneider's area formula \|K\| = ½ ∫ h_K dσ_K for planar convex bodies ([`area_eq_half_integral_supp`](MovingSofa/External/AreaFormula.lean#L592),
    in [`MovingSofa/External/`](MovingSofa/External));
  - the existence and uniqueness of the solution of Romik's system of equations that defines Gerver's
    sofa ([`GerverParams.romik_exists`](MovingSofa/External/Romik.lean#L387), [`GerverParams.romik_unique`](MovingSofa/External/Romik.lean#L393), also in [`MovingSofa/External/`](MovingSofa/External));
  - the facts the paper cites from convex geometry and measure theory, which are proved where they
    are used or come from Mathlib.
- **The structure of Gerver's sofa** (Theorem 8.4.1, and with it Theorems 6.1.2 and 8.4.2), and its area,
  between 2.2192 and 2.2199, proved from Romik's equations by rigorous interval arithmetic.
- **Status:** `lake build` succeeds, and the only `sorry`s are the four statements of [`Challenge.lean`](Challenge.lean).
  There are no `axiom`s, and [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). Run it with `lake env lean scripts/Audit.lean`; it also prints,
  for each result of the paper, the results from prior work that its proof uses.

## The main results

[`Challenge.lean`](Challenge.lean) states the results in Mathlib's vocabulary only, with its own copies of the
definitions (the hallway, moving sofas, Romik's parameters and Gerver's sofa), so that it can be read
without the rest of the repository. [`Solution.lean`](Solution.lean) proves them from the library.

- [`gerver_params_exists`](Challenge.lean#L162) and [`gerver_params_unique`](Challenge.lean#L166): Romik's system of equations (27)–(44) has exactly
  one solution with φ ∈ [0.039, 0.04] and θ ∈ [0.68, 0.69]. So Gerver's sofa, the shape of the rotation
  path these parameters define, is well defined.
- [`gerver_sofa_area`](Challenge.lean#L172): Gerver's sofa has area between 2.2192 and 2.2199. Gerver's value is 2.21953…;
  this ties the shape defined from Romik's parameters to the sofa Gerver found.
- [`gerver_sofa_optimal`](Challenge.lean#L178): Gerver's sofa is a moving sofa, and every moving sofa has area at most the area
  of Gerver's sofa (Theorem 1.1.1).

[`comparator.json`](comparator.json) configures Lake's Comparator, which checks in a sandbox that [`Solution.lean`](Solution.lean) proves
exactly the statements of [`Challenge.lean`](Challenge.lean) with the standard axioms only:

```sh
sed 's/"enable_nanoda": true/"enable_nanoda": false/' comparator.json > /tmp/comparator-local.json
lake comparator --config=/tmp/comparator-local.json
```

## Palomar

The repository is packaged for the [Palomar](https://palomar-registry.org) registry of machine-checked
proofs:

- [`Challenge.lean`](Challenge.lean) holds the statements of record;
- [`Solution.lean`](Solution.lean) holds their proofs;
- [`comparator.json`](comparator.json) selects the four compared theorems;
- [`formalization.yaml`](formalization.yaml) records the metadata: sources, scope, divergences from the
  paper, automation and review;
- [`LICENSE`](LICENSE) holds the licence.

The workflow [`.github/workflows/palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs
Palomar's complete mechanical verification on a commit, on demand. It is pinned to a fixed commit of
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission). Run it with
`gh workflow run palomar_preflight.yml --ref main`; it publishes its report as the artifact
`mechanical-report-preflight001`.

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

Two independent Lean 4 formalizations of Baek's proof existed before this one:
[RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal) and
[deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), the latter written by AI coding
agents directed by Dean Cureton. This repository was developed without consulting either, shares no
code with them, and has not been compared with them in detail. Relative to the paper, it adds:
- an audit of the paper against its LaTeX source ([`REPORT.md`](REPORT.md));
- a proof that Romik's system has exactly one solution in the stated box (Romik asserts uniqueness
  without proof);
- a proof of Theorem 8.4.1, which the paper states without proof. For the niche, part (2), the proof
  reduces a two-parameter family of inequalities to one-variable inequalities verified by interval
  arithmetic.

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
Opus 5.5 (Anthropic, model `claude-opus-5-5`), running in Claude Code 2.1.285, at the request of
The-Anh Vu-Le, who is the author and maintainer of this repository. No human has reviewed the proofs;
Lean's kernel checks every one of them.

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
