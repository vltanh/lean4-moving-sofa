# Optimality and uniqueness of Gerver's sofa, in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-moving-sofa/actions/workflows/lean_action_ci.yml)
[![Palomar](https://img.shields.io/badge/Palomar-registered-blue)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000008)

The moving sofa problem asks for the largest area of a shape that can be moved around the
right-angled corner of a hallway of unit width. This repository proves, in Lean 4 with Mathlib, that
Gerver's sofa, of area 2.21953…, has the largest area, and that it is the only shape that does, up to
rigid motions:

- **optimality:** the whole of Jineon Baek's proof, *Optimality of Gerver's Sofa*
  ([arXiv:2411.19826v1](https://arxiv.org/abs/2411.19826v1)), with the results it takes from the literature and the
  structure of Gerver's sofa (Theorem 8.4.1), which the paper states without proof;
- **uniqueness:** every moving sofa with the area of Gerver's sofa is mapped onto it by a rotation
  and a translation. Baek's paper does not prove this, and Google DeepMind's formal-conjectures lists
  it as open. The argument was written by ChatGPT Pro 6 for this repository and has not been peer
  reviewed;
- **the bridge to formal-conjectures:** formal-conjectures states the problem with definitions of its
  own, which describe the same moving sofas, the same optimal area and the same Gerver's sofa as
  Baek's. Its statements, the open one included, follow from the first two results.

![Gerver's sofa sliding along the horizontal side of the hallway, turning the corner, and leaving along the vertical side](docs/proof/figures/01-introduction/gerver-moving.gif)

## Definitions

More on each definition: [docs/definitions.md](docs/definitions.md).

Read these before trusting the results: Lean's kernel checks the proofs, not that the statements mean
what you intend. [`Challenge.lean`](Challenge.lean) states the results with Mathlib's vocabulary and two sets of
definitions, Baek's and formal-conjectures'.

Baek's (namespace `Baek`): the plane is `ℝ × ℝ`, and the hallway is the union of its horizontal side
`(-∞, 1] × [0, 1]` and its vertical side `[0, 1] × (-∞, 1]`. A moving sofa is a closed, connected set
that a continuous rotation angle `θ` and translation `c`, starting at a translation, carry from the
horizontal side to the vertical side without leaving the hallway:

```lean
def IsMovingSofa (S : Set (ℝ × ℝ)) : Prop :=
  IsClosed S ∧ IsConnected S ∧
    ∃ (θ : ℝ → ℝ) (c : ℝ → ℝ × ℝ), ContinuousOn θ (Icc 0 1) ∧ ContinuousOn c (Icc 0 1) ∧
      θ 0 = 0 ∧ (∀ p ∈ S, rot (θ 0) p + c 0 ∈ horizSide) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ p ∈ S, rot (θ s) p + c s ∈ hallway) ∧
      (∀ p ∈ S, rot (θ 1) p + c 1 ∈ vertSide)
```

Gerver's sofa follows Romik's description of it. Seen from the sofa, the hallway turns around it,
and its inner corner traces a *rotation path* `x(t)`, `0 ≤ t ≤ π/2`, glued from five explicit curves
whose 22 parameters solve Romik's equations. The sofa is the set of points that stay in every moved
hallway:

```lean
def shapeOfPath (x : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  horizSide ∩ (⋂ t ∈ Icc 0 (π / 2), (fun p => x t + rot t p) '' hallway) ∩
    (fun p => x (π / 2) + rot (π / 2) p) '' vertSide

def gerverSofa (P : GerverParams) : Set (ℝ × ℝ) := shapeOfPath P.path
```

formal-conjectures' (namespace `FormalConjectures.MovingSofa`, with formal-conjectures' code): moving sofas in
`EuclideanSpace ℝ (Fin 2)`, moved by continuous paths of isometries that start at the identity; the
sofa constant, the supremum of their areas; and Gerver's sofa, from Gerver's four constants.

## Results

More on each theorem: [docs/results.md](docs/results.md).

[`Solution.lean`](Solution.lean) proves the twelve theorems of [`Challenge.lean`](Challenge.lean). The three main ones:

```lean
theorem Baek.gerver_sofa_optimal (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox) :
    IsMovingSofa (gerverSofa P) ∧ ∀ S, IsMovingSofa S → volume S ≤ volume (gerverSofa P)

theorem Baek.gerver_sofa_unique (P : GerverParams) (hP : P.IsSolution) (hPb : P.InBox)
    (S : Set (ℝ × ℝ)) (hS : IsMovingSofa S) (harea : volume S = volume (gerverSofa P)) :
    ∃ (θ : ℝ) (v : ℝ × ℝ), (fun p => rot θ p + v) '' S = gerverSofa P

theorem FormalConjectures.MovingSofa.volume_eq_sofaConstant_iff_congruent_gerversSofa
    (s : Set ℝ²) (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa
```

- In `Baek`: Romik's equations have exactly one solution in a small box around Romik's numerical
  one, so Gerver's sofa is well defined ([`Baek.gerver_params_exists`](Challenge.lean#L332), [`Baek.gerver_params_unique`](Challenge.lean#L336)). Its area lies
  between 2.2192 and 2.2199 ([`Baek.gerver_sofa_area`](Challenge.lean#L342)). It is optimal ([`Baek.gerver_sofa_optimal`](Challenge.lean#L348), Baek's Theorem
  1.1.1) and unique up to rigid motions ([`Baek.gerver_sofa_unique`](Challenge.lean#L355)).
- In `Bridge`: the two notions of moving sofa agree ([`Bridge.isMovingSofa_iff`](Challenge.lean#L367)), the sofa constant is
  the supremum of the areas of Baek's moving sofas ([`Bridge.sofaConstant_eq`](Challenge.lean#L375)), and the two Gerver's sofas
  are the same set ([`Bridge.gerversSofa_eq`](Challenge.lean#L383)).
- In `FormalConjectures.MovingSofa`: formal-conjectures' four statements, among them the open one
  above, derived from the theorems of `Baek` and `Bridge`.

## Proof outline

The proofs are written out as an illustrated textbook, every numbered result linked to its Lean
declarations: [docs/proof/](docs/proof/README.md).

- **Optimality** ([Chapters 2 to 10](docs/proof/02-preliminaries.md)). A maximum sofa can be taken
  *monotone*: a convex *cap* minus the *niche* that the hallway's inner corner carves out of it.
  Limits of maximum polygon sofas give a *balanced* maximum sofa, which turns through a full right
  angle, and a differential inequality shows that the hallway's inner corner, seen from the sofa,
  moves steadily leftward and so never crosses its own path: the *injectivity condition*. Under that condition Baek's upper bound $\mathcal{Q}$, a quadratic
  functional of three convex bodies, is concave by Mamikon's theorem, and Gerver's sofa maximizes it
  and has area equal to it.
- **Uniqueness** ([Chapters 11 and 12](docs/proof/11-selection.md)). Baek's argument gives the right-angle turn
  and the injectivity condition only to a maximum chosen by compactness. The uniqueness proof
  approximates a given maximum by polygon maximizers of a penalized problem; their balance passes to
  the limit as bounds on curvature, which give the given sofa both properties. Equality in Baek's
  bound then forces equality in each of Mamikon's terms, which makes the monotone sofa a horizontal
  translate of Gerver's; Gerver's sofa is the closure of its interior, which recovers the given set.
- **The bridge** ([Chapter 13](docs/proof/13-bridge.md), [Appendix A](docs/proof/appendix-a.md)). A continuous path of isometries
  from the identity consists of rotations whose angle lifts to a continuous function, which matches
  the two notions of moving sofa. Gerver's four constants are unique by elementary inequalities; they
  are read off Romik's parameters; and formal-conjectures' integrals are the coordinates of Romik's
  rotation path, which matches the two Gerver's sofas.

## The audit of Baek's paper

[`REPORT.md`](REPORT.md) audits the paper against its LaTeX source and the formalization. Definition 3.2.5
uses the parallelogram $P_\omega$ where the fan $F_\omega$ is meant, which makes Proposition 3.3.5 and
Lemma 3.4.2 false as written (E6), and one direction of Proposition 5.1.4 is false (E11). Theorem
8.4.1 has no proof (E24), and the proof of Theorem 6.1.2 misreads Gerver's Theorem 2 (E12). Two
statements need a hypothesis that the paper leaves out: Schneider's theorem on the surface area
measure, as the paper states it, needs convex bodies with interior points, and Theorem 3.1.2 needs a
bounded Nef polygon; every use satisfies both. Every result holds in its intended form, the main
theorem included, and the formalization proves it. Twelve of the findings come from the notes of
another formalization, deancureton/MovingSofa, and are credited in the report.

Every proof follows Baek's argument, except at the steps that REPORT.md lists in Section 7, each
forced by an error or gap of the paper (E12, E15, E17, E20, E21, E24), by mathematics that
Mathlib lacks (the Jordan curve theorem and Green's theorem, the Brunn–Minkowski inequality, mixed
volumes), or by the definition of the surface area measure as a Lebesgue–Stieltjes measure. A route
check in CI compares the results that each Lean proof uses with those that Baek's proof cites, and
[`docs/route_differences.tsv`](docs/route_differences.tsv) gives the reason for every difference.

## Prior work

More on each earlier result, with references: [docs/prior-work.md](docs/prior-work.md).

- Moser posed the problem in 1966. Hammersley found a sofa of area $\pi/2 + 2/\pi \approx 2.2074$;
  Gerver found the sofa in 1992 and conjectured that it is optimal; Romik derived it from differential
  equations in 2018; Kallus and Romik proved by computer that the maximum is at most 2.37.
- Baek proved Gerver's conjecture in 2024. That Gerver's sofa is the only optimal sofa is stated as
  open in formal-conjectures; we know of no earlier proof.
- Concurrent with Baek's paper, in 2024: Baek's own conditional bound 1 + π²/8 for sofas with the
  injectivity condition (arXiv:2406.10725, superseded by the paper), numerical evidence by neural
  networks that Gerver's sofa is the global maximum (Leng, Bi, Cha, Pinilla and Thiyagalingam,
  arXiv:2407.11106), and a calculus of variations approach that recovers Gerver's sofa under
  convexity assumptions (Deng, arXiv:2407.02587).
- Two Lean formalizations of Baek's proof appeared shortly before this one,
  [deancureton/MovingSofa](https://github.com/deancureton/MovingSofa) and [RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal). Both prove
  formal-conjectures' statement of the optimality; [docs/formalizations.md](docs/formalizations.md) compares the three.

## What's next

Baek's paper is still a preprint (arXiv version 1), reported in 2026 to be under review. No erratum
or counterexample has appeared; the other formalizations, like this audit, found only repairable
errors and gaps in its proofs. Since it appeared, two other Lean formalizations and this one have
verified its result, and preprints have studied a three-dimensional sofa by computer search,
rectangular sofas, and corridors with other corner angles; another Lean formalization bounds the area
of sofas that turn both ways. The report's
[What's next](REPORT.md#10-whats-next) also lists open directions (stability, other angles, the
ambidextrous sofa) and simpler arguments for several of Baek's proofs that came up while formalizing
them.

## Layout

More on each file: [docs/layout.md](docs/layout.md).

```text
Challenge.lean            the statements of record, for the Palomar registry
ChallengeDefs.lean        the definitions that Challenge.lean copies
Solution.lean             the proofs of the statements of record
MovingSofaOptimality/     Baek's paper, one directory per chapter, with External/ for
                          the results it cites and Gerver/ for Gerver's sofa
MovingSofaUniqueness/     the uniqueness, one module per step of the argument
MovingSofaBridge/         the bridge to formal-conjectures' definitions
REPORT.md                 the audit of Baek's paper
docs/                     these pages, the illustrated text (docs/proof/) and the
                          archived notes of the uniqueness proof (docs/archive/)
scripts/                  the axiom audit, generators, documentation tools, figures
```

## Verification

More on each check: [docs/verification.md](docs/verification.md).

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
lake env lake comparator --config=comparator.json
```

The build uses Lean and Mathlib `v4.35.0-rc3`, pinned by [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).
`lake build` succeeds, and its only `sorry`s are the twelve statements of [`Challenge.lean`](Challenge.lean). The audit
checks that every declaration of the three libraries uses only the axioms [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
[`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound); the route check, that every proof of a result of Baek's paper uses the
results that Baek's proof cites, except the differences recorded with their reasons; and Comparator,
that [`Solution.lean`](Solution.lean) proves exactly the statements of [`Challenge.lean`](Challenge.lean). GitHub Actions builds the project, runs
the audit and the route check, and checks the documentation on every push.

## Palomar registry

The library is registered in the [Palomar](https://palomar-registry.org) registry as
[PALOMAR-2026-10-02-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000008): version 1 registers the optimality (commit `d0b42d2`),
and version 2 adds the uniqueness (commit `cf4feff`). Palomar checks the proofs against
[`Challenge.lean`](Challenge.lean), which imports only Mathlib; [`comparator.json`](comparator.json) selects its twelve theorems, and
[`formalization.yaml`](formalization.yaml) records provenance, authorship and AI use. The workflow
[`.github/workflows/palomar_preflight.yml`](.github/workflows/palomar_preflight.yml) runs Palomar's mechanical verification on a commit
([verification](docs/verification.md#continuous-integration-and-the-palomar-preflight)).

## License

Apache-2.0 ([`LICENSE`](LICENSE)), matching Mathlib and the Lean ecosystem.

## Credits

- Claude Opus 5.5 (Anthropic), in Claude Code, formalized Baek's paper, wrote the audit and the
  documentation with the illustrated text of the proofs, and completed the uniqueness proof and the
  bridge from uncompiled Lean drafts by ChatGPT Pro 6 (OpenAI), which also wrote the informal
  uniqueness argument. The work followed the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, at the request of
  The-Anh Vu-Le, who directed it.
- No person has reviewed the proofs; Lean's kernel checks every one of them. The work took nine
  rounds between 1 and 5 October 2026, with up to 26 sub-agents in a round.
- Who did what and when, with the time and effort of each round: [CREDITS.md](CREDITS.md).
