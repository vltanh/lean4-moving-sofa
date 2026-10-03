# Verification

[Back to the README](../README.md)

```sh
lake exe cache get                                  # Mathlib's compiled files
lake build                                          # the three libraries, Challenge and Solution
lake env lean scripts/Audit.lean                    # axioms and dependencies
python3 scripts/sync_challenge_defs.py --check      # the Challenge's copy of the definitions
lake env lake comparator --config=comparator.json   # the Solution proves the Challenge
```

Needs [elan](https://github.com/leanprover/elan) and network access for Mathlib, and
[bubblewrap](https://github.com/containers/bubblewrap) for Comparator. The toolchain is `leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](../lean-toolchain)),
and Mathlib is pinned to its release tag `v4.35.0-rc3`, with the exact revision in
[`lake-manifest.json`](../lake-manifest.json). Every proof is complete and rests on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
alone.

- `lake build` must succeed, and its only warnings are the twelve `declaration uses 'sorry'` of
  [`Challenge.lean`](../Challenge.lean), whose theorems are the statements of record.
- [`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the three libraries and of the
  theorems of [`Solution.lean`](../Solution.lean), and fails unless each one uses only the three standard axioms: an
  unproved lemma would add `sorryAx`, and `native_decide`, which trusts the compiler,
  `Lean.ofReduceBool`. It also prints, for each numbered result of Baek's paper, each step of the
  uniqueness proof and each bridge theorem, the results from prior work that its proof uses.
- `scripts/sync_challenge_defs.py --check` checks that [`Challenge.lean`](../Challenge.lean) copies the two blocks of
  definitions of [`ChallengeDefs.lean`](../ChallengeDefs.lean) word for word (without `--check`, it copies them). The Challenge may
  import only Mathlib, and Comparator compares constants by name, so the libraries and the Solution
  use the constants of [`ChallengeDefs`](../ChallengeDefs.lean).

## Comparator

[`comparator.json`](../comparator.json) configures Lake's Comparator, which checks in a sandbox that [`Solution.lean`](../Solution.lean) proves
exactly the twelve statements of [`Challenge.lean`](../Challenge.lean), over identical definitions, with the three standard
axioms only, and replays the proofs through Lean's kernel and the NanoDa kernel. It must end with
`Your solution is okay!`.

## Continuous integration and the Palomar preflight

[`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) builds the project on every push and pull request, runs the axiom
audit and the check of the Challenge's definitions, and checks that the links from the documentation
to the code are current and that the Markdown tables are well formed.
[`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml), run by hand with `gh workflow run palomar_preflight.yml --ref main`,
runs Palomar's complete mechanical verification of a commit without submitting it; its report, the
artifact `mechanical-report-preflight001`, must say `status: pass`. It does not cover the rendering
of the Challenge, which Palomar runs after verification with Verso: keep Mathlib on the release tag
that matches the toolchain, since the render fails when a package that Mathlib and Verso share, such
as `plausible`, is pinned at two different revisions, as it soon is on Mathlib `master`.

## The documentation

The pages of [`docs/`](.) and [`docs/proof/`](proof/README.md) link every Lean name they cite to its declaration, by file and line.
`python3 scripts/linkify_docs.py` refreshes the links from the `.ilean` files that `lake build`
writes, and warns about a name that matches no declaration or several; CI runs it with `--check`.
`python3 scripts/check_md_tables.py README.md REPORT.md docs/*.md docs/proof/*.md` finds table rows
that a `|` inside a cell would break. [`docs/archive/`](archive) is kept as it was.

`python3 scripts/figures/make_all.py` redraws every figure of the text, in
[`docs/proof/figures/`](proof/figures). Each chapter's figures come from its module `scripts/figures/fig_<chapter>.py`;
[`scripts/figures/gerver.py`](../scripts/figures/gerver.py) computes Gerver's sofa from the formalization's definitions, and checks its area,
`2.21954` with the default grid, against Gerver's `2.21953…`.

## Generated Lean files

Two Lean files of interval arithmetic are written by scripts, which reproduce them exactly; both need
Python 3 with SymPy and mpmath:

- [`MovingSofaOptimality/External/Romik/Num.lean`](../MovingSofaOptimality/External/Romik/Num.lean): `python3 scripts/romik/mk_num.py`;
- [`MovingSofaOptimality/Gerver/AreaBounds.lean`](../MovingSofaOptimality/Gerver/AreaBounds.lean):
  `cd scripts/area && python3 gen.py emit ../../MovingSofaOptimality/Gerver/AreaBounds.lean`.

[Appendix B](proof/appendix-b.md) of the text explains what they prove.
