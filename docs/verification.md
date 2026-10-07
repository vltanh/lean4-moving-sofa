# Verification

[Back to the README](../README.md)

```sh
lake exe cache get                                  # Mathlib's compiled files
lake build                                          # the five libraries, Challenge and the Solutions
lake env lean scripts/Audit.lean                    # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
                                                    # the proofs follow the routes of Baek's proofs
lake env lean scripts/AuditMaximizerRoute.lean      # the second proof of optimality avoids Baek's theorem
lake env lean scripts/AuditCoerciveRoute.lean       # the coercive route avoids it and the first uniqueness proof
python3 scripts/sync_challenge_defs.py --check      # the Challenge's copy of the definitions
lake env lake comparator --config=comparator.json   # the Solution proves the Challenge
lake env lake comparator --config=comparator-coercive.json
                                                    # so does the second solution, through the coercive route
```

Needs [elan](https://github.com/leanprover/elan) and network access for Mathlib, and
[bubblewrap](https://github.com/containers/bubblewrap) for Comparator. The toolchain is `leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](../lean-toolchain)),
and Mathlib is pinned to its release tag `v4.35.0-rc3`, with the exact revision in
[`lake-manifest.json`](../lake-manifest.json). Every proof is complete and rests on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
alone.

- `lake build` must succeed, and its only warnings are the fifteen `declaration uses 'sorry'` of
  [`Challenge.lean`](../Challenge.lean), whose theorems are the statements of record.
- [`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the five libraries and of
  [`SolutionCoercive.lean`](../SolutionCoercive.lean) (5,868 declarations), and of the theorems of [`Solution.lean`](../Solution.lean), and fails unless each one uses only the three standard axioms: an
  unproved lemma would add `sorryAx`, and `native_decide`, which trusts the compiler,
  `Lean.ofReduceBool`. It also prints, for each numbered result of Baek's paper, each step of the
  uniqueness proof, each bridge theorem, the main stability theorems and the theorems of the coercive
  route, the results from prior work that its proof uses.
  It reaches the proofs through one `import all` line per module (the module system hides proofs
  from a plain import), and CI checks that these lines name exactly the modules of the five
  libraries.
- The audit also writes the *route* of every numbered result of Baek's paper: the other numbered
  results that its Lean proof uses. `python3 scripts/route_check.py check docs/paper_routes.tsv
  --accept docs/route_differences.tsv` compares the routes with the results that the paper's own
  proofs cite, which [`docs/paper_routes.tsv`](paper_routes.tsv) records (extracted from the
  paper's LaTeX source by `route_check.py extract`). It fails on any difference that
  [`docs/route_differences.tsv`](route_differences.tsv) does not record with its reason: a result
  that the paper uses without citing it, a citation made only in passing, or a departure from the
  paper's proof, which [`REPORT.md`](../REPORT.md) lists with its reason (Section 7).
- [`scripts/AuditMaximizerRoute.lean`](../scripts/AuditMaximizerRoute.lean) checks the second proof of Baek's optimality theorem, in
  [`MovingSofaUniqueness/Maximizing.lean`](../MovingSofaUniqueness/Maximizing.lean) and [`MovingSofaUniqueness/MaximizerRoute.lean`](../MovingSofaUniqueness/MaximizerRoute.lean) (a remark at the end of Section 8 of the
  [manuscript](paper/README.md)), 35 declarations. It fails if a declaration of these modules uses an axiom other than the three
  standard ones, or if, following the proofs through the whole library without stopping at numbered results, it
  reaches Baek's Theorem 1.1.1, the results from which Baek derives the right-angle motion and the injectivity
  condition of Baek's cap from its balance (Theorems 1.5.2, 4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6,
  Corollary 6.4.4 and Theorem 8.1.1 (2)), or a declaration of [`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean). Negative controls
  check that the traversal finds these results in the first proof.
- [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) checks the coercive route ([the coercive route](coercive.md)): every declaration
  of [`MovingSofaExtremal/`](../MovingSofaExtremal), [`MovingSofaStability/`](../MovingSofaStability) and [`SolutionCoercive.lean`](../SolutionCoercive.lean), 743 with the private and generated
  ones. It fails if one of them uses an axiom other than the three standard ones, or if, following the proofs
  through all the repository's declarations, it reaches Baek's Theorem 1.1.1, the results of his balance argument
  listed above, a declaration of [`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean) or [`MovingSofaUniqueness.Rigidity`](../MovingSofaUniqueness/Rigidity.lean) (the first proof of
  uniqueness), of the second proof of optimality ([`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean)), or of [`Solution.lean`](../Solution.lean). It also fails if
  one of the 41 declarations of the route's optimality and uniqueness ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean),
  [`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean)) reaches the stability proof after the certificate, which uses them
  ([`MovingSofaStability.Margins`](../MovingSofaStability/Margins.lean) and the eleven modules that import it),
  if one of twenty positive controls is missing (for example, that the uniqueness reaches the certificate
  [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120)), if one of eight negative controls fails, or if a theorem of [`SolutionCoercive.lean`](../SolutionCoercive.lean)
  does not have exactly the statement of the theorem of [`Solution.lean`](../Solution.lean) that it restates.
- `scripts/sync_challenge_defs.py --check` checks that [`Challenge.lean`](../Challenge.lean) copies the two blocks of
  definitions of [`ChallengeDefs.lean`](../ChallengeDefs.lean) word for word (without `--check`, it copies them). The Challenge may
  import only Mathlib, and Comparator compares constants by name, so the Solution states its theorems
  with the constants of [`ChallengeDefs`](../ChallengeDefs.lean), which the bridge library uses too.

## Comparator

[`comparator.json`](../comparator.json) configures Lake's Comparator, which checks in a sandbox that [`Solution.lean`](../Solution.lean) proves
exactly the fifteen statements of [`Challenge.lean`](../Challenge.lean), over identical definitions, with the three standard
axioms only, and replays the proofs through Lean's kernel and the NanoDa kernel. It must end with
`Your solution is okay!`. The second solution, [`SolutionCoercive.lean`](../SolutionCoercive.lean), names its theorems in the namespace
`CoerciveSolution`, so that the audits can load it together with [`Solution.lean`](../Solution.lean).
[`SolutionCoerciveComparator.lean`](../SolutionCoerciveComparator.lean) states the same theorems under the Challenge's names, each proved by the theorem
of [`SolutionCoercive.lean`](../SolutionCoercive.lean), and [`comparator-coercive.json`](../comparator-coercive.json) has Comparator check it as it checks
[`Solution.lean`](../Solution.lean); it too must end with `Your solution is okay!`. That module declares the names that
[`Solution.lean`](../Solution.lean) declares, so no module imports both. [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) also checks that each theorem
of [`SolutionCoercive.lean`](../SolutionCoercive.lean) has exactly the statement of the theorem of [`Solution.lean`](../Solution.lean) that it restates.

## Continuous integration and the Palomar preflight

[`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) builds the project on every push and pull request, checks that the
axiom audit imports every module, runs the audit, the route check, the audits of the second proof of optimality
and of the coercive route, and the check of the Challenge's definitions, and checks that the links from the documentation
to the code are current and that the Markdown tables are well formed.
[`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml), run by hand with `gh workflow run palomar_preflight.yml --ref main`,
runs Palomar's complete mechanical verification of a commit without submitting it; its report, the
artifact `mechanical-report-preflightv05`, must say `status: pass`. It does not cover the rendering
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
