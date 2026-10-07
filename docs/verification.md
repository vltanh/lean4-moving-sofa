# Verification

[Back to the README](../README.md)

```sh
lake exe cache get                                  # Mathlib's compiled files
lake build                                          # the five libraries, the two Challenges and their Solutions
lake env lean scripts/Audit.lean                    # axioms and dependencies
python3 scripts/route_check.py check baek/paper_routes.tsv --accept baek/route_differences.tsv
                                                    # the proofs follow the routes of Baek's proofs
lake env lean scripts/AuditMaximizerRoute.lean      # the second proof of optimality avoids Baek's theorem
lake env lean scripts/AuditCoerciveRoute.lean       # the certificate entry's proofs avoid it and the first uniqueness proof
python3 scripts/sync_challenge_defs.py --check      # the Challenges' copies of the definitions
lake env lake comparator --config=comparator.json   # the certificate entry: Solution.lean proves Challenge.lean
lake env lake comparator --config=baek/comparator.json
                                                    # Baek's entry: baek/Solution.lean proves baek/Challenge.lean
```

Needs [elan](https://github.com/leanprover/elan) and network access for Mathlib, and
[bubblewrap](https://github.com/containers/bubblewrap) for Comparator. The toolchain is `leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](../lean-toolchain)),
and Mathlib is pinned to its release tag `v4.35.0-rc3`, with the exact revision in
[`lake-manifest.json`](../lake-manifest.json). Every proof is complete and rests on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound)
alone.

- `lake build` must succeed, and its only warnings are the seventeen `declaration uses 'sorry'` of
  [`Challenge.lean`](../Challenge.lean) and the twelve of [`baek/Challenge.lean`](../baek/Challenge.lean), whose theorems are the statements of record.
- [`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the five libraries (5,992 declarations),
  which hold the definitions that the Challenges copy and the proofs of the certificate entry too, and
  of the theorems that Comparator checks: the certificate entry's two theorems about the certificate, and the twelve
  of Baek's entry, as [`baek/Solution.lean`](../baek/Solution.lean) proves them. Fourteen other theorems of the certificate entry are
  restatements, in [`Solution.lean`](../Solution.lean), of theorems of [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean), whose declarations the audit checks;
  it cannot import [`Solution.lean`](../Solution.lean), which declares the names of [`baek/Solution.lean`](../baek/Solution.lean). The seventeenth,
  `ABφθSpec.existsUnique`, is the theorem of [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean) that Baek's entry uses too. The audit fails unless
  each one uses only the three standard axioms: an unproved lemma would add `sorryAx`, and `native_decide`, which
  trusts the compiler,
  `Lean.ofReduceBool`. It also prints, for each numbered result of Baek's paper, each step of the
  uniqueness proof, each bridge theorem, the main stability theorems and the theorems of the coercive
  route, the results from prior work that its proof uses.
  It reaches the proofs through one `import all` line per module (the module system hides proofs
  from a plain import), and CI checks that these lines name exactly the modules of the five
  libraries.
- The audit also writes the *route* of every numbered result of Baek's paper: the other numbered
  results that its Lean proof uses. `python3 scripts/route_check.py check baek/paper_routes.tsv
  --accept baek/route_differences.tsv` compares the routes with the results that the paper's own
  proofs cite, which [`baek/paper_routes.tsv`](../baek/paper_routes.tsv) records (extracted from the
  paper's LaTeX source by `route_check.py extract`). It fails on any difference that
  [`baek/route_differences.tsv`](../baek/route_differences.tsv) does not record with its reason: a result
  that the paper uses without citing it, a citation made only in passing, or a departure from the
  paper's proof, which [`baek/REPORT.md`](../baek/REPORT.md) lists with its reason (Section 7).
- [`scripts/AuditMaximizerRoute.lean`](../scripts/AuditMaximizerRoute.lean) checks the second proof of Baek's optimality theorem, in
  [`MovingSofaUniqueness/Maximizing.lean`](../MovingSofaUniqueness/Maximizing.lean) and [`MovingSofaUniqueness/MaximizerRoute.lean`](../MovingSofaUniqueness/MaximizerRoute.lean) (a remark at the end of Section 8 of the
  [manuscript](paper/README.md)), 35 declarations. It fails if a declaration of these modules uses an axiom other than the three
  standard ones, or if, following the proofs through the whole library without stopping at numbered results, it
  reaches Baek's Theorem 1.1.1, the results from which Baek derives the right-angle motion and the injectivity
  condition of Baek's cap from its balance (Theorems 1.5.2, 4.1.2, 4.1.4, 4.2.5, 6.1.1, 6.3.3, 6.4.3, 6.5.6,
  Corollary 6.4.4 and Theorem 8.1.1 (2)), or a declaration of [`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean). Negative controls
  check that the traversal finds these results in the first proof.
- [`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) checks the proofs of the certificate entry ([the coercive route](coercive.md)): every
  declaration of [`MovingSofaExtremal/`](../MovingSofaExtremal), which holds the certificate entry's proofs, and of [`MovingSofaStability/`](../MovingSofaStability), 867 with
  the private and generated ones. It fails if one of them uses an axiom other than the three standard ones, or
  if, following the proofs through all the repository's declarations, it
  reaches Baek's Theorem 1.1.1, the results of his balance argument listed above, a declaration of [`MovingSofaUniqueness.Main`](../MovingSofaUniqueness/Main.lean) or [`MovingSofaUniqueness.Rigidity`](../MovingSofaUniqueness/Rigidity.lean) (the first proof of
  uniqueness), of the second proof of optimality ([`MovingSofaUniqueness.MaximizerRoute`](../MovingSofaUniqueness/MaximizerRoute.lean)), or of [`baek/Solution.lean`](../baek/Solution.lean). It also fails if
  one of the 41 declarations of the route's optimality and uniqueness ([`MovingSofaUniqueness.Maximizing`](../MovingSofaUniqueness/Maximizing.lean),
  [`MovingSofaExtremal.Main`](../MovingSofaExtremal/Main.lean)) reaches the stability proof after the certificate, which uses them
  ([`MovingSofaStability.Margins`](../MovingSofaStability/Margins.lean) and the ten modules that import it),
  if one of twenty-two positive controls is missing (for example, that the uniqueness reaches the certificate
  [`MovingSofaStability.coercive_certificate`](../MovingSofaStability/CapEstimate.lean#L1120), and that the certificate entry's statement of the certificate does too), if one of
  eight negative controls fails, or if one of the twelve theorems that [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) shares with
  [`baek/Solution.lean`](../baek/Solution.lean) does not have exactly the statement of the theorem of [`baek/Solution.lean`](../baek/Solution.lean) that it restates.
- `scripts/sync_challenge_defs.py --check` checks that the Challenges copy marked blocks of definitions word for
  word (without `--check`, it copies them): [`Challenge.lean`](../Challenge.lean) four blocks of [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean), Baek's core
  definitions, the definitions of the stability theorems and formal-conjectures' two blocks, and the block of
  [`MovingSofaExtremal/CertificateDefs.lean`](../MovingSofaExtremal/CertificateDefs.lean); [`baek/Challenge.lean`](../baek/Challenge.lean) the same blocks of [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean) except the stability
  block ([Definitions](definitions.md)). The Challenges may import only Mathlib, and Comparator compares constants by
  name, so the Solutions state their theorems with the constants of
  [`MovingSofaBridge.Defs`](../MovingSofaBridge/Defs.lean), which the rest of the bridge library uses too, and of [`MovingSofaExtremal.CertificateDefs`](../MovingSofaExtremal/CertificateDefs.lean). The script also checks that each
  Challenge holds its blocks in the order in which the script lists them: Lean names the auxiliary theorems that it
  makes from proofs inside definitions after the first definition that needs them in a module, so a block must
  follow the same blocks in the Challenge as in the library. [`MovingSofaExtremal/CertificateDefs.lean`](../MovingSofaExtremal/CertificateDefs.lean) starts with a command that gives
  Lean's cache of auxiliary theorems the state it has in [`Challenge.lean`](../Challenge.lean) after the blocks of
  [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean), so that its block elaborates to the same terms in both.

## Comparator

Lake's Comparator checks in a sandbox that a Solution proves exactly the statements of a Challenge, over identical
definitions, with the three standard axioms only, and replays the proofs through Lean's kernel and the NanoDa
kernel. Each of the two configurations must end with `Your solution is okay!`:

- [`comparator.json`](../comparator.json), the certificate entry: [`Solution.lean`](../Solution.lean) proves the seventeen statements of
  [`Challenge.lean`](../Challenge.lean).
- [`baek/comparator.json`](../baek/comparator.json), Baek's entry: [`baek/Solution.lean`](../baek/Solution.lean) proves the twelve statements of [`baek/Challenge.lean`](../baek/Challenge.lean).

[`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) proves fifteen theorems of the certificate entry in the namespace `CoerciveSolution`, so that
the audits can load it together with [`baek/Solution.lean`](../baek/Solution.lean). [`Solution.lean`](../Solution.lean) states fourteen of them under the
Challenge's names, each proved by the matching theorem of [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean), and takes
`ABφθSpec.existsUnique` from [`MovingSofaBridge/Defs.lean`](../MovingSofaBridge/Defs.lean) and the two theorems about the certificate from
[`MovingSofaExtremal/Certificate.lean`](../MovingSofaExtremal/Certificate.lean). It declares the names that [`baek/Solution.lean`](../baek/Solution.lean) declares, so no module imports it.
[`scripts/AuditCoerciveRoute.lean`](../scripts/AuditCoerciveRoute.lean) also checks that the twelve theorems that [`MovingSofaExtremal/Statements.lean`](../MovingSofaExtremal/Statements.lean) shares with
[`baek/Solution.lean`](../baek/Solution.lean) have exactly the same statements.

## Continuous integration and the Palomar preflight

[`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) builds the project on every push and pull request, checks that the
axiom audit imports every module of the five libraries, runs the audit, the route check, the audits of the second
proof of optimality and of the coercive route, and the check of the Challenges' definitions, and checks that the
links from the documentation to the code are current and that the Markdown tables are well formed.

[`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml), run by hand, runs Palomar's complete mechanical verification of a commit
without submitting it. Its inputs choose the entry: the Comparator configuration, the metadata, whose file name
must be formalization.yaml, and a request id of exactly 12 lowercase letters or digits. Without inputs it checks the
certificate entry ([`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml), request id `preflightc01`); the second command checks
Baek's entry:

```sh
gh workflow run palomar_preflight.yml --ref main
gh workflow run palomar_preflight.yml --ref main -f comparator_config_path=baek/comparator.json \
  -f formalization_metadata_path=baek/formalization.yaml -f request_id=preflightb05
```

The report, the artifact `mechanical-report-` followed by the request id (`mechanical-report-preflightc01` for
the certificate entry), must say `status: pass`. It does not cover the rendering of the Challenge, which Palomar runs after
verification with Verso: keep Mathlib on the release tag that matches the toolchain, since the render fails when a
package that Mathlib and Verso share, such as `plausible`, is pinned at two different revisions, as it soon is on
Mathlib `master`.

## The documentation

The README and the pages of [`docs/`](.), [`baek/`](../baek) and [`baek/proof/`](../baek/proof/README.md) link every Lean name they cite to its
declaration, by file and line.
`python3 scripts/linkify_docs.py` refreshes the links from the `.ilean` files that `lake build`
writes, and warns about a name that matches no declaration or several; CI runs it with `--check`. A name that a
Challenge and a Solution both declare links to the Challenge, the root's [`Challenge.lean`](../Challenge.lean) before [`baek/Challenge.lean`](../baek/Challenge.lean).
`python3 scripts/check_md_tables.py README.md baek/*.md baek/proof/*.md docs/*.md` finds table rows
that a `|` inside a cell would break. [`docs/archive/`](archive) is kept as it was.

`python3 scripts/figures/make_all.py` redraws every figure of the text, in
[`baek/proof/figures/`](../baek/proof/figures). Each chapter's figures come from its module `scripts/figures/fig_<chapter>.py`;
[`scripts/figures/gerver.py`](../scripts/figures/gerver.py) computes Gerver's sofa from the formalization's definitions, and checks its area,
`2.21954` with the default grid, against Gerver's `2.21953…`.

## Generated Lean files

Two Lean files of interval arithmetic are written by scripts, which reproduce them exactly; both need
Python 3 with SymPy and mpmath:

- [`MovingSofaOptimality/External/Romik/Num.lean`](../MovingSofaOptimality/External/Romik/Num.lean): `python3 scripts/romik/mk_num.py`;
- [`MovingSofaOptimality/Gerver/AreaBounds.lean`](../MovingSofaOptimality/Gerver/AreaBounds.lean):
  `cd scripts/area && python3 gen.py emit ../../MovingSofaOptimality/Gerver/AreaBounds.lean`.

[Appendix B](../baek/proof/appendix-b.md) of the text explains what they prove.
