# Credits

How this formalization was made, from the run log and the session transcripts. Times are US Central
Time (UTC−5). The figures come from the Claude Code session transcripts, computed with the
formalize-math-paper skill's `session_stats.py`; they do not include the work of ChatGPT Pro 6, which
was not recorded.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization of Baek's paper and
  for each later round below, and decided the scope, the names and the publication.
- **Formalization:** Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in Claude Code 2.1.285,
  2.1.287 and 2.1.289, in five sessions: the Lean code of the three libraries, the audit of the paper, the
  documents and the figures, and on 5 October the comparison of the formalizations below; on 4 October, as
  sub-agents of the session that wrote the manuscript (Claude Code 2.1.289, whose main agent is Claude Sonnet 5.5),
  the extension of the libraries below; and on 5 and 6 October, in another session of Claude Code 2.1.289, the
  merge of the second proof of optimality below, the compilation of the stability proof, the compilation and
  completion of the coercive route, the simplification of the new libraries, and the merge of this work into main.
  ChatGPT Pro 6 (OpenAI) wrote the informal uniqueness argument and uncompiled Lean drafts of the
  uniqueness proof and of the connection with formal-conjectures, and on 5 October the uncompiled
  Lean modules of a second proof of Baek's theorem (pull request #5), the stability argument
  with its uncompiled Lean code (pull request #8), and the coercive route with its uncompiled Lean
  code (pull request #9).
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill:
  commit `cbdedac` for Baek's paper, versions 1.3.0 and 1.3.1 for the rounds up to the
  simplification, version 1.4.0 for following Baek's proofs, and versions 2.1.0 and 2.1.1 for the later rounds.
- **Review:** no person has reviewed the proofs; Lean's kernel checks every one of them. Independent
  agents checked the statements against the paper's LaTeX source before any proof was written, the
  audit's findings against the same source, the uniqueness statements against the informal
  argument, the text of the proofs against the Lean statements, every changed proof against Baek's,
  the report's "What's next" section against its sources, the comparison of the formalizations
  against the three projects' sources, the manuscript against the Lean statements and proofs, and every
  repaired proof of the stability library against the draft's.

## Baek's paper (1 and 2 October 2026)

How it was made:
- Claude Opus 5.5, in Claude Code 2.1.285, formalized Baek's paper following the skill: every
  statement first, then the proofs of the paper's results and of the results it cites,
  verification, cleanup, and the audit of the paper.
- One coordinating agent and 19 sub-agents. Seventeen proved groups of files, each a chapter or part
  of one, and for Gerver's sofa its separate components (Romik's system, the structure of the sofa,
  the niche, the area); one reviewed every statement against the paper's LaTeX source before any
  proof was written; one checked every finding of the audit against the LaTeX source.
- The coordinating agent wrote the statements, divided the work, checked and integrated every
  result, and wrote the documents. The audited formalization is commit `59b35c2`.
- Afterwards, in the same session, the packaging for the Palomar registry. Version 1 of entry
  PALOMAR-2026-10-02-000008 registers the optimality part, at commit `d0b42d2`.

Figures, from 1 October 22:38 to 2 October 02:28 (commit `59b35c2`; the packaging is not included):
- elapsed time: 3 hours 50 minutes;
- sub-agents: 19, at most 13 at once, about 17.9 hours of work;
- tool calls: 2,704 by the sub-agents, 429 by the main session;
- tokens of the sub-agents: 6.6 million output, 19.3 million input, 1,008 million cache reads;
  of the main session: 0.9 million output, 1.7 million input, 205 million cache reads;
- model calls: 2,597 by the sub-agents and 414 by the main session, all to `claude-opus-5-5`.

## The uniqueness (2 October 2026)

The owner asked for a proof, in Baek's definitions, that every moving sofa of maximal area is
congruent to Gerver's sofa.

How it was made:
- 15:01 to 22:43: ChatGPT Pro 6 wrote the informal uniqueness proof (note 20 and the notes before
  it, now in [`docs/archive/uniqueness/`](docs/archive/uniqueness)), a Lean draft of it, and a draft of
  the connection with formal-conjectures, all without a compiler, in 151 commits of pull request #1.
- 21:55 to 22:56: Claude Opus 5.5, in Claude Code 2.1.287, with the skill's version 1.3.0, checked
  every module of the draft and replaced the 54 proofs that did not compile by `sorry`; every
  statement compiled. Eight sub-agents, each owning a group of files, proved those 54 again,
  starting from the draft's proofs, and a ninth reviewed the statements against note 20. Every proof
  compiled after 27 minutes; the documented proof is commit `7f967fd`.
- Version 2 of the Palomar entry adds the uniqueness theorem, at commit `cf4feff`.

Figures, from 21:55 to 22:56:
- elapsed time: 1 hour;
- sub-agents: 9, all running at once, about 0.9 hours of work;
- tool calls: 400 by the sub-agents, 209 by the main session;
- tokens of the sub-agents: 0.30 million output, 1.2 million input, 44 million cache reads; of the
  main session: 0.21 million output, 0.51 million input, 62 million cache reads;
- model calls: 378 by the sub-agents and 205 by the main session, all to `claude-opus-5-5`.

## The connection with formal-conjectures (2 and 3 October 2026)

The owner asked to prove formal-conjectures' statements of the moving sofa problem from Baek's
theorems.

How it was made:
- 23:05 to 00:02: Claude Opus 5.5, in the same session, ported ChatGPT Pro 6's draft of the
  connection to the repository's layout. Every statement compiled after renaming and a few fixes,
  and the 78 proofs that did not compile were replaced by `sorry`.
- Seven sub-agents proved them again, starting from the draft's proofs; an eighth checked every
  inequality and derivative formula of the analytic argument numerically and compared the
  definitions with formal-conjectures' file; a ninth cleaned up the documentation and the warnings.
  The documented proof is commit `dc408ab`.
- 05:07: pull request [#6808](https://github.com/google-deepmind/formal-conjectures/pull/6808) links
  the proofs from formal-conjectures' file and marks the uniqueness statement solved.

Figures, from 23:05 to 00:02:
- elapsed time: 57 minutes;
- sub-agents: 9, at most 8 at once, about 1.3 hours of work;
- tool calls: 444 by the sub-agents, 120 by the main session;
- tokens of the sub-agents: 0.48 million output, 1.4 million input, 48 million cache reads; of the
  main session: 0.15 million output, 0.26 million input, 83 million cache reads;
- model calls: 402 by the sub-agents and 121 by the main session, all to `claude-opus-5-5`.

## Consolidation (3 October 2026)

The owner asked to simplify the uniqueness proof, consolidate the Lean files, give the Challenge's
namespaces clearer names, present the bridge between formal-conjectures' definitions and Baek's as
the core of that part, and shorten the description in [`formalization.yaml`](formalization.yaml).

How it was made:
- 07:48 to 08:53: Claude Opus 5.5, in Claude Code 2.1.287. The 75 files of the uniqueness and bridge
  libraries became 12 modules, one per step of the argument, and the declarations that no final
  theorem uses were removed (10,428 lines became 8,469). The bridge stopped using the optimality and
  uniqueness theorems.
- The Challenge's namespaces became `Baek`, `Bridge` and `FormalConjectures.MovingSofa`, and the
  Challenge gained the three bridge theorems, from which the Solution derives formal-conjectures'
  statements. One sub-agent rewrote the documentation of the uniqueness modules. Commit `3ddca13`.

Figures, from 07:48 to 08:53:
- elapsed time: 1 hour 5 minutes;
- sub-agents: 1, about 0.4 hours of work;
- tool calls: 61 by the sub-agent, 163 by the main session;
- tokens of the sub-agent: 0.18 million output, 0.73 million input, 16 million cache reads; of the
  main session: 0.26 million output, 0.65 million input, 72 million cache reads;
- model calls: 58 by the sub-agent and 153 by the main session, all to `claude-opus-5-5`.

## The illustrated text (3 October 2026)

The owner asked for an illustrated text of the proofs, in the style of the owner's earlier
formalization [lean4-squares-in-circles](https://github.com/vltanh/lean4-squares-in-circles).

How it was made:
- 09:34 to 10:55: Claude Opus 5.5, in the same session, merged the consolidation into `main` and ran
  Palomar's preflight on it (commit `02af501`, `status: pass`), updated the formal-conjectures pull
  request to link the Solution at that commit, and drew Gerver's sofa in the hallway and its
  animation.
- It wrote the illustrated text of the proofs in [`docs/proof/`](docs/proof/README.md), with the pages
  of [`docs/`](docs) and the README; the earlier documents moved to [`docs/archive/`](docs/archive). Seven
  sub-agents wrote two chapters each, Chapters 2 to 13 and the two appendices, with their figures,
  all seven running at the same time. The coordinating agent wrote Chapter 1 and the other pages,
  and checked and integrated the chapters.
- Writing the text found a sign slip in the paper's proof of Lemma 7.3.1, two inaccuracies in the
  audit, now corrected in [`REPORT.md`](REPORT.md), and a few docstrings that misdescribed their
  declarations. No statement or proof changed.
- Version 3 of the Palomar entry registers commit `eb93296`, the end of this round, at 11:46. Its
  Challenge states twelve theorems, seven more than in version 2: the bridge to formal-conjectures.

Figures, from 09:34 to 10:55:
- elapsed time: 1 hour 21 minutes;
- sub-agents: 7, all running at once, about 5.8 hours of work;
- tool calls: 1,303 by the sub-agents, 328 by the main session;
- tokens of the sub-agents: 2.4 million output, 6.4 million input, 511 million cache reads; of the
  main session: 0.33 million output, 0.77 million input, 153 million cache reads;
- model calls: 1,098 by the sub-agents and 305 by the main session, all to `claude-opus-5-5`.

## Simplification (3 October 2026)

The owner asked for a deep audit that would simplify the Lean and the text proofs and make them
easier to read, and then for a check that the proofs remain faithful to Baek's.

How it was made:
- 12:35 to 15:45: Claude Opus 5.5, in Claude Code 2.1.287. The coordinating agent merged about 190
  copies of small facts, proved again in file after file, into about 90 lemmas of `Basic/`. It found
  that the axiom audit had not imported one module with `import all` (its line had merged into a
  comment), so that the audit did not see that module's proofs; CI now checks the audit's imports.
- Eleven sub-agents, each owning a group of files, simplified the proofs, removed dead and repeated
  code, and gave the long proofs named steps and docstrings; a twelfth merged the duplicates that
  crossed their boundaries, and a thirteenth split the file of Baek's §3.4 into four modules. One
  copy of the interval arithmetic now serves both generated files. The three libraries went from
  50,304 to 45,783 lines; no statement of the Challenge or of a numbered result changed.
- Seven sub-agents audited the text, two chapters each, against the Lean statements. They found no
  false theorem, but about forty gaps and imprecisions, and filled them.
- The proofs were then compared with those of the last audited commit, `eb93296`, and six more
  sub-agents compared the changed proofs, Lean and text, with Baek's LaTeX source. One proof of the
  text, which an editor had replaced by another argument, was restored to Baek's. Commit `3a50b21`.

Figures, from 12:35 to 15:45:
- elapsed time: 3 hours 10 minutes;
- sub-agents: 26, at most 18 at once, about 12.5 hours of work;
- tool calls: 2,914 by the sub-agents, 303 by the main session;
- tokens of the sub-agents: 1.1 million output, 13.3 million input, 893 million cache reads; of the
  main session: 0.32 million output, 0.73 million input, 135 million cache reads;
- model calls: 2,743 by the sub-agents and 300 by the main session, all to `claude-opus-5-5`.

## Following Baek's proofs (3 October 2026)

The skill's version 1.4.0, written that afternoon at the owner's request, requires every proof to
follow the paper's argument and every departure from it to be necessary and reported. The owner
asked to bring this formalization in line with it.

How it was made:
- 16:30 to 20:45: Claude Opus 5.5, in the same session. A new route check compares, for every
  numbered result, the numbered results that its Lean proof uses, which the axiom audit now records,
  with those that Baek's proof cites, extracted from the LaTeX source
  ([`docs/paper_routes.tsv`](docs/paper_routes.tsv)); CI runs it. Of its first 269 differences, 132
  came from facts that the paper uses throughout without citing them.
- Three sub-agents reviewed the other 137 against the LaTeX source, one per group of chapters. They
  fixed about thirty proofs that reached a cited result by a detour, recorded the uses that the
  paper leaves implicit and the citations it makes in passing, and found the proofs that argued
  differently from Baek's with no reason to.
- Nine sub-agents then rewrote about 25 proofs along Baek's arguments, among them Lemma 2.5.6,
  Theorems 3.4.3, 3.4.10 and 4.1.4, Lemmas 6.4.1 and 6.4.2, Theorems 6.2.5, 6.4.3, 7.1.2 (3) and
  7.4.1, and Theorems 8.5.2 and 8.5.4. Three more sub-agents compared every changed proof with the
  LaTeX source, and their findings led to the last rewrites.
- Three statements changed to match the paper: Theorem 8.5.2 regained the hypothesis b < a + π,
  which its proof needs; Lemma 6.2.4 lost a hypothesis that its proof does not use; Theorem 8.4.3 (2)
  gained the equalities of curve area functionals that the paper's "as oriented curves" provides.
- Sixteen results still depart from Baek's proofs, each for an error or gap of the paper, for
  mathematics that Mathlib lacks, or for the definition of the surface area measure; [`REPORT.md`](REPORT.md)
  lists them in its Section 7, and [`docs/route_differences.tsv`](docs/route_differences.tsv) gives
  the reason for each of the 222 route differences. The work also found a wrong citation in the
  proof of Theorem 2.5.9 and two small gaps in the proof of Theorem 3.4.3. The three libraries went
  from 45,783 to 47,894 lines. Commit `0c5c1d3`.

Figures, from 16:30 to 20:45:
- elapsed time: 4 hours 15 minutes;
- sub-agents: 21, at most 6 at once, about 6.3 hours of work; six of them were a first attempt that
  stopped at a usage limit and was run again after it reset at 17:40;
- tool calls: 1,283 by the sub-agents, 291 by the main session;
- tokens of the sub-agents: 2.5 million output, 6.4 million input, 267 million cache reads; of the
  main session: 0.36 million output, 1.6 million input, 129 million cache reads;
- model calls: 1,249 by the sub-agents and 293 by the main session, all to `claude-opus-5-5`.

## What's next, and these credits (3 October 2026)

The owner asked to run Palomar's preflight on the previous round's commit, and to bring the
formalization in line with the skill's versions 1.5.0 to 2.1.0, which add the report's "What's next"
section, this file, and the recording of simpler arguments.

How it was made:
- 20:46 to 21:52: Claude Opus 5.5, in the same session. Palomar's preflight passed on commit
  `0c5c1d3` (`status: pass`, no errors).
- The coordinating agent searched the literature that followed the paper (the arXiv listings, the
  citations that Semantic Scholar and OpenAlex record, and the web) and wrote the report's Section
  10: the work since the paper, open directions, simpler arguments for several of Baek's proofs
  (among them the arguments that the previous round had set aside), and what would extend the
  formalization. It moved the run log into this file, one section per round, with the figures
  recomputed from the transcripts.
- One sub-agent checked Section 10 against its sources and against the paper's LaTeX source. It
  found a preprint that the search had missed (Georgiev, Gómez-Serrano, Tao and Wagner), and the notes
  of deancureton/MovingSofa, which list errors and gaps of the paper. A second sub-agent compared
  those notes, and the blueprint of RuifengCao/sofa-formal, with the audit. Twelve of their findings
  were missing from it; they are now in [`REPORT.md`](REPORT.md), credited to the notes. Two statements need a
  hypothesis that the paper leaves out (Section 4), and a new E18 concerns Lemma 7.1.6, so the later
  E-items moved up by one.
- A third sub-agent restored two Lean statements that were weaker than the paper's: Lemma 7.1.6 now
  holds for every convex-bilinear map on a real vector space, and Theorem 8.4.1 (4) includes the
  one-sided derivatives at the junctions and at the ends of the phases.
- Version 4 of the Palomar entry registers commit `16653ae`, the end of this round, on 4 October at
  05:16: the Challenge of version 3, with the simplified proofs that follow Baek's arguments.

Figures, from 20:46 to 21:52:
- elapsed time: 1 hour 6 minutes;
- sub-agents: 3, one at a time, about 0.8 hours of work;
- tool calls: 222 by the sub-agents, 131 by the main session;
- tokens of the sub-agents: 0.30 million output, 0.72 million input, 36 million cache reads; of the main session: 0.15 million output, 0.27 million input, 103 million cache reads;
- model calls: 213 by the sub-agents and 133 by the main session, all to `claude-opus-5-5`.

## The manuscript's results in Lean (4 October 2026)

The owner asked that the manuscript of the uniqueness be a faithful translation of the formalization: a result that
the text had and the Lean did not was to be proved in Lean, and the text was to state what the Lean states
everywhere else.

How it was made:
- 11:48 to 14:15: Claude Sonnet 5.5, in Claude Code 2.1.289, the session that wrote the manuscript, coordinated
  sub-agents running Claude Opus 5.5.
- One sub-agent extended [`MovingSofaUniqueness/`](MovingSofaUniqueness) (`Main`, `Rigidity`, `RegularClosed`, [`Rigid`](MovingSofaUniqueness/Rigid.lean#L88)): a right-angle cap
  has the sofa area of Gerver's sofa if and only if it is a horizontal translate of Gerver's cap; the maximal
  sofas are the moving sofas that a rigid map takes onto Gerver's sofa; the width of Gerver's sofa exceeds one in
  every direction but the vertical, so that no rotation is needed and a rotated copy of Gerver's sofa moves only if
  the angle is a multiple of π. Three helper lemmas that are not numbered results of the paper now state the
  rotation angle. No numbered result and no statement of the Challenge changed. Commit `952812d`; the audit, the
  route check and the other checks pass, and so does Palomar's preflight (`status: pass`).
- Six sub-agents rewrote Sections 2 and 4 to 9 of the manuscript and its Appendices B and C to state what the Lean
  states and to follow its proofs; four more sub-agents compared Section 2 with the Lean line by line, and five
  compared the whole manuscript with the Lean in two rounds. They found no false step, and many places where the text
  said more, less or something other than the Lean; all were corrected.

Figures, from 11:48 to 14:15:
- elapsed time: 2 hours 26 minutes;
- sub-agents: 16 (4 of them launched by another sub-agent), at most 10 at once, about 7.3 hours of work;
- tool calls: 1,679 by the sub-agents, 142 by the main session;
- tokens of the sub-agents: 3.00 million output, 18.03 million input, 469 million cache reads; of the main
  session: 0.23 million output, 0.48 million input, 74 million cache reads;
- model calls: 1,365 by the sub-agents (all to `claude-opus-5-5`) and 118 by the main session (`claude-sonnet-5-5`).

## A second proof of optimality (5 October 2026)

The owner asked to merge pull request #5, in which ChatGPT Pro 6 had written a second proof of Baek's optimality
theorem from the maximizing caps of the uniqueness proof, and to update the manuscript as the pull request
suggested.

How it was made:
- 11:56 to 12:52: Claude Opus 5.5, in Claude Code 2.1.289. The pull request added three Lean modules
  (`Maximizers`, `Optimality`, `Alternative`; 428 lines), a separate dependency audit and notes,
  none of them compiled or run, and left every existing file unchanged. The modules compiled without change and
  without warnings, and the audit passed: none of their 24 declarations depends on Baek's Theorem 1.1.1 or on
  [`MovingSofaUniqueness.Main`](MovingSofaUniqueness/Main.lean). Commit `3af9279` merges the pull request as it was.
- Commit `51c9be1` makes CI check the new code. [`scripts/Audit.lean`](scripts/Audit.lean) imports the three modules, as the CI step
  that compares its imports with the libraries requires. The second audit, [`scripts/AuditMaximizerRoute.lean`](scripts/AuditMaximizerRoute.lean),
  also rejects the results from which Baek derives the right-angle motion and the injectivity condition of
  Baek's cap from its balance (Theorems 1.5.2 and 8.1.1 (2), and the eight results they rest on), and it passes;
  CI runs it. The docstrings and the documentation describe the second proof. The continuous integration and
  Palomar's preflight passed on this commit.
- The manuscript gained Fact 2.7, Section 8.4 (Lemmas 8.6 and 8.7, Theorem 8.8) and the related passages of
  Sections 1 to 3 and 10 and Appendices C to E, and now cites commit `51c9be1`. Two sub-agents (Claude Opus 5.5),
  neither able to edit, read the new text, one against the Lean and one for its prose; the first found no
  mathematical error, and their findings were applied.
- Afterwards, at the owner's request, the same session removed the paragraph on the second proof that had ended
  Section 1.4 of the manuscript, and added one sentence on it to the abstract.

Figures, from 11:56 to 12:52:
- elapsed time: 57 minutes;
- sub-agents: 3, at most 3 at once, about 0.4 hours of work: the two readers of the manuscript, and a one-word test
  call;
- tool calls: 81 by the sub-agents, 166 by the main session;
- tokens of the sub-agents: 0.15 million output, 0.48 million input, 12 million cache reads; of the main session:
  0.21 million output, 0.52 million input, 56 million cache reads;
- model calls: 70 by the sub-agents (69 to `claude-opus-5-5`, 1 to `claude-haiku-4-5`) and 151 by the main session
  (`claude-opus-5-5`).

## The comparison of the formalizations (5 October 2026)

The owner asked for a deeper comparison between the formalizations of Baek's proof, and then for the
changes that it suggested.

How it was made:
- 16:35 to 18:48: Claude Opus 5.5, in Claude Code 2.1.289. The coordinating agent searched GitHub,
  Palomar's registry and the records of the Justin Sun Prize for Lean projects on the moving sofa
  problem; cloned the two other formalizations of Baek's proof and six related projects; built the
  two other formalizations and this repository at the commits compared; and measured the three with
  the same scripts: the lines of code, the declarations that a user can name, those that the proof of
  formal-conjectures' main statement uses, the axioms of the theorems that Comparator checks, and
  the build times.
- Six sub-agents, running at the same time, read the sources: one profile of each formalization, a
  comparison of the statements and of what each asks a reader to trust, a map of the paper's 301
  numbered environments onto the three, and a merged list of the errors that the three found in the
  paper, checked against its LaTeX source. Two more sub-agents checked the new page against the
  sources; the first found 18 problems and the second 16 more, all fixed. The result is
  [`docs/formalizations.md`](docs/formalizations.md), which replaces the comparison table of [`docs/prior-work.md`](docs/prior-work.md).
- From 22:02, at the owner's request, the changes. The comparison had found that Theorem 2.1.3 was
  proved by compactness instead of by Baek's ε-triangle, a departure that the report's Section 7 did
  not list; the proof now follows Baek's argument, and Chapter 2 of the text with it. The report's
  status line and Section 9 now name the results that the formalization leaves out, item E17 notes
  that the overview states f(0) = 1, and Section 10 gains O'Keefe's upper bounds for the ambidextrous
  sofa and says how the findings of RuifengCao/sofa-formal compare with the audit's. The Challenge,
  the README, the definitions page and [`formalization.yaml`](formalization.yaml) no longer call the Challenge's copy of
  formal-conjectures verbatim: its docstrings are reworded, and the `ℝ²` notation and two instances are
  declared in it. [`ChallengeDefs`](ChallengeDefs.lean) and the definitions and verification pages no longer say that
  all the libraries use the constants of [`ChallengeDefs`](ChallengeDefs.lean).

Figures, from 16:35 to 18:48 and from 22:02 to 22:17:
- elapsed time: 2 hours 13 minutes and 15 minutes;
- sub-agents: 8, all in the first part, at most 6 at once, about 4.3 hours of work;
- tool calls: 1,367 by the sub-agents, 273 by the main session;
- tokens of the sub-agents: 6.2 million input, 465 million cache reads (their transcripts record the output tokens only in part); of the main session: 0.38 million output, 1.7 million input, 131 million cache reads;
- model calls: 1,319 by the sub-agents and 255 by the main session, all to `claude-opus-5-5`.

## The stability (5 October 2026)

The owner asked to incorporate pull request #8, which proves that sofas of nearly maximal area are close to Gerver's
sofa. Its argument (the notes now in [`docs/archive/stability/`](docs/archive/stability)) and its Lean code, 85 modules and about
12,200 lines, had been written by ChatGPT Pro 6 and never compiled.

How it was made:
- 22:17 to 23:13: Claude Opus 5.5, in Claude Code 2.1.289, following the skill's procedure for an uncompiled draft,
  in a separate worktree of the pull request's branch.
- Every module was brought to elaborate in the order of its imports, with the 123 proofs that failed (of about 490
  declarations) replaced by `sorry`, and two variable names that Lean rejects renamed. That is the baseline,
  commit `d56546e`.
- Sixteen sub-agents restored and repaired the draft's proofs, each a group of modules, checking them against
  private copies of the compiled modules. Most failures were names that Mathlib has changed, rewrites that found no
  match, and facts that `linarith` could not see. Twenty lemmas were false as compiled: their hypotheses were
  section variables that the statements never mention, which Lean 4 leaves out. The agents checked a
  counterexample to each in Lean, and `include` now adds the hypotheses that the draft's proofs and callers assumed.
- The coordinating agent compared every agent's statements with the baseline, integrated the work, removed six
  hypotheses that helper lemmas did not use, cleared the other linter warnings, and made the library a default
  target, part of the axiom audit and part of CI. A seventeenth sub-agent compared every repaired proof with the
  draft's and found no change of argument. The audit passes: the 5,957 declarations of the libraries use only the
  standard axioms.
- [Stability](docs/stability.md) describes the result. The pull request's notes, numerical checks and status documents
  moved to [`docs/archive/stability/`](docs/archive/stability); the README, the report's "What's next", and the pages on the layout
  and the verification mention the new library. The manuscript is unchanged.

Figures, from 22:17 to 23:13:
- elapsed time: 56 minutes;
- sub-agents: 17, at most 16 at once, about 2.3 hours of work;
- tool calls: 883 by the sub-agents, 209 by the main session;
- tokens of the sub-agents: 0.78 million output, 2.40 million input, 80 million cache reads; of the main
  session: 0.22 million output, 0.52 million input, 66 million cache reads;
- model calls: 832 by the sub-agents and 199 by the main session, all to `claude-opus-5-5`.

## The stability in the Challenge and the manuscript (6 October 2026)

The owner named ChatGPT Pro 6 as the author of pull request #8 and asked to state the stability theorems in the
Challenge without running Palomar's preflight yet, to add the stability to the manuscript, and to add to the
formalize-math-paper skill the pitfall that the previous round had met.

How it was made:
- 07:08 to 09:49: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous round.
- Commit `92b2f86` states three stability theorems in the Challenge ([`Baek.gerver_sofa_stable`](Challenge.lean#L405),
  [`Baek.gerver_sofa_angle_stable`](Challenge.lean#L415), [`Baek.gerver_sofa_stability_exponent`](Challenge.lean#L425)), with five definitions in [`ChallengeDefs`](ChallengeDefs.lean)
  and, in [`Solution.lean`](Solution.lean), the proofs that they agree with the library's. Comparator accepts the fifteen theorems,
  the audit passes with 5,962 declarations, and the continuous integration passed; Palomar's preflight was not run.
  [`formalization.yaml`](formalization.yaml) describes the stability, and the documents name ChatGPT Pro 6 as the author of pull
  request #8.
- The manuscript gained Section 10, the stability (Theorems 10.1 to 10.4 with their proofs, about sixteen pages),
  and the passages on it in the abstract, Sections 1 and 11 and Appendices D and E; it now cites commit `92b2f86`.
  A sub-agent wrote Section 10 and its rows of the dictionary from the Lean, and three sub-agents that it launched
  compared every statement and proof with the Lean, part by part. Two more sub-agents, neither able to edit, then
  read the new text, one against the Lean and the repository, the other for its prose. Their findings were applied,
  among them a sign error in the description of Mamikon's term in Section 2. The manuscript grew from 70 to 91
  pages; its README records the round.
- Version 2.1.1 of the formalize-math-paper skill (commit `06ae331`) adds the pitfall that Lean 4 leaves out of a
  statement the section variables that it does not mention, with the check and the fix.

Figures, from 07:08 to 09:49:
- elapsed time: 2 hours 41 minutes;
- sub-agents: 6 (3 of them launched by another sub-agent), at most 4 at once, about 3.2 hours of work;
- tool calls: 549 by the sub-agents, 108 by the main session;
- tokens of the sub-agents: 1.32 million output, 4.63 million input, 121 million cache reads; of the main
  session: 0.16 million output, 1.63 million input, 85 million cache reads;
- model calls: 447 by the sub-agents and 114 by the main session, all to `claude-opus-5-5`.

## The coercive route (6 October 2026)

The owner asked to integrate pull request #9 so that one theorem gives another proof of optimality, uniqueness and
stability at once, and to present it in the manuscript as a new section or subsection. ChatGPT Pro 6 had written the
pull request on the evening of 5 October, without compiling it: the library [`MovingSofaExtremal`](MovingSofaExtremal), which proves
optimality and uniqueness from two estimates of the stability library, a second solution of twelve statements of the
Challenge, and an audit. It had left for later the step that moves the stability proof onto the route.

How it was made:
- 09:56 to 13:22: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous rounds, with version 2.1.1
  of the formalize-math-paper skill.
- The manuscript's branch was merged into the pull request's branch (commit `bcb4562`; the conflicts in [`lakefile.toml`](lakefile.toml)
  and `MamikonEnergy.lean` were resolved for the compiled code). One proof did not compile, a `change` whose two sides
  are not definitionally equal, and one linter warning remained (commit `ae0162a`).
- A search through the proofs found the four places where the stability library still reached the first proofs: the
  sign of the deficit and the compactness step, through Baek's theorem; the identification of the limit, through the
  first proof of uniqueness; and the lemma that a moving sofa lies in a strip of height one. Commit `70ccc8a` takes
  them from the route or from a neutral module, states the certificate as one theorem
  ([`MovingSofaStability.coercive_certificate`](MovingSofaStability/CapEstimate.lean#L1120)), which the route's classification of the maximizing caps and the
  stability library's local estimate both use, adds to the route the theorem that no rotation is needed, states the
  three results in one theorem ([`MovingSofaExtremal.gerver_sofa_optimal_unique_stable`](MovingSofaExtremal/Unified.lean#L38)), and extends the second
  solution to the fifteen statements. The pull request's audit had never run, and on the merged branch it failed;
  it was rewritten for the whole route, the stability library included, and now runs in CI: none of the 958
  declarations reaches Baek's Theorem 1.1.1, his balance results or the first proof of uniqueness, and optimality
  and uniqueness do not reach the stability theorem. The main audit passes with 6,062 declarations, Comparator
  accepts the fifteen theorems, and [The coercive route](docs/coercive.md) describes the result.
- The pull request was retargeted at the manuscript's branch and merged as commit `94a1bcf`, on which the continuous
  integration passed; Palomar's preflight was not run.
- The manuscript gained Section 11, the derivation of the three results from one estimate, and the formalization
  section became Section 12. A sub-agent wrote the section and the passages that refer to it from the Lean; three
  sub-agents that it launched compared the text with the Lean part by part, and a fourth checked the passages
  rewritten after their reports. Two more sub-agents, neither able to edit, then read the new text, one against the
  Lean and the repository, the other for its prose; neither found a mathematical error, and the writing sub-agent
  applied their reports. The manuscript grew from 91 to 101 pages.
- The owner then said that they have not read the manuscript past Section 1, which Section 1.5 and Appendix E now
  say, and asked to use the best bound: the stability proof now carries the coefficient 2 sec φ of the cap estimate
  through its constants, where it had weakened it to 80 (commit `a94bde6`; Comparator accepts, the audits pass).
  Section 10 of the manuscript changed with it.
- At the owner's request, Section 8.4 of the manuscript (the second proof of optimality of pull request #5) was
  shortened to a remark at the end of Section 8 (Remark 8.6), which outlines the second proof with Baek's own bound
  and says that the formalization proves it ([`MovingSofaUniqueness.MaximizerRoute`](MovingSofaUniqueness/MaximizerRoute.lean)); its lemma on the right-angle
  motion moved to the end of Section 6 (Lemma 6.10), and Section 11 writes the proof out with the certificate. The
  docstrings of the second proof now cite the remark (commit `6ed7657`). The manuscript has 99 pages and cites
  `6ed7657`.

Figures, from 09:56 to 13:22:
- elapsed time: 3 hours 26 minutes, of which 12 minutes waiting for the owner's answers;
- sub-agents: 7 (4 of them launched by another sub-agent), at most 4 at once, about 3.8 hours of work; the
  writing sub-agent was resumed three times, to apply the two reviews, to fold Section 8.4 into Section 11, and to
  move the remark to Section 8;
- tool calls: 810 by the sub-agents, 256 by the main session;
- tokens of the sub-agents: 1.20 million output, 6.06 million input, 257 million cache reads; of the main
  session: 0.39 million output, 0.75 million input, 119 million cache reads;
- model calls: 678 by the sub-agents and 261 by the main session, all to `claude-opus-5-5`.

## Simplifying the new libraries (6 October 2026)

The owner asked to simplify and consolidate the stability library and the other new code, keeping the
formalization of Baek's paper and the connection with formal-conjectures intact, and then to rewrite the manuscript.

How it was made:
- 13:25 to 16:09: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous rounds, with version 2.1.1
  of the formalize-math-paper skill.
- Commit `0b7978c` removes what the two new proofs of optimality repeated. Both turned the value and the shape of
  the maximizing right-angle caps into optimality and uniqueness by the same steps; one assembly now does it
  ([`MovingSofaUniqueness.Maximizing`](MovingSofaUniqueness/Maximizing.lean)), and each proof gives the two facts in its own way
  ([`MovingSofaUniqueness.MaximizerRoute`](MovingSofaUniqueness/MaximizerRoute.lean), from Baek's bound and the equality analysis; [`MovingSofaExtremal.Main`](MovingSofaExtremal/Main.lean), from
  the certificate). The helpers that the coercive route had copied from [`MovingSofaUniqueness.Rigidity`](MovingSofaUniqueness/Rigidity.lean), so as not
  to import it, moved to two modules that both proofs import ([`MovingSofaUniqueness.Mamikon`](MovingSofaUniqueness/Mamikon.lean), [`MovingSofaUniqueness.Rigid`](MovingSofaUniqueness/Rigid.lean)).
- Commit `830b03d` merges the 86 files of the stability library (87 before `0b7978c` moved `MamikonFoundation` out),
  most of them 100 to 200 lines long and in one chain of imports, into eleven modules, one for each step of the
  proof, besides the root module `All`, and removes 74 declarations that no
  theorem uses, among them the cap estimate with coefficient 80, which the proof no longer needs since it
  carries the coefficient 2 sec φ.
- Commit `5817473`: eight sub-agents, in parallel and each on its own copy of the build, rewrote the eleven
  modules and the modules shared by the two proofs. A declaration that another module, a solution or an audit
  uses kept its name and its statement, which a comparison of the elaborated types checked; the others could be
  merged, restated or removed. The sub-agents merged repeated helpers, inlined helpers used once, and replaced
  computations by hand with Mathlib lemmas.
- The stability library went from 12,550 lines in 87 files to 7,585 lines in 12, and the coercive route from 661
  lines in 7 files to 235 in 3; the main audit now checks 5,860 declarations instead of 6,062, and the audit of the
  coercive route 743 instead of 958. Baek's library, the bridge, the Challenge, its definitions and the proofs of
  [`Solution.lean`](Solution.lean) are unchanged, and no statement of the Challenge, of a numbered result or of a main theorem
  changed. The audits and the route check pass, and Comparator accepts the fifteen theorems.
- Commit `1856810` brought the documentation up to date, and commit `7b8c0a8` the docstring of
  [`MovingSofaExtremal/All.lean`](MovingSofaExtremal/All.lean), which still listed the old modules; the continuous integration passed on both, and
  Palomar's preflight was not run.
- A sub-agent then revised the manuscript for the simplified libraries, with five sub-agents that it launched, which
  compared each part of Section 10 with the Lean before and after the rewrite. Appendix D names the declarations at
  commit `7b8c0a8`, which the manuscript now cites; Section 10 lost the bound with the constant 80, and six of its
  steps now follow the Lean's proofs, two that the rewrite changed and four that had differed before; Remark 8.6 and
  Sections 11 and 12 describe the new modules and counts, and Appendix E and the manuscript's README record the round.
  Two more sub-agents, neither able to edit, then read the revision, one against the Lean and the repository, the
  other for its prose. Neither found a mathematical error; the writing sub-agent applied their findings (a line
  count, the account of the files and of the rewritten modules, and the wording of several passages). The manuscript
  has 100 pages.

Figures, from 13:25 to 16:09:
- elapsed time: 2 hours 44 minutes;
- sub-agents: 16 (5 of them launched by another sub-agent), at most 8 at once, about 7.1 hours of work; the writing
  sub-agent was resumed twice, for the four older differences and for the two reviews;
- tool calls: 1,474 by the sub-agents, 189 by the main session;
- tokens of the sub-agents: 2.69 million output, 7.77 million input, 426 million cache reads; of the main session:
  0.26 million output, 0.52 million input, 85 million cache reads;
- model calls: 1,372 by the sub-agents and 189 by the main session, all to `claude-opus-5-5`.

## Comparator for the second solution, and the manuscript reorganized (6 October 2026)

The owner asked whether the second solution should be in the Challenge too, then asked that Comparator check it
in the same project, and that the page of results say that the stability theorem gives the uniqueness up to a
translation. Then the owner asked that Section 12 of the manuscript keep only the open questions, with the
formalization and the use of AI in the appendices; allowed renaming the manuscript; and asked for an introduction
in which Section 1.4 gives the strategy of the uniqueness proof, with a short remark that it gives another proof of
optimality, and a new section gives the strategy of the stability proof, parallel to the outlines of Baek's proof
and of the uniqueness proof, with a remark on the certificate that gives the three results.

How it was made:
- 16:13 to 16:58: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous rounds.
- Comparator now checks the second solution too (commit `3d3ea3e`, on which the continuous integration passed):
  [`SolutionCoerciveComparator.lean`](SolutionCoerciveComparator.lean) states the theorems of [`SolutionCoercive.lean`](SolutionCoercive.lean) under the Challenge's names, each
  proved by the theorem of [`SolutionCoercive.lean`](SolutionCoercive.lean), and [`comparator-coercive.json`](comparator-coercive.json) points Comparator at it;
  Comparator accepts both solutions. The audit of the coercive route now requires each theorem of the second solution to
  have exactly the statement of the matching theorem of [`Solution.lean`](Solution.lean), where it accepted a definitionally equal one.
  The page of results now notes that the Challenge's stability theorem, at zero deficit, gives the uniqueness up to a
  translation.
- The manuscript cites commit `3d3ea3e`. The main session moved its description of the formalization from Section 12
  to Appendix D.1, so that Section 12 lists the open questions only; renamed it *Uniqueness and stability of Gerver's
  sofa*; and wrote the remark at the end of Section 1.4 on the second proof of optimality and Section 1.5 on the
  strategy of the stability proof, which ends with the reason for the name "coercive certificate": an identity
  writes the gap as a sum of nonnegative terms, as a certificate does in optimization, and the energy among these
  terms also bounds the distance to Gerver's cap. Two sub-agents, neither able to edit, then read the result, one
  for its accuracy against the later sections and the Lean, the other for its prose and its structure. Neither
  found a mathematical error; the main session applied their findings, among them a false sentence on the punctured
  sofas and a term used for two inequalities. The manuscript has 102 pages.

Figures, from 16:13 to 16:58:
- elapsed time: 45 minutes;
- sub-agents: 2, at the same time, about 0.4 hours of work;
- tool calls: 97 by the sub-agents, 70 by the main session;
- tokens of the sub-agents: 0.18 million output, 0.55 million input, 14 million cache reads; of the main session:
  0.14 million output, 0.23 million input, 28 million cache reads;
- model calls: 84 by the sub-agents and 67 by the main session, all to `claude-opus-5-5`.

## The manuscript's readability (6 October 2026)

The owner asked to shorten the outline of the manuscript (Section 1.7), to rewrite the account of the use of AI
(Appendix E) as bulleted lists, to put the definitions of Section 2 into definition environments, and to move long
inline formulas onto their own lines.

How it was made:
- 16:59 to 17:50: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous rounds.
- The main session shortened Section 1.7, which the two sections on the strategies had made partly redundant;
  rewrote Appendix E as three bulleted lists (who wrote what, what was checked and by whom, what a person has read),
  from 1,880 words to about 820, leaving the round-by-round detail to this file and to the manuscript's README; and
  put every notion of Section 2 into a definition with its name in the title. A word-level comparison found no change
  of content.
- Seven sub-agents, one per group of section files, moved long inline formulas into unnumbered displays, 387
  in all, each building a private copy of the manuscript to check that it compiles without overfull lines. A script
  compared every file before and after with the typography stripped: the mathematics, the labels and the references
  did not change; the only word changes are the connectives that the displays need. The manuscript has 117 pages.

Figures, from 16:59 to 17:50:
- elapsed time: 51 minutes;
- sub-agents: 7, all at the same time, about 3.1 hours of work;
- tool calls: 938 by the sub-agents, 43 by the main session;
- tokens of the sub-agents: 1.21 million output, 2.71 million input, 117 million cache reads; of the main session:
  0.08 million output, 0.14 million input, 27 million cache reads;
- model calls: 526 by the sub-agents and 44 by the main session, all to `claude-opus-5-5`.

## Merging into main for Palomar version 5 (6 October 2026)

The owner asked to merge this work into main so as to submit a fifth version of the Palomar entry, and to clean up
the branches and pull requests.

How it was made:
- 18:16 to 18:30: Claude Opus 5.5, in Claude Code 2.1.289, in the session of the previous rounds.
- Main had one commit that the branch of the manuscript lacked (`13d574e`, the comparison of the formalizations).
  Commit `22f0b37` merges it. The conflicts were in the illustrated text's links to the code (regenerated), the
  README, the page of results and this file; the merged build is clean, the audit checks 5,868 declarations, the
  route check and the audits of the second proof and of the coercive route pass, Comparator accepts both solutions,
  and the continuous integration passed on the merge. Main now points to this work. The branches of the merged pull
  requests were deleted, and the three open pull requests that targeted the manuscript's branch now target main.
- 19:26 to 19:47, at the owner's request: pull requests #2 (a separate manuscript of 3 October) and #6 (the
  experiment that led to the stability proof) were closed, their heads kept as the tags
  `archive/stationarity-deficit-rigidity` and `archive/original-sofa-discovery`, and their branches deleted. The
  preflight workflow now pins Palomar's current pipeline (`d4e41c1`, commit `701ec74`), and Palomar's preflight passed
  on `701ec74` (`status: pass`, with one warning: the Challenge exceeds the preferred review size of 300 lines); the
  continuous integration passed on it too. It is the commit prepared for version 5, and the manuscript cites it.

Figures, from 18:16 to 18:30 and from 19:26 to 19:47:
- elapsed time: 14 and 21 minutes;
- sub-agents: none;
- tool calls: 54 by the main session; tokens: 0.05 million output, 0.08 million input, 42 million cache reads;
- model calls: 55, all to `claude-opus-5-5`.
