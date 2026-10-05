# Credits

How this formalization was made, from the run log and the session transcripts. Times are US Central
Time (UTC−5). The figures come from the Claude Code session transcripts, computed with the
formalize-math-paper skill's `session_stats.py`; they do not include the work of ChatGPT Pro 6, which
was not recorded.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization of Baek's paper and
  for each later round below, and decided the scope, the names and the publication.
- **Formalization:** Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in Claude Code 2.1.285
  and 2.1.287, in four sessions: the Lean code of the three libraries, the audit of the paper, the
  documents and the figures; and on 4 October, as sub-agents of the session that wrote the manuscript
  (Claude Code 2.1.289, whose main agent is Claude Sonnet 5.5), the extension of the libraries below;
  and on 5 October, in Claude Code 2.1.289, the merge of the second proof of optimality below.
  ChatGPT Pro 6 (OpenAI) wrote the informal uniqueness argument and uncompiled Lean drafts of the
  uniqueness proof and of the connection with formal-conjectures, and on 5 October the uncompiled
  Lean modules of a second proof of Baek's theorem (pull request #5).
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill:
  commit `cbdedac` for Baek's paper, versions 1.3.0 and 1.3.1 for the rounds up to the
  simplification, version 1.4.0 for following Baek's proofs, and version 2.1.0 for the last round.
- **Review:** no person has reviewed the proofs; Lean's kernel checks every one of them. Independent
  agents checked the statements against the paper's LaTeX source before any proof was written, the
  audit's findings against the same source, the uniqueness statements against the informal
  argument, the text of the proofs against the Lean statements, every changed proof against Baek's,
  and the report's "What's next" section against its sources, and the manuscript against the Lean
  statements and proofs.

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
- One sub-agent extended [`MovingSofaUniqueness/`](MovingSofaUniqueness) (`Main`, `Rigidity`, `RegularClosed`, [`Rigid`](MovingSofaUniqueness/Rigid.lean#L85)): a right-angle cap
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
  ([`Maximizers`](MovingSofaUniqueness/Maximizers.lean), [`Optimality`](MovingSofaUniqueness/Optimality.lean), [`Alternative`](MovingSofaUniqueness/Alternative.lean); 428 lines), a separate dependency audit and notes,
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
