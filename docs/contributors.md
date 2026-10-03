# Contributors

[Back to the README](../README.md)

AI models wrote the Lean code, the informal uniqueness argument, the documents and the figures. The
repository owner, The-Anh Vu-Le, directed the work and made the decisions about scope, naming and
publication. No human has reviewed the proofs; Lean's kernel checks every one of them. Times are US
Central time (UTC−5); figures on effort come from the session transcripts, computed by the
[formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill's `session_stats.py`.

## 1 and 2 October 2026: Baek's paper

* **22:38 to 02:28: the formalization.** Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in
  Claude Code 2.1.285, formalized Baek's paper, following the formalize-math-paper skill (commit
  `cbdedac`): every statement first, then the proofs of the paper's results and of the results it
  cites, verification, cleanup, and the audit of the paper. One coordinating agent and 19 sub-agents,
  at most 13 of them running at the same time:
  - 17 proved groups of files, each a chapter or part of one, and for Gerver's sofa its separate
    components (Romik's system, the structure of the sofa, the niche, the area);
  - one reviewed every statement against the paper's LaTeX source before any proof was written;
  - one checked every finding of the audit against the LaTeX source.

  The coordinating agent wrote the statements, divided the work, checked and integrated every result,
  and wrote the documents. The audited formalization is commit `59b35c2`. The sub-agents worked about
  18 hours in total; all agents together made 3,135 tool calls (2,704 of them by sub-agents),
  generated 7.5 million output tokens and read 21 million input tokens, plus 1.2 billion tokens from
  the prompt cache.
* **Afterwards: Palomar.** The packaging for the Palomar registry came next; version 1 of entry
  PALOMAR-2026-10-02-000008 registers the optimality part, at commit `d0b42d2`.

## 2 October 2026: the uniqueness

* **15:01 to 22:43: the argument and a Lean draft.** ChatGPT Pro 6 (OpenAI) wrote the informal
  uniqueness proof (note 20 and the notes before it, now in [`docs/archive/uniqueness/`](archive/uniqueness)), a
  Lean draft of it, and a draft of the connection with formal-conjectures, all without a compiler, in
  151 commits of pull request #1. Its effort was not recorded.
* **21:55 to 22:56: the compiled proof.** Claude Opus 5.5, in Claude Code 2.1.287, with the skill
  (version 1.3.0), checked every module of the draft and replaced the 54 proofs that did not compile
  by `sorry`; every statement compiled. Eight sub-agents, each owning a group of files, proved those
  54 again, starting from the draft's proofs, and a ninth reviewed the statements against note 20;
  at most nine ran at the same time. The documented proof is commit `7f967fd`; every proof compiled
  after 27 minutes. The sub-agents worked about 0.9 hours; all agents together made 607 tool calls
  (400 by sub-agents), generated 0.5 million output tokens and read 1.7 million input tokens, plus
  105 million tokens from the prompt cache.
* Version 2 of the Palomar entry adds the uniqueness theorem, at commit `cf4feff`.

## 2 and 3 October 2026: the connection with formal-conjectures

* **23:05 to 00:02.** Claude Opus 5.5, in the same session, ported ChatGPT Pro 6's draft of the
  connection to the repository's layout. Every statement compiled after renaming and a few fixes,
  and the 78 proofs that did not compile were replaced by `sorry`. Seven sub-agents proved them
  again, starting from the draft's proofs; an eighth checked every inequality and derivative formula
  of the analytic argument numerically and compared the definitions with formal-conjectures' file,
  and a ninth cleaned up the documentation and the warnings. At most eight ran at the same time. The
  documented proof is commit `dc408ab`. The sub-agents worked about 1.3 hours; all agents together
  made 561 tool calls (444 by sub-agents), generated 0.6 million output tokens and read 1.7 million
  input tokens, plus 129 million tokens from the prompt cache.
* **05:07: formal-conjectures.** Pull request
  [#6808](https://github.com/google-deepmind/formal-conjectures/pull/6808) links the proofs from
  formal-conjectures' file and marks the uniqueness statement solved.

## 3 October 2026: consolidation, and this text

* **07:48 to 08:53: consolidation.** Claude Opus 5.5, in Claude Code 2.1.287, at the owner's
  request: the 75 files of the uniqueness and bridge libraries became 12 modules, one per step of the
  argument, and the declarations that no final theorem uses were removed (10,428 lines became
  8,469); the bridge stopped using the optimality and uniqueness theorems; the Challenge's
  namespaces became `Baek`, `Bridge` and `FormalConjectures.MovingSofa`, and the Challenge gained the
  three bridge theorems, from which the Solution derives formal-conjectures' statements. One
  sub-agent rewrote the documentation of the uniqueness modules. Commit `3ddca13`. All agents
  together made 221 tool calls (61 by the sub-agent), generated 0.4 million output tokens and read
  1.4 million input tokens, plus 86 million tokens from the prompt cache.
* **09:34 to 10:55: this text.** Claude Opus 5.5, in the same session, at the owner's request:
  merged the consolidation into `main` and ran Palomar's preflight on it (commit `02af501`,
  `status: pass`), updated the formal-conjectures pull request to link the Solution at that commit,
  drew Gerver's sofa in the hallway and its animation, and wrote the illustrated text of the proofs in
  [`docs/proof/`](proof/README.md), with the pages of `docs/` and the README, in the style of the
  owner's earlier formalization
  [lean4-squares-in-circles](https://github.com/vltanh/lean4-squares-in-circles); the earlier
  documents moved to [`docs/archive/`](archive). Seven sub-agents wrote two chapters each, Chapters 2
  to 13 and the two appendices, with their figures, all seven running at the same time; the
  coordinating agent wrote Chapter 1 and the other pages, and checked and integrated the chapters.
  Writing the text found a sign slip in the paper's proof of Lemma 7.3.1 and two inaccuracies in the
  audit, now corrected in [`REPORT.md`](../REPORT.md), and a few docstrings that misdescribed their
  declarations. No statement or proof changed. The sub-agents worked about 5.8 hours; all agents
  together made 1,619 tool calls (1,303 by sub-agents), generated 2.7 million output tokens and
  read 7.2 million input tokens, plus 658 million tokens from the prompt cache.
