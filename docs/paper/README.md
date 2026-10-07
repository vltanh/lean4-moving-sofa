# Uniqueness and stability of Gerver's sofa: the manuscript

A LaTeX manuscript, prepared for arXiv, of the theorem that Gerver's sofa is the only maximal moving
sofa: every moving sofa of the same area is a rotated and translated copy of it, as a set. Section 10 proves
that this uniqueness is stable: a moving sofa whose area is ε less than the maximum lies, after a translation,
within Hausdorff distance O(√ε) of Gerver's sofa, and the exponent 1/2 cannot be improved. Section 11 derives
optimality, uniqueness and stability from one estimate of the stability proof (the coercive certificate). The manuscript
follows the formalization in this repository and cites it for the machine-checked statements; the Lean
statements are `Baek.gerver_sofa_unique`, `Baek.gerver_sofa_stable`, `Baek.gerver_sofa_angle_stable` and
`Baek.gerver_sofa_stability_exponent` in [`Challenge.lean`](../../Challenge.lean).

This is a draft for the author to read. An AI model (Claude Sonnet 5.5, in Claude Code) wrote the text from
the Lean library, the illustrated text of the proofs in [`docs/proof/`](../proof/README.md) and the text of
Baek's paper, and independent model runs checked it. The author has read and edited the abstract and the
introduction (4 and 5 October); the rest of the text has been checked by model runs only. The sentence of the
abstract on the second proof of optimality, and its mentions in Sections 1.6 and 1.7, were added later on
5 October at the author's request. Section 10, the sentence of the abstract on stability and their mentions in
Sections 1 and 12 and Appendices D and E were added on 6 October at the author's request; the author has not read
Section 10 yet. Section 11, the sentence of the abstract on the single estimate and the passages that refer to
Section 11 in Sections 1, 2, 8 and 10 and Appendices D and E were added later on 6 October at the author's
request; no person has read Section 11 yet. On 6 October the author said that they had read nothing past
Section 1, and the text has said since then that the author has proofread and edited the abstract and Section 1. Sections 8, 10 and 11 and Appendices D and E were then revised for the simplified
libraries of the formalization, also on 6 October; no person has read the revision. Last, at the author's request,
the description of the formalization moved from Section 12 to Appendix D, so that Section 12 lists open questions
only; Section 1 gained a remark on the second proof of optimality at the end of Section 1.4 and Section 1.5, on
the strategy of the stability proof and the certificate; and the title, formerly *Uniqueness of Gerver's sofa*,
now names the stability. No person has read these new parts of Section 1.
[How it was made](#how-it-was-made) says what has been compared with what, and
[Before submitting](#before-submitting) lists what only the author can settle.

## Files

| File | Content |
| --- | --- |
| [`main.tex`](main.tex) | the preamble, the title and abstract, and the list of sections |
| [`macros.tex`](macros.tex) | the notation |
| [`sections/01-introduction.tex`](sections/01-introduction.tex) … [`12-questions.tex`](sections/12-questions.tex) | Sections 1 to 12 |
| [`sections/a0-baek.tex`](sections/a0-baek.tex), [`a1-gerver.tex`](sections/a1-gerver.tex), [`a2-corrections.tex`](sections/a2-corrections.tex), [`a3-lean.tex`](sections/a3-lean.tex), [`a4-ai.tex`](sections/a4-ai.tex) | Appendices A (pictures of Baek's argument), B (Gerver's sofa), C (corrections to Baek's statements), D (the Lean formalization: the libraries and the checks, the statements of record and a dictionary), E (the use of AI) |
| [`refs.bib`](refs.bib) | the bibliography |
| [`figures/`](figures) | the figures: `make_figures.py` draws thirteen of them as PDF files from the definitions of the formalization (it imports `scripts/figures/`); the fourteenth is TikZ, in Section 3 |
| [`main.pdf`](main.pdf) | the compiled manuscript (117 pages) |
| [`Makefile`](Makefile) | `make` builds the PDF, `make figures` redraws the figures, `make arxiv` builds the upload |

## Build

```sh
make            # main.pdf: latexmk with pdflatex and bibtex (amsart, tikz, cleveref, microtype, lmodern)
make figures    # redraw figures/*.pdf: python3 with numpy and matplotlib
make arxiv      # arxiv/gerver-sofa-uniqueness.tar.gz, after a test build of the archive alone
```

The archive holds `main.tex`, `macros.tex`, `main.bbl`, `sections/` and `figures/*.pdf`: arXiv builds from the
`.bbl`, so the bibliography is not rebuilt there. The manuscript compiles with a standard TeX Live and without
shell escape; the test build of the archive (three `pdflatex` runs, no `.bib`) gives the same 117 pages and no
undefined reference.

## What the manuscript claims, and on what

- Theorem 1.1 is proved in the text, from Baek's results (arXiv:2411.19826, version 1; its numbering is
  used throughout, as `[1, Thm. x.y.z]`) which Section 2 records as Facts, with the corrections that the
  audit of that paper found (Appendix C). Section 3 reduces the theorem to caps and outlines the proof;
  Sections 4 to 9 prove it.
- The text is a translation of the formalization. Every result of the paper is proved in Lean 4 in the
  repository, and Appendix D gives the statement of record in mathematical notation, with the definitions that
  make it meaningful, and a dictionary from each result of the text to its Lean declarations. The Challenge
  states Theorem 1.1. Theorem 8.5, Corollary 9.4, Lemma 9.5 and Corollary 9.6 were added to the libraries on
  4 October (commit `952812d`), and Fact 2.14 and the second proof of optimality (now Lemma 6.10 and Remark 8.6)
  on 5 October (commits `3af9279` and `51c9be1`). Appendix D says what the machine check does and does not give, and
  Appendix E who and what wrote which part.
- Remark 8.6, at the end of Section 8, outlines a second proof of optimality (Baek's theorem) from the maximizing
  caps, with Baek's own bound for $\mathcal Q$ and the equality analysis of Section 8; Section 11 writes it out with
  the certificate in their place (Proposition 11.3, Theorem 11.4). It uses Baek's results recorded as Facts, except Fact 2.15 (Baek's Theorem 1.1.1), and with it
  Theorem 1.1 and Corollary 9.4 hold without Baek's Theorem 1.1.1. ChatGPT Pro 6 wrote it in Lean in pull request
  #5, merged on 5 October; the formalization proves it in the modules `MovingSofaUniqueness.MaximizerRoute` and
  `MovingSofaUniqueness.Maximizing`, the second shared with Section 11, and a second audit, run by the continuous
  integration, checks that they use neither Baek's Theorem 1.1.1 nor the results from which Baek derives step (3)
  of Section 1.3 from the balance. Section 8.4 presented it in full until 6 October, when, at the author's request,
  it was shortened to this remark and Lemma 6.10 (the right-angle motion, at the end of Section 6).
- Section 10 proves the stability (Theorems 10.1 to 10.4), translated from the library `MovingSofaStability`. ChatGPT
  Pro 6 wrote that library and the argument in pull request #8, without compiling it; Claude Opus 5.5 made it compile
  on 5 October, and the Challenge states Theorems 10.1 to 10.3 since 6 October (commit `92b2f86`). The cap estimate,
  Theorem 10.4, is proved in the library and not stated in the Challenge.
- Section 11 derives optimality, uniqueness and stability from one estimate (Theorem 11.1, the coercive
  certificate: Lemma 10.6 and Theorem 10.4 (a) together), translated from the library `MovingSofaExtremal`, the
  module `MovingSofaUniqueness/Maximizing.lean` and the theorem `coercive_certificate` of
  `MovingSofaStability/CapEstimate.lean`. Its classification of the maximizing right-angle caps
  (Proposition 11.3) replaces the equality analysis of Section 8 (Lemmas 8.1 and 8.2, Proposition 8.3); its
  optimality and uniqueness theorems (Theorems 11.4 and 11.7) use neither Baek's Theorem 1.1.1 nor his Theorems 1.5.2 and 8.1.1 (2) and the balance
  results that the audit lists. The stability proof of Section 10 takes the sign of the deficit, and the
  optimality and uniqueness of its compactness step and of its case of zero deficit, from these theorems, and its
  local cap estimate from the certificate. ChatGPT Pro 6 wrote the route in pull request #9, without compiling it; Claude
  Opus 5.5 compiled and completed it on 6 October, and `scripts/AuditCoerciveRoute.lean` checks its
  dependencies. `SolutionCoercive.lean` proves the fifteen theorems of the Challenge again, taking optimality,
  uniqueness and the stability of Theorems 10.1 and 10.2 from the route; Comparator checks it against the Challenge
  as it checks `Solution.lean`, through `SolutionCoerciveComparator.lean`, which states its theorems under the
  Challenge's names.
- Three Facts (the equality case of Baek's bound needs a proof that avoids $\mathcal N(K)\subset K$; the structure
  of Gerver's sofa; the height of its rotation path) are known only from the formalization.
- The links to the repository are pinned to commit `701ec744a73a5fe21c3ac1703ac83cf31df853c2`, on which the
  continuous integration and Palomar's preflight passed; it is the commit prepared for version 5 of the Palomar
  entry. Version 4 registers the earlier commit `16653ae`, whose Challenge has the twelve theorems other than those
  of stability.
- Figures are computed from the definitions of the formalization; the facts that a caption states are checked
  by `assert`s in the scripts.

## Before submitting

These are the author's to settle; the text settles none of them.

1. The title page names the author only. The AI models are not authors and are described in Section 1.6 and
   Appendix E. Check that wording against arXiv's current policy on generative-AI tools, and against what you are
   ready to stand behind: the text says that the author has proofread and edited the abstract and Section 1, except
   the end of Section 1.4 and Section 1.5, and has not yet read the other sections, and that the argument has not
   yet been refereed.
2. Lean's kernel has checked the formal proofs, not the text. The text is a translation of them by a model,
   compared with the Lean statements, proof by proof, and with Baek's paper by independent model runs (below). A
   human read of Sections 2 to 12 and of the new parts of Section 1 is the check that is missing, and Appendix D's paraphrase of the Lean
   definitions is the place where nothing but model checks stand behind the text.
3. Baek's paper is a preprint, and all the numbers of its results are those of arXiv version 1. If a later
   version renumbers, the citations `\baek{...}` and Appendices C and D need updating.
4. The suggested primary category is math.MG (Metric Geometry), with MSC 2020 codes 52A38, 52A40 (primary) and
   52A10, 49Q10, 68V20 (secondary), as in `main.tex`; a cross-list to cs.LO would reflect the formalization. A
   first submission to a category may need an endorsement, and the licence is chosen in the submission form.
5. For the submission form: the title is *Uniqueness and stability of Gerver's sofa*, the author The-Anh Vu-Le,
   and the comments "117 pages, 14 figures. The proofs, together with Baek's, are formalized in Lean 4:
   <https://github.com/vltanh/lean4-moving-sofa>". The abstract (1,546 characters, plain text) is:

   > The moving sofa problem asks for the largest area of a closed connected planar shape that can be moved
   > around the right-angled corner of a hallway of unit width. Gerver found a shape of area 2.2195... in 1992
   > and conjectured that it is optimal; Baek proved this in 2024. We prove that Gerver's sofa is the only
   > optimal shape: every moving sofa of the same area is a rotated and translated copy of it. To prove
   > optimality, Baek first bounds the area of any large moving sofa by that of a special shape with two
   > geometric properties. Baek then bounds the area of every shape with these properties by a concave functional
   > whose largest value is the area of Gerver's sofa. Since this chain of inequalities passes through the
   > special shape, it says nothing about the shape of a moving sofa of maximal area. To prove uniqueness, we
   > show that every moving sofa of maximal area has the same two properties, so that the functional bounds its
   > area directly. Equality now forces the sofa to be Gerver's. This argument does not use the value of the
   > maximal area, so it also gives a second proof of optimality. We prove, moreover, that the uniqueness is
   > stable: a moving sofa whose area is ε less than the maximum lies, after a translation, within Hausdorff
   > distance O(√ε) of Gerver's sofa, and the exponent 1/2 cannot be improved. We also derive optimality,
   > uniqueness and stability from one estimate for this functional. The proofs, together with Baek's, are
   > formalized in Lean 4 with Mathlib and checked by Lean's kernel, using only Lean's standard axioms.

6. `\date{October 2026}` in `main.tex`.
7. [`README.md`](../../README.md) and [`CREDITS.md`](../../CREDITS.md) list the four versions of the Palomar
   entry; `CREDITS.md` has a section for each later round. Version 4 registers `16653ae`, and the libraries have
   grown since: the Challenge now has fifteen theorems, and `formalization.yaml` describes them. Palomar's preflight
   passed on the cited commit `701ec74` on 6 October, with one warning (the Challenge exceeds the preferred review
   size of 300 lines); submitting it as version 5 is for the author.

## How it was made

Section numbers below are those of the time: the formalization section was Section 10 until 6 October, when
Section 10 became the stability and the formalization section Section 11; later that day Section 11 became the
derivation of the three results from one estimate, and the formalization section Section 12. At the end of that
day, the description of the formalization moved to Appendix D.1, and Section 12 kept only the open questions.


The manuscript was written on 4 October 2026 by Claude Sonnet 5.5 in Claude Code (version 2.1.289), at the
author's request ("prepare an arXiv paper for the uniqueness of Gerver's sofa"), from the Lean library,
[`docs/proof/`](../proof/README.md), [`REPORT.md`](../../REPORT.md), [`CREDITS.md`](../../CREDITS.md) and the
LaTeX source of Baek's paper. The text is a translation of the formal proofs, in the order of
`MovingSofaUniqueness/`; the figures are drawn from the definitions of the formalization.

Nine sub-agents read the manuscript; none could edit it, and the main session applied the findings. The first
eight ran at once, after the first full draft:

| Scope | Model | What it checked | Main findings |
| --- | --- | --- | --- |
| §2.1 to 2.3, §3 | Opus 5.5 | Facts against Baek's TeX and the Lean statements; Proposition 3.2 | "standard position" was false without "with rotation angle ω"; E3 described backwards; the polyline's abscissa increases, not decreases; "every cap contains O and o_ω" had no proof |
| §2.4 to 2.6, Appendix A | Opus 5.5 | Facts; Romik's system re-solved from the appendix's 28 equations (residual 5·10⁻⁵¹) | every printed number correct to ten places; $\mathcal P_K$ and $\mathcal Q$ not defined; $\mathbf D'$ and $\mathbf B'$ jump at $t_1$, $t_4$; wrong dictionary entries |
| §4, §5 | Opus 5.5 | every constant and the selection argument | no false step; the limit argument of the text followed another route than the Lean's; notation clashes ($C$, $P$, $F$, $R$, $K_j$) |
| §6, Prop. 3.2, definitions | Opus 5.5 | the triangle lemma and Fact 6.5 numerically; the turning lemma | no false step; wrong range for Baek's Thm. 1.5.2; a wrong limit for $z^\circ$ |
| §7 | Opus 5.5 | Lemmas 7.1 to 7.3 on about 2,100 random polygon caps; the rest by hand | Lemma 7.4 was false at the right endpoint of the interval; Lemma 7.5 needed $C\ge0$; a gap in Lemma 7.7 |
| §8, §9 | Opus 5.5 | the equality argument, the tangent equations, regular closedness (numerically) | a sign error in Lemma 8.2; what Lean does not state; the niche's description omits the floor segment; the rotation in Theorem 1.1 is trivial |
| §1, §10, Appendices B and C, bibliography | Sonnet 5.5 | every claim about the repository, every Lean name, Appendix C against `Challenge.lean`, the bibliography | Romik did not find Gerver's boundary in closed form; overclaims about what the Lean covers; E15 missing from Appendix B |
| the whole manuscript, as a reader | Opus 5.5 | a cold read of the PDF without the Lean or Baek's TeX | the role of Mamikon's theorem was misdescribed; notation clashes; "Fact" was never defined; the machinery of §4 and §5 runs twice and the outline did not say so |

A ninth sub-agent (Opus 5.5) then checked the passages rewritten after these reports. It found one false
statement (the introduction's argument that no rotation is needed, now Corollary 9.6, missed rotations by $\pi$), one gap (the position of the
ends of the upper boundary had no proof; it is now Lemma 2.6), five wrong or misplaced citations, and a number of
statements about what Lean does and does not state; they were applied by the main session, which no one has
reviewed again. It confirmed that claim and its numbers by an independent computation, and the rewritten
Lemmas 7.1 to 7.7 and 8.1 to 8.2.

The main session also ran its own numerical checks, with the scripts in the session's scratch directory
(not kept): the formulas of Lemma 7.1 and the bound of Lemma 7.2 on random polygon caps (546 and 406 cases,
no failure), the inequalities of Fact 6.5 over the whole range of $\omega$, and the parameters of Appendix A, the
widths of Gerver's sofa and the point $t_*$ of Figure 7.

A second pass followed on 4 October, in the same session and at the author's request: to correct the Palomar
versions and the dates in the repository's records, and to humanize the introductory speech and the informal
passages while keeping the academic tone of a formal paper (the humanizer skill). It rewrote Section 1 (the
announcement "Four remarks." became plain paragraphs, Baek's four steps became a list, the long strategy paragraph
was split, the stress italics were removed), the lead-in of Section 3, the provenance paragraphs and the acknowledgments
of Section 10, two passages of the abstract, and 28 passages of Sections 2 and 4 to 9 and Appendices A to C. It
changed the run-in headings from bold to italic and rewrote this file. Section 10.2 now also lists the ninth
sub-agent above, and Section 10.1 says that version 4 of the Palomar entry registers the commit that it cites.
[`README.md`](../../README.md) and [`CREDITS.md`](../../CREDITS.md) now list the four versions of the entry and
date the rounds from 1 to 3 October.

Two more sub-agents (Opus 5.5) took part, neither able to edit. One read Sections 2 and 4 to 9 and the
appendices for the same patterns and reported 29 passages; 28 were applied, some in modified form, and one
sentence was kept. The other compared the text before and after the pass for any changed claim, in two rounds. In
the first it found a sentence that the rewrite had made false ("hold only for" where the text had said that the
properties are known only for Baek's cap), a dropped claim (not every rotated copy of Gerver's sofa is a moving
sofa), a pronoun that had lost its antecedent and several smaller points; in the second it found two wordings to
tighten and a conclusion that needed "so that $\theta=0$". The main session applied all of them.

A third pass followed the same day, in the same session and at the author's request. The author asked that the
text be a faithful translation of the formalization: that a result or a proof that the text has and the Lean does
not be put into the Lean when it is better and be removed from the text otherwise, that the text list no
differences from the Lean, and that it say nothing about the informal draft that preceded the formalization.

The Lean libraries were extended (commit `952812d`, by a sub-agent running Opus 5.5): a right-angle cap has the
sofa area of Gerver's sofa if and only if it is a horizontal translate of Gerver's cap (Theorem 8.5), the maximal
sofas are the moving sofas that a rigid map takes onto Gerver's sofa (Corollary 9.4), the width of Gerver's sofa
exceeds one in every direction but the vertical (Lemma 9.5), and no rotation is needed (Corollary 9.6). Three
helper lemmas that are not numbered results of Baek's paper now state the rotation angle; no numbered result and no
statement of the Challenge changed. The continuous integration and Palomar's preflight passed on that commit.

The text then followed the Lean. Sub-agents (Opus 5.5), one for each of Section 2, Sections 4 and 5, Section 6,
Section 7 and Sections 8 and 9, rewrote them to state what the Lean states, with its hypotheses and constants, and
to follow its proofs; the one for Section 2 first had four more sub-agents compare the section with the Lean line
by line. The existence proof of the penalized maximizers, the box and the constants of the lemmas of Sections 4 and
7, the cell lemma, the triangle lemma, the proofs that every cap contains $O$ and $o_\omega$ and the sine identity
for the sides of the polygon niche now follow the Lean; what the Lean does not state was deleted or reduced to what
it states (a remark with two counterexamples, an example of a cap, numerical values in the proof that no rotation is
needed). Another sub-agent rebuilt Appendix C, now one row for each of the 67 results, and corrected Appendix B.
Sections 1 and 10 no longer list differences or discuss the informal draft; ChatGPT Pro 6 is credited as the writer of
the first version of the proof in one sentence of Section 1.4 and in Section 10.2. The paper grew from 49 to 63 pages.

Five sub-agents (Opus 5.5), each assigned some sections and appendices, compared the text with the Lean in two
rounds, without editing. The first round found no false step. It found many places where the text said more, less
or something other than the Lean, some wrong E-labels and dictionary entries and a few claims that the Lean does
not state; the second round found smaller points. They were applied by the main session or by the sub-agents that had
rewritten the sections. The edits that followed the second round, about twenty small ones, were not checked again.

Figures from the session transcript, from 08:04 to 14:15 CDT on 4 October (computed with the
formalize-math-paper skill's `session_stats.py`; they include the writing of the first draft and the second and third
passes):

- elapsed time: 6 hours 11 minutes;
- sub-agents: 27 (4 of them launched by another sub-agent), at most 10 at once, about 11.2 hours of work;
- tool calls: 2,476 by the sub-agents, 710 by the main session;
- tokens of the sub-agents: 4.63 million output, 22.40 million input, 646 million cache reads; of the main
  session: 1.24 million output, 2.66 million input, 296 million cache reads;
- model calls: 1,907 by the sub-agents (all to `claude-opus-5-5`) and 700 to `claude-sonnet-5-5`, of which 589 by the main session.

The third pass alone, from 11:48 to 14:15: 2 hours 26 minutes, 16 sub-agents, about 7.3 hours of
sub-agent work; [`CREDITS.md`](../../CREDITS.md) has its figures.

On 4 and 5 October the author walked through the abstract and the introduction with Claude (Sonnet 5.5, then Opus
5.5, in Claude Code) and had them rewritten sentence by sentence. The same session moved the corrections to Baek's
statements out of Section 2 into Appendix C, moved the account of the use of AI into a new Appendix E, added
Appendix A with five figures of Baek's argument (among them a maximum polygon cap computed numerically, whose
balance the script asserts), and rewrapped the source to 80 columns (the text of the compiled PDF was compared before
and after). These edits were not checked by independent model runs.

On 5 October, at the author's request, a session of Claude Opus 5.5 (Claude Code 2.1.289) merged pull request #5,
in which ChatGPT Pro 6 had written in Lean a second proof of optimality from the maximizing caps, with a plan
for presenting it in the manuscript; the code had never been compiled. It compiled without change, and its audit
passed, also after the session extended the audit to the results from which Baek derives step (3) from the
balance (commits `3af9279` and `51c9be1`; the continuous integration and Palomar's preflight passed on the second).
The session then wrote, from the Lean, Fact 2.7 (Baek's existence of a cap with the largest sofa area), Section 8.4
(Lemmas 8.6 and 8.7, Theorem 8.8 and two paragraphs on what the second proof gives and uses), the paragraph that
ended Section 1.4, and the matching passages of Sections 1.5, 1.6, 2, 3 and 10 and Appendices C to E. The plan
suggested a subsection at the end of Section 8, a paragraph in the introduction and the formalization's entries;
the text follows it, with Fact 2.7 added because the second proof cites Baek's existence result on its own. Two
sub-agents (Claude Opus 5.5), neither able to edit, then read the new text: one compared it with the Lean and
found no mathematical error, but a commit pin that did not yet contain the new code (fixed by this pin) and a proof
route that the text had shortened (restored); the other read it for its prose and for the author's rules, and
most of its rewrites were applied. The figures of Appendix A now float with `[htbp]`, as the longer text had pushed
two of them onto an overfull page; the source was rewrapped to 80 columns as before, and the text of the PDF was
compared before and after the rewrap.
The author then had the paragraph on the second proof that ended Section 1.4 removed, as unnecessary for now, and
one sentence added to the abstract instead ("This argument does not use the value of the maximal area, so it also
gives a second proof of optimality."); Section 1.5 now introduces the second proof with a reference to Section
8.4, and the text calls it the second proof of optimality throughout.

On 6 October, at the author's request ("yes" to a stability section), a session of Claude Opus 5.5 (Claude Code
2.1.289) added the stability, which the library `MovingSofaStability` had proved since the evening before (pull
request #8, ChatGPT Pro 6's code made to compile in the same session). It first stated the three main theorems in the
Challenge (commit `92b2f86`, then cited by the manuscript; Comparator accepts the fifteen theorems and the continuous
integration passed). A sub-agent (Opus 5.5) wrote Section 10 and its rows of the dictionary from the Lean; three more
sub-agents, launched by it, compared every statement and proof of the section with the Lean, part by part, and found
two statements of lemmas with a wrong quantifier order or a property that the Lean does not export, four proof steps
with a wrong or missing reason, and a lemma cited outside its hypotheses; all were corrected. The main session wrote
the sentence of the abstract, the passages of Sections 1 and 11 and Appendices D and E on stability, renumbered the
formalization section to 11, and repinned the citation of the repository. Two more sub-agents (Opus 5.5), neither able
to edit, then read the new text: one against the Lean and the repository, which found the mathematics of Section 10
in agreement with the Lean and seven problems in the surrounding claims (the Challenge states only part (b) of Theorem
10.3, an introduction sentence that said the opposite of the exponent result, a stale section number, a claim about
the figure script made false by the new citation, among others); the other for its prose, whose items were applied
in Section 10 by the writing sub-agent and elsewhere by the main session. One of the three comparing sub-agents also
found a sign error in Section 2, which said that the last term of $\mathcal M_K$ is $\mathcal J$ of the arc of $K$,
where it is $-\mathcal J$; the main session corrected it. The changes made after these two reviews were not checked again.

Later on 6 October, at the author's request (integrate pull request #9, "a unifying theorem that provide an
alternative proof of optimality, uniqueness, and stability at once", as a new section or subsection), the same session
of Claude Opus 5.5 integrated the pull request, in which ChatGPT Pro 6 had derived optimality and uniqueness from two
estimates of the stability library without compiling the code. The session made the code compile, moved the stability
proof onto it, stated the certificate and the theorem that gives the three results (commits `ae0162a` and `70ccc8a`),
and merged the pull request as `94a1bcf`, on which the continuous integration passed and which the manuscript then
cited. Following the pull request's notes, which suggested keeping Baek's proof and Section 8.4 and presenting the
three results in that order from the common estimate, the derivation became a new Section 11 and the formalization
section Section 12. A sub-agent (Opus 5.5) wrote Section 11 and the passages that refer to it from the Lean. Three
sub-agents launched by it compared the text with the Lean part by part, and a fourth checked the passages rewritten
after their reports; they found an overstatement of the results that the derivation avoids, a proof of Theorem 11.7
(b) that took another route than the Lean's, citations of the sign of the deficit missing from Section 10, and an
overclaim in Section 12 about the exponent theorem, among others. The main session removed a paragraph that the
sub-agent had added at the end of Section 1.4, as the author had done for the second proof, wrote the sentence of the
abstract and the sentence of Section 1.5 on who has read Sections 10 and 11, and repinned the citation. Two more
sub-agents (Opus 5.5), neither able to edit, then read the new text. The first, against the Lean and the repository,
found the statements, proofs, numbers and history in agreement with the Lean, except a proof step that the Lean does
not take (that a translate of Gerver's cap is a cap), a hypothesis missing from a summary of Lemma 8.1, a lemma that
Appendix D listed as proved twice, gaps in Appendix E, and a stale PDF. The second, for the prose, proposed the present
opening of Section 11 and found terms used before their definition ("coercive certificate" in Section 10, "route" in
Section 12), mentions outside the section that were too long, steps without their reasons, and repetitions. Neither
found a mathematical error. The writing sub-agent applied both reports, with the main session's decisions on the
wording of the abstract and of Section 1.5; those edits were not checked again. The manuscript grew from 91 to 101
pages.
The author then confirmed the removal of the paragraph of Section 1.4 and said that they have not read anything past
Section 1; Section 1.5 and Appendix E now say that the author has proofread and edited the abstract and Section 1
and has not yet read the other sections. At the author's request ("use the best bound"), the stability proof now
carries the coefficient $2\sec\varphi$ of the cap estimate instead of weakening it to 80 (commit `a94bde6`):
Proposition 10.11 and the constants of the local recovery in Section 10 changed accordingly, and the manuscript then
cited that commit. The main session made these edits; they were not checked by another run.
At the author's request ("keep it as a remark, and say we have formalized that"), Section 8.4 was then folded into
Section 11: Lemma 8.7 became Lemma 11.4, Remark 11.6 records the second proof of optimality with Baek's own bound,
which the formalization proves, and Lemma 8.6 and Theorem 8.8 were dropped, as Proposition 11.3 and Theorem 11.5
state them. The writing sub-agent made the change and checked the remark against the Lean of the second proof; the
main session checked in the Lean the new claim of Section 11 on which results of Sections 4 to 9 use Baek's Theorem
1.1.1 (in the uniqueness library, only declarations of `Main` reach it). The docstrings of the second proof now cite
the remark (commit `6ed7657`, which the manuscript then cited). The manuscript had 99 pages.
At the author's suggestion ("why don't you put the remark at the end of 8?"), the remark then moved to the end of
Section 8 (Remark 8.6), rewritten to stand on its own, and the lemma on the right-angle motion to the end of Section 6
(Lemma 6.10), after Proposition 6.9, whose argument it reuses: the second proof uses nothing after Section 8. Section
11 got back its numbering (Theorem 11.4 for optimality, 11.7 for uniqueness, 11.8 for the three results). The writing
sub-agent made the move and checked the remark against the Lean of the second proof; the Lean did not change.

Later on 6 October, at the author's request (to simplify and consolidate the stability library and the other new code,
keeping the formalization of Baek's paper and the connection with formal-conjectures intact, and then to rewrite the
manuscript), the same session of Claude Opus 5.5 (Claude Code 2.1.289) simplified the new libraries. Commit `0b7978c`
put the steps from the two properties of the maximizing right-angle caps (their sofa area and their shape) to
optimality and uniqueness, which the second proof of optimality and the route of Section 11 had each written out, into
one module, `MovingSofaUniqueness.Maximizing`. The second proof became one module,
`MovingSofaUniqueness.MaximizerRoute`, and the route two, `MovingSofaExtremal.Main` and `MovingSofaExtremal.Unified`.
The results of `MovingSofaUniqueness.Rigidity` that the route and the stability library had proved again so as not to
import it (in `MovingSofaExtremal.HorizontalTranslation` and `MovingSofaStability.MamikonFoundation`) moved out of
`Rigidity` into the modules `MovingSofaUniqueness.Rigid` and `MovingSofaUniqueness.Mamikon`, and the copies were
removed; this left 86 of the 87 files of the stability library. Commit `830b03d` merged these 86 files, all but the
root file `All.lean`, into eleven modules, so that the library has 12 files, and removed 74 declarations that no
theorem used, among them the cap estimate with the constant 80. In commit `5817473`, eight sub-agents (Opus 5.5)
rewrote the eleven stability modules and the shared modules `MovingSofaUniqueness.Mamikon` and
`MovingSofaUniqueness.Maximizing` in parallel, each on its own copy of the build, keeping the names and statements of
the declarations that other modules, the solutions or the audits use. Commit `1856810` updated the documentation, and
commit `7b8c0a8` the docstring of `MovingSofaExtremal/All.lean`, which still listed the old modules; the manuscript
now cites `7b8c0a8`, and the continuous integration passed on it. The stability library went from 12,550 lines in 87
files to 7,585 in 12, and the route from 661 lines in 7 files to 235 in 3 at the cited commit; the main audit now
checks 5,860 declarations (6,062 before), the audit of the second proof 35, and that of the route 743 (958 before). No
statement of the Challenge, of a numbered result of Baek's paper or of a main theorem changed.

A sub-agent (Opus 5.5) then revised the manuscript, with five sub-agents (Opus 5.5), which did not edit, that compared
each part of Section 10 with the Lean before and after the rewrite. Section 10 lost the bound with the constant 80
(part (a) and the last claim of Proposition 10.9, and the sentence of the overview on it). In the proof of Lemma 10.21
(b), the bound for the part B of the roof is now sin t ≥ sin t₁ (it was sin t ≥ sin t₃), as in the rewritten proof.
The rewrite also leaves the split point t* of the proof of Lemma 10.15 (b) anywhere in (φ, π/2), where the text had
the midpoint; the text now does the same. The comparing sub-agents found no other change of argument, and four steps
where the text had differed from the Lean before the rewrite; these now follow the Lean too, three of them at the main
session's request: the proof of Theorem 10.3 (b) takes the bound from part (a) instead of deriving (b) from (c); Lemma
10.5 takes the convexity of the Mamikon terms from Baek's Lemma 8.3.3 and Theorem 7.4.2 instead of from (10.3); the
proof of Lemma 10.6 states how the derivatives of the area and of the core term extend to the enlarged domain (the
symmetry of the mixed area for all convex bodies, and Baek's proof of his Theorem 8.5.5 for any competitor); and Lemma
10.19 takes ψ₀ from the height of the rectangle under Gerver's roof. Appendix D names the declarations at the new
commit, with new conventions for the shared module and the merged stability modules; Remark 8.6, one sentence of
Section 11 on the steps that the two proofs share, Section 12 (the libraries, the second proof, the third audit) and
Appendix E describe the new modules and counts. Two more sub-agents (Opus 5.5), neither able to edit, then read the
revision, one against the Lean and the repository, the other for its prose. Neither found a mathematical error. Their
findings (a line count, the description of the files and of the rewritten modules, the wording of Remark 8.6, of
Appendix D and of several sentences of Sections 10 to 12, and a stale item of [Before submitting](#before-submitting))
were applied by the writing sub-agent and not checked again by another run. The manuscript has 100 pages.

At the author's request, Comparator then also checked the second solution, `SolutionCoercive.lean`: the main
session added `SolutionCoerciveComparator.lean`, which states its theorems under the Challenge's names, and the
configuration `comparator-coercive.json` (commit `3d3ea3e`; Comparator accepts both solutions, and the continuous
integration passed). The manuscript now cites that commit, and Appendix D.1 says so in two sentences.

Last, at the author's request ("Section 12 should just do the open questions. Formalization and use of AI can go
into appendix all. Paper can be renamed. Introduction should have 1.4 be strategy for the uniqueness proof, with a
short remark that this can be organized to be another optimality proof, then add section for the strategy for the
stability proof [...] with remark about how this leads to a unifying certificate for all 3 results"), the main
session (Claude Opus 5.5) reorganized the manuscript. The description of the formalization moved from Section 12 to
Appendix D.1 ("The libraries and the checks"), and Appendix D became "The Lean formalization"; the short Section
12.2 on the use of AI was dropped, as Appendix E already says what it said; Section 12 is now "Open questions",
followed by the acknowledgments. The title, formerly *Uniqueness of Gerver's sofa*, is now *Uniqueness and
stability of Gerver's sofa*. Section 1.2 is now "Uniqueness and stability", and Section 1.4, "The strategy of the
uniqueness proof", ends with a short remark on the second proof of optimality. The new Section 1.5, "The strategy of
the stability proof", follows Baek's chain (1.1): it makes step (4) quantitative, replaces step (3) near Gerver's
cap, adds the compactness argument, writes the chain (1.3) of the stability proof, and ends with a paragraph on the
coercive certificate, which says why it is called a certificate. Two runs of Claude Opus 5.5, neither able to edit,
then read the result, one for its accuracy against Sections 6 to 11 and the Lean, the other for its prose and its
structure against the author's request. Neither found a mathematical error. They found a false sentence (the
punctured sofas are at distance at least r, not exactly r, from the rigid images of Gerver's sofa), the term
"Baek's bound" used both for $\mathcal A(K)\le\mathcal Q(K)$ and for the maximality of $\mathcal Q$ at Gerver's
cap (now kept for the first only, in Sections 1, 2 and 11 and Appendix D), terms of Section 1.5 not defined in
Section 1, and stale passages here and in Appendices D and E. The main session applied their findings; these edits
were not checked again by another run. The manuscript has 102 pages. At the author's request ("Shorten 1.7
(Organization) because now we already discuss a lot in these two strategies subsection"), the main session then
cut Section 1.7 to a short outline that points to Sections 1.4 and 1.5 for the parts of the proof. At the
author's request ("Appendix E is a massive wall of text, can you simplify it and format it in bullet points for
readability?"), the main session then rewrote Appendix E as three bulleted lists (who wrote what, what was checked
and by whom, what a person has read), from 1,880 words to about 820; the round-by-round detail it left out is in
this file and in `CREDITS.md`, which the appendix cites. The manuscript has 101 pages.

At the author's request ("In Section 2, many of the definitions are not put in definition env, which make it hard
to find"), the main session put every notion of Section 2 into a definition with its name in the title: convex
bodies, the moving sofa (now with the hallway), standard position, the supporting hallway, the monotone sofa, the cap,
the niche and the sofa area, the cap of a sofa and the mirror image, polygon caps, the sides of the polygon niche,
polygon caps from support values, arm lengths, the iteration, the triples, convex-linear functionals, curve areas and
displacements, Mamikon terms, the rotation path and its shape, and Gerver's sofa. The facts that the text proved
along the way stay as text after the definitions; a word-level comparison found no change of content. Section 2 now
numbers 36 items, so its later Facts moved: Baek's existence of a cap with the largest sofa area is now Fact 2.14 and
his optimality theorem Fact 2.15. Then, at the author's request ("I feel like a lot of math is inlined instead of
being its own line, which makes it really hard to read"), seven sub-agents (Opus 5.5), one per group of section
files, moved long inline formulas into unnumbered displays: definitions by formulas, formulas with integrals, sums or
fractions, chains of inequalities that carry a step, lists of conditions, and every formula that the PDF broke across
lines; 387 displays in all, where the text had 125. A script compared every file before and after with the typography stripped: the
mathematics, the labels and the references did not change, and the only word changes are connectives that a display
needs ("and" between formulas of one display, "Then" before an aligned block), two piecewise definitions written as
cases, and Theorem 11.1, which now names the radius r of its bound. The manuscript has 117 pages.

At the author's request ("merge all this to main so we can submit Palomar v5"), the main session merged main into
this branch (commit `22f0b37`, on which the continuous integration passed) and moved the branch into main. Main had
one commit of its own, the comparison of the three formalizations of Baek's proof, with a proof of Baek's Theorem
2.1.3 along his argument; every name of Appendix D still exists after it. Appendix D.1 now says, as main's pages
do, that the Challenge restates formal-conjectures' definitions with its code rather than verbatim. The manuscript
cites `22f0b37` and has 117 pages.
Palomar's preflight, run at the author's request with Palomar's current pipeline, then passed on `701ec74`, the
commit prepared for version 5, and the manuscript now cites that commit.

## What has not been done

- The author has read and edited the abstract and the introduction; Sections 2 to 12 and the appendices have been
  read by model runs only. The text added on 5 October (Fact 2.14, the second proof of optimality, then Section 8.4,
  and the related passages) has been read by two model runs, and not by the author; Lemma 6.10 and Remark 8.6, into
  which that subsection was folded on 6 October, have not been checked by an independent run; the sentence of the abstract on the second proof, added at the
  author's request, has not been checked by a model run.
- The manuscript was not compiled by arXiv; only the local build and the test build of the archive were run.
- The Facts of Section 2 state Baek's results as the Lean states them; the Lean statements were compared with his TeX
  by the route check and by model runs, not proved again by hand. Baek's paper is itself unrefereed.
- Appendix D's paraphrase of the Lean definitions was compared with `Challenge.lean` by model runs, in two rounds.
- The edits after the second round of checks, the E-label marks added in it, and this file were not checked again.
- Version 4 of the Palomar entry registers `16653ae`; the Lean results of 4 and 5 October, the three stability
  theorems that the Challenge states since 6 October, and the derivation of Section 11, are not in a registered
  version yet; Palomar's preflight passed on the cited commit.
- Sections 10 and 11 and the passages on them added on 6 October have been read by model runs only, not by the
  author. Section 1.6 and Appendix E say that the author has proofread and edited the abstract and Section 1
  only (the author's statement of 6 October), except the parts of Section 1 written later; until 6 October the
  section on the use of AI said that the author proofread and edited the text.
- The remark at the end of Section 1.4, Section 1.5 and the reorganization of 6 October (the move of the
  description of the formalization to Appendix D, Section 12 reduced to the open questions, the new title) have
  been read by two model runs, not by the author; the edits that followed their reports were not checked again.
- The edits applied to Section 11 and its passages after the last two reviews (below) were not checked again.
- The revision of 6 October for the simplified libraries has been read by two model runs, not by the author; the
  edits that followed their reports were not checked again.
