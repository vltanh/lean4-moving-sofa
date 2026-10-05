# Uniqueness of Gerver's sofa: the manuscript

A LaTeX manuscript, prepared for arXiv, of the theorem that Gerver's sofa is the only maximal moving
sofa: every moving sofa of the same area is a rotated and translated copy of it, as a set. It follows the
formalization in this repository and cites it for the machine-checked statement; the Lean statement is
`Baek.gerver_sofa_unique` in [`Challenge.lean`](../../Challenge.lean).

This is a draft for the author to read. An AI model (Claude Sonnet 5.5, in Claude Code) wrote the text from
the Lean library, the illustrated text of the proofs in [`docs/proof/`](../proof/README.md) and the text of
Baek's paper, and independent model runs checked it. The author has read and edited the abstract and the
introduction (4 and 5 October); the rest of the text has been checked by model runs only.
[How it was made](#how-it-was-made) says what has been compared with what, and
[Before submitting](#before-submitting) lists what only the author can settle.

## Files

| File | Content |
| --- | --- |
| [`main.tex`](main.tex) | the preamble, the title and abstract, and the list of sections |
| [`macros.tex`](macros.tex) | the notation |
| [`sections/01-introduction.tex`](sections/01-introduction.tex) … [`10-formalization.tex`](sections/10-formalization.tex) | Sections 1 to 10 |
| [`sections/a0-baek.tex`](sections/a0-baek.tex), [`a1-gerver.tex`](sections/a1-gerver.tex), [`a2-corrections.tex`](sections/a2-corrections.tex), [`a3-lean.tex`](sections/a3-lean.tex), [`a4-ai.tex`](sections/a4-ai.tex) | Appendices A (pictures of Baek's argument), B (Gerver's sofa), C (corrections to Baek's statements), D (the Lean statement and a dictionary), E (the use of AI) |
| [`refs.bib`](refs.bib) | the bibliography |
| [`figures/`](figures) | the figures: `make_figures.py` draws thirteen of them as PDF files from the definitions of the formalization (it imports `scripts/figures/`); the fourteenth is TikZ, in Section 3 |
| [`main.pdf`](main.pdf) | the compiled manuscript (66 pages) |
| [`Makefile`](Makefile) | `make` builds the PDF, `make figures` redraws the figures, `make arxiv` builds the upload |

## Build

```sh
make            # main.pdf: latexmk with pdflatex and bibtex (amsart, tikz, cleveref, microtype, lmodern)
make figures    # redraw figures/*.pdf: python3 with numpy and matplotlib
make arxiv      # arxiv/gerver-sofa-uniqueness.tar.gz, after a test build of the archive alone
```

The archive holds `main.tex`, `macros.tex`, `main.bbl`, `sections/` and `figures/*.pdf`: arXiv builds from the
`.bbl`, so the bibliography is not rebuilt there. The manuscript compiles with a standard TeX Live and without
shell escape; the test build of the archive (three `pdflatex` runs, no `.bib`) gives the same 66 pages and no
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
  4 October (commit `952812d`). Section 10 says what the machine check does and does not give, and who and
  what wrote which part.
- Three Facts (the equality case of Baek's bound needs a proof that avoids $\mathcal N(K)\subset K$; the structure
  of Gerver's sofa; the height of its rotation path) are known only from the formalization.
- The links to the repository are pinned to commit `952812dd097faa3565f042ed9172d40ec3c29848`, on which the
  continuous integration and Palomar's preflight both passed. Version 4 of the Palomar entry registers the
  earlier commit `16653ae`, which has the same Challenge.
- Figures are computed from the definitions of the formalization; the facts that a caption states are checked
  by `assert`s in the scripts.

## Before submitting

These are the author's to settle; the text settles none of them.

1. The title page names the author only. The AI models are not authors and are described in Section 1.5 and
   Appendix E. Check that wording against arXiv's current policy on generative-AI tools, and against what you are
   ready to stand behind: the text says that the author proofread and edited the text and that the argument has
   not yet been refereed.
2. `\address` and `\email` are commented out in `main.tex`.
3. Lean's kernel has checked the formal proofs, not the text. The text is a translation of them by a model,
   compared with the Lean statements, proof by proof, and with Baek's paper by independent model runs (below). A
   human read of Sections 2 to 10 is the check that is missing, and Appendix D's paraphrase of the Lean
   definitions is the place where nothing but model checks stand behind the text.
4. Baek's paper is a preprint, and all the numbers of its results are those of arXiv version 1. If a later
   version renumbers, the citations `\baek{...}` and Appendices C and D need updating.
5. The suggested primary category is math.MG (Metric Geometry), with MSC 2020 codes 52A38, 52A40 (primary) and
   52A10, 49Q10, 68V20 (secondary), as in `main.tex`; a cross-list to cs.LO would reflect the formalization. A
   first submission to a category may need an endorsement, and the licence is chosen in the submission form.
6. For the submission form: the title is *Uniqueness of Gerver's sofa*, the author The-Anh Vu-Le, and the
   comments "66 pages, 14 figures. The proof, together with Baek's, is formalized in Lean 4:
   <https://github.com/vltanh/lean4-moving-sofa>". The abstract (1,127 characters, plain text) is:

   > The moving sofa problem asks for the largest area of a closed connected planar shape that can be moved
   > around the right-angled corner of a hallway of unit width. Gerver found a shape of area 2.2195... in 1992
   > and conjectured that it is optimal; Baek proved this in 2024. We prove that Gerver's sofa is the only
   > optimal shape: every moving sofa of the same area is a rotated and translated copy of it. To prove
   > optimality, Baek first bounds the area of any large moving sofa by that of a special shape with two
   > geometric properties. Baek then bounds the area of every shape with these properties by a concave functional
   > whose largest value is the area of Gerver's sofa. Since this chain of inequalities passes through the
   > special shape, it says nothing about the shape of a moving sofa of maximal area. To prove uniqueness, we
   > show that every moving sofa of maximal area has the same two properties, so that the functional bounds its
   > area directly. Equality now forces the sofa to be Gerver's. The proof, together with Baek's, is formalized
   > in Lean 4 with Mathlib and checked by Lean's kernel, using only Lean's standard axioms.

7. `\date{October 2026}` in `main.tex`.
8. [`README.md`](../../README.md) and [`CREDITS.md`](../../CREDITS.md) list the four versions of the Palomar
   entry and date the rounds from 1 to 3 October; `CREDITS.md` has a section for the Lean results of 4 October.
   Version 4 registers `16653ae`, and the libraries have grown since: whether to register a version 5, and to
   update `formalization.yaml`, which does not mention the new results, is for the author to decide.

## How it was made

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

## What has not been done

- The author has read and edited the abstract and the introduction; Sections 2 to 10 and the appendices have been
  read by model runs only.
- The manuscript was not compiled by arXiv; only the local build and the test build of the archive were run.
- The Facts of Section 2 state Baek's results as the Lean states them; the Lean statements were compared with his TeX
  by the route check and by model runs, not proved again by hand. Baek's paper is itself unrefereed.
- Appendix D's paraphrase of the Lean definitions was compared with `Challenge.lean` by model runs, in two rounds.
- The edits after the second round of checks, the E-label marks added in it, and this file were not checked again.
- Version 4 of the Palomar entry registers `16653ae`; the Lean results of 4 October are in the libraries but not in
  a registered version.
