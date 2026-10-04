# Uniqueness of Gerver's sofa: the manuscript

A LaTeX manuscript, prepared for arXiv, of the theorem that Gerver's sofa is the only maximal moving
sofa: every moving sofa of the same area is a rotated and translated copy of it, as a set. It follows the
formalization in this repository and cites it for the machine-checked statement; the Lean statement is
`Baek.gerver_sofa_unique` in [`Challenge.lean`](../../Challenge.lean).

**Status: a draft for the author to read.** The text was written by an AI model (Claude Sonnet 5.5, in Claude
Code) from the Lean library, the illustrated text of the proofs in [`docs/proof/`](../proof/README.md) and the
text of Baek's paper, and checked by independent model runs. No person has checked it.
[How it was made](#how-it-was-made) says what has been compared with what, and
[Before submitting](#before-submitting) lists what only the author can settle.

## Files

| File | Content |
| --- | --- |
| [`main.tex`](main.tex) | the preamble, the title and abstract, and the list of sections |
| [`macros.tex`](macros.tex) | the notation |
| [`sections/01-introduction.tex`](sections/01-introduction.tex) … [`10-formalization.tex`](sections/10-formalization.tex) | Sections 1 to 10 |
| [`sections/a1-gerver.tex`](sections/a1-gerver.tex), [`a2-corrections.tex`](sections/a2-corrections.tex), [`a3-lean.tex`](sections/a3-lean.tex) | Appendices A (Gerver's sofa), B (corrections to Baek's statements), C (the Lean statement and a dictionary) |
| [`refs.bib`](refs.bib) | the bibliography |
| [`figures/`](figures) | the figures: `make_figures.py` draws eight of them as PDF files from the definitions of the formalization (it imports `scripts/figures/`); the ninth is TikZ, in Section 3 |
| [`main.pdf`](main.pdf) | the compiled manuscript (49 pages) |
| [`Makefile`](Makefile) | `make` builds the PDF, `make figures` redraws the figures, `make arxiv` builds the upload |

## Build

```sh
make            # main.pdf: latexmk with pdflatex and bibtex (amsart, tikz, cleveref, microtype, lmodern)
make figures    # redraw figures/*.pdf: python3 with numpy and matplotlib
make arxiv      # arxiv/gerver-sofa-uniqueness.tar.gz, after a test build of the archive alone
```

The archive holds `main.tex`, `macros.tex`, `main.bbl`, `sections/` and `figures/*.pdf`: arXiv builds from the
`.bbl`, so the bibliography is not rebuilt there. The manuscript compiles with a standard TeX Live and without
shell escape; the test build of the archive (three `pdflatex` runs, no `.bib`) gives the same 49 pages and no
undefined reference.

## What the manuscript claims, and on what

- **Theorem 1.1** is proved in the text, from Baek's results (arXiv:2411.19826, version 1; its numbering is
  used throughout, as `[1, Thm. x.y.z]`) which Section 2 records as *Facts*, with the corrections that the
  audit of that paper found (Appendix B). Section 3 reduces the theorem to caps and outlines the proof;
  Sections 4 to 9 prove it.
- The same theorem, and Baek's, are **proved in Lean 4** in the repository; Appendix C gives the statement in
  mathematical notation, with the definitions that make it meaningful, and a dictionary from each result of the
  text to its Lean declarations, with the places where the text and the Lean differ. Section 10 says what the
  machine check does and does not give, and who and what wrote which part.
- Three Facts (the equality case of Baek's bound needs a proof that avoids $\mathcal N(K)\subset K$; the structure
  of Gerver's sofa; the height of its rotation path) are known only from the formalization.
- **Remark 9.6** (the rotation in Theorem 1.1 is trivial, so every maximal sofa is a translate of Gerver's sofa) is
  an addition made while checking the draft. It is proved in the text from the Facts and numerical values of the
  parameters of Appendix A, and is not formalized.
- The links to the repository are pinned to commit `16653ae81e0e4f52a362bafae2ad3440100ad065`, on which
  the continuous integration and Palomar's preflight both passed.
- Figures are computed from the definitions of the formalization; the facts that a caption states are checked
  by `assert`s in the scripts.

## Before submitting

Things that are the author's to settle; none is settled by the text.

1. **Authorship and responsibility.** The title page names the author only; the AI models are not authors and
   are described in Section 1.4 and Section 10.2. Check the wording against arXiv's current policy on
   generative-AI tools, and against what you are ready to stand behind: the text says that no person has
   checked the argument independently of the formalization.
2. **Address and e-mail.** `\address` and `\email` are commented out in `main.tex`.
3. **Read the proofs.** Lean's kernel has checked the formal proofs, not the text; the text is a translation
   of them by a model, compared with the Lean statements and with Baek's paper by independent model runs
   (below). A human read of Sections 4 to 9 is the check that is missing. Remark 9.6 and Appendix C's
   paraphrase of the Lean definitions are the two places where nothing but model checks stand behind the text.
4. **Baek's paper is a preprint.** All the numbers of its results are those of arXiv version 1. If a later
   version renumbers, the citations `\baek{...}` and Appendices B and C need updating.
5. **Category, endorsement and licence.** Suggested primary category math.MG (Metric Geometry), with
   MSC 2020 codes 52A38, 52A40 (primary) and 52A10, 49Q10, 68V20 (secondary), as in `main.tex`; a cross-list to
   cs.LO would reflect the formalization. A first submission to a category may need an endorsement, and the
   licence is chosen in the submission form.
6. **Metadata** for the form. Title: *Uniqueness of Gerver's sofa*. Author: The-Anh Vu-Le. Comments: "49 pages, 9
   figures. The proof, together with Baek's, is formalized in Lean 4: <https://github.com/vltanh/lean4-moving-sofa>".
   Abstract (1,186 characters, plain text):

   > The moving sofa problem asks for the largest area of a planar region that can be moved around the
   > right-angled corner of a hallway of unit width. Gerver found a region of area 2.2195... in 1992 and
   > conjectured that it is optimal; Baek proved this in 2024. We prove that Gerver's sofa is the only optimal
   > region: every moving sofa of the same area is the image of Gerver's sofa under a rotation and a
   > translation, as a set. Baek's proof analyzes one particular maximizer, produced by a compactness
   > argument: after a rotation its sofa turns through a right angle, and it satisfies an injectivity condition;
   > a given maximizer need not be that one. We show that every maximizer has these properties, by
   > approximating a maximizing convex cap by polygonal maximizers of a penalized problem, which are almost
   > balanced, and passing to the limit. Equality in Baek's concave upper bound, whose terms are areas swept by
   > tangent segments, then forces differential equations for the difference of the support functions of the cap
   > and of Gerver's cap, which identify the cap, and a last argument recovers the region from its cap. The
   > proof, together with Baek's, is formalized in Lean 4 with Mathlib.
7. **Date.** `\date{October 2026}` in `main.tex`.
8. **Records in the repository.** [`CREDITS.md`](../../CREDITS.md) logs the formalization rounds and was not
   changed; the log of this manuscript is below. [`README.md`](../../README.md) still lists Palomar's versions 1
   and 2 only, and says the rounds ran "between 1 and 4 October", where `CREDITS.md` says 1 to 3 October.

## How it was made

The manuscript was written on 4 October 2026 by Claude Sonnet 5.5 in Claude Code (version 2.1.289), at the
author's request ("prepare an arXiv paper for the uniqueness of Gerver's sofa"), from the Lean library,
[`docs/proof/`](../proof/README.md), [`REPORT.md`](../../REPORT.md), [`CREDITS.md`](../../CREDITS.md) and the
LaTeX source of Baek's paper. The text is a translation of the formal proofs, in the order of
`MovingSofaUniqueness/`; the figures are drawn from the definitions of the formalization.

**Independent checks.** Nine sub-agents read the manuscript; none could edit it, and the main session applied
the findings. The first eight ran at once, after the first full draft:

| Scope | Model | What it checked | Main findings |
| --- | --- | --- | --- |
| §2.1–2.3, §3 | Opus 5.5 | Facts against Baek's TeX and the Lean statements; Proposition 3.2 | "standard position" was false without "with rotation angle ω"; E3 described backwards; the polyline's abscissa increases, not decreases; "every cap contains O and o_ω" had no proof |
| §2.4–2.6, Appendix A | Opus 5.5 | Facts; Romik's system re-solved from the appendix's 28 equations (residual 5·10⁻⁵¹) | every printed number correct to ten places; $\mathcal P_K$ and $\mathcal Q$ not defined; $\mathbf D'$ and $\mathbf B'$ jump at $t_1$, $t_4$; wrong dictionary entries |
| §4, §5 | Opus 5.5 | every constant and the selection argument | no false step; the text's limit argument differs from the Lean's; notation clashes ($C$, $P$, $F$, $R$, $K_j$) |
| §6, Prop. 3.2, definitions | Opus 5.5 | the triangle lemma and Fact 6.5 numerically; the turning lemma | no false step; wrong range for Baek's Thm. 1.5.2; a wrong limit for $z^\circ$ |
| §7 | Opus 5.5 | Lemmas 7.1–7.3 on about 2,100 random polygon caps; the rest by hand | Lemma 7.4 was false at the right endpoint of the interval; Lemma 7.5 needed $C\ge0$; a gap in Lemma 7.7 |
| §8, §9 | Opus 5.5 | the equality argument, the tangent equations, regular closedness (numerically) | a sign error in Lemma 8.2; what Lean does not state; the niche's description omits the floor segment; the rotation in Theorem 1.1 is trivial |
| §1, §10, Appendices B and C, bibliography | Sonnet 5.5 | every claim about the repository, every Lean name, Appendix C against `Challenge.lean`, the bibliography | Romik did not find Gerver's boundary in closed form; overclaims about what the Lean covers; E15 missing from Appendix B |
| the whole manuscript, as a reader | Opus 5.5 | a cold read of the PDF without the Lean or Baek's TeX | the role of Mamikon's theorem was misdescribed; notation clashes; "Fact" was never defined; the machinery of §4–5 runs twice and the outline did not say so |

A ninth sub-agent (Opus 5.5) then checked the passages rewritten after these reports. It found one false
statement (the introduction's argument for Remark 9.6 missed rotations by $\pi$), one gap (the position of the
ends of the upper boundary had no proof; it is now Lemma 2.6), five wrong or misplaced citations, and a number of
statements about what Lean does and does not state; they were applied by the main session, which no one has
reviewed again. It confirmed Remark 9.6 and its numbers by an independent computation, and the rewritten
Lemmas 7.1 to 7.7 and 8.1 to 8.2.

The main session also ran its own numerical checks, with the scripts in the session's scratch directory
(not kept): the formulas of Lemma 7.1 and the bound of Lemma 7.2 on random polygon caps (546 and 406 cases,
no failure), the inequalities of Fact 6.5 over the whole range of $\omega$, and the parameters of Appendix A, the
widths of Gerver's sofa and the point $t_*$ of Figure 7.

Figures from the session transcript, from 08:04 to 10:28 CDT on 4 October (computed with the
formalize-math-paper skill's `session_stats.py`; they include the writing of the first draft):

- elapsed time: 2 hours 24 minutes;
- sub-agents: 9, at most 8 at once, about 3.4 hours of work;
- tool calls: 721 by the sub-agents, 388 by the main session;
- tokens of the sub-agents: 1.43 million output, 3.92 million input, 170 million cache reads; of the main
  session: 0.82 million output, 1.80 million input, 181 million cache reads;
- model calls: 601 by the sub-agents (490 to `claude-opus-5-5`, 111 to `claude-sonnet-5-5`) and 343 by the main
  session (`claude-sonnet-5-5`).

## What has not been done

- No person has read the manuscript.
- The manuscript was not compiled by arXiv; only the local build and the test build of the archive were run.
- The statement and proofs of Section 2's Facts, which are Baek's, were compared with his TeX, not proved again;
  Baek's paper is itself unrefereed.
- Appendix C's paraphrase of the Lean definitions was compared with `Challenge.lean` by one model run.
- The edits that answered the ninth sub-agent's report (Lemma 2.6, the rewritten Remark 9.6, Section 10 and
  Appendices B and C) were not checked again.
