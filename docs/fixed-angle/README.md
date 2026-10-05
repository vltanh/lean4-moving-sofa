# Fixed net rotation angle: paper-first research

This directory starts a separate investigation of the optimal sofa with a prescribed **net rotation angle** in the usual unit-width, right-angled hallway. It does not alter the existing uniqueness manuscript or formalization.

## Read in this order

1. [PEM.md](PEM.md): proof-exploration memo, current results, dependency audit, and the precise remaining global hypothesis.
2. [relaxation.tex](relaxation.tex): the strongest exact result in this first pass. It verifies feasibility of Baek's relaxed candidate for `0 < omega <= 1` radian, derives a strict quadratic gap, and proves optimality plus uniqueness in the injective monotone class.
3. [small-angle.tex](small-angle.tex): the unrestricted small-angle expansion and uniqueness of the limiting rescaled missing corner, without an injectivity assumption.
4. [paper.tex](paper.tex): elementary bounds for every `0 < omega < pi/2`, the zero-angle equality case, and an abstract sharp-majorant interface.
5. [REVIEW.md](REVIEW.md): adversarial proof checks, sources, exploratory symbolic/numerical checks, and validation limits.

The three `.tex` files are standalone paper sources, not additions to the main uniqueness paper. Their chronology matters: the elementary competitor in `paper.tex` is improved by `small-angle.tex`, and the explicit relaxed candidate in `relaxation.tex` gives a still stronger exact lower bound. All remain useful for separating assumptions and proof dependencies.

## What the notes establish at paper level

Let `m(omega)` be the unrestricted supremal sofa area for the prescribed net angle.

| Scope | Result | Source |
| --- | --- | --- |
| Zero angle | `m(0) = 1`, attained only by a square up to translation in the fixed initial orientation | `paper.tex` |
| `0 < omega < pi/2` | An explicit feasible lower bound and a quantitative strict upper bound below `sec(omega)` | `paper.tex` |
| `omega -> 0+`, unrestricted | `m(omega) = 1 + omega^2/2 + o(omega^4)` | `small-angle.tex` |
| `o(omega^4)`-near-maximizers | A unique limiting rescaled missing-corner region in symmetric-difference area | `small-angle.tex` |
| `0 < omega <= 1`, unrestricted | A directly feasible sofa with exact area `1 + omega^2/2`, hence this is a lower bound for `m(omega)` | `relaxation.tex` |
| `0 < omega <= 1`, relaxed cap problem | A quantitative gap and a unique normalized maximizer of Baek's `A_1` | `relaxation.tex` |
| `0 < omega <= 1`, injective monotone class | Exact optimum `1 + omega^2/2` and a unique normalized optimizer, using Baek's explicitly stated conditional majorization | `relaxation.tex` |

The limiting missing region is

`D_0 = { (x,y) : x >= 0, y >= 0, x+y+(x-y)^2 < 3/4 }`,

with area `5/24`. The spatial scale is `omega^2`, so the missing-area scale is `omega^4`. This asymptotic rigidity result is not an exact positive-angle uniqueness theorem.

## What is not yet proved

**The exact unrestricted maximum and unrestricted uniqueness at positive angles are not established.** In particular, the feasible area `1 + omega^2/2` must not be reported as the unrestricted optimum.

The remaining majorization target is `A_omega(K) <= A_1(K)` for the relevant global fixed-angle maximizing caps. Baek's injectivity and fan-containment condition is one sufficient route. To obtain uniqueness for arbitrary original sofas, the argument must cover every maximizing envelope and include a valid equality recovery from that envelope.

A fixed-angle maximizer that also has a right-angle motion need not maximize the right-angle problem. The existing right-angle rigidity theorem cannot be used to bypass this missing step.

## Attribution and validation

Baek's *A Conditional Upper Bound for the Moving Sofa Problem*, arXiv:2406.10725v1, already contains `A_1`, the candidate cap `K_(omega,1)`, and its relaxed value `1 + omega^2/2`. These are explicitly attributed in `relaxation.tex`; the note does not claim to discover them. That note retains both hypotheses of Baek's Theorem 5.5 in its restricted-class application.

The starting repository reference is branch `paper/uniqueness-arxiv`, commit `1ade045936f32cf76572ee668ed8aa1627772bde`. The new paper proofs have not been independently refereed or formalized. TeX was not compiled. No Lean compilation, CI, workflow dispatch, or axiom audit was run. Every research commit uses `[skip ci]`; workflow files are unchanged.
