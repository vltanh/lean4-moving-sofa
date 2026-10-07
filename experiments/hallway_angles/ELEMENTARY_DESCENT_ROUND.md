# Elementary-descent round: structural progress beyond finite denominator bounds

Starting checkpoint: `e5b064b6d6986580252ed5f58dc7d14eb0b77bb6` (143 commits in PR #7). The branch contained five commits beyond the preceding conversation's 138-commit checkpoint. In particular the algebraic-direction and elementary-tower lemmas were already present; they are reused explicitly, not reported as new discoveries of this round.

## Completed results

1. **Schanuel now implies full non-elementarity of the bend.** `SCHANUEL_NON_ELEMENTARITY.md` proves that every real solution of the compact contact/crossing equations in the stated hyperbolic domain has beta outside the algebraically closed exp/log field L. The model root is one such solution. This excludes finite nested elementary expressions, not merely rational angles or algebraic directions.
2. **Both equations are used.** The area equality makes exp(iT) algebraic over a finite elementary tower with T adjoined; the contact equation does the same for exp(2mu*T). Schanuel captures T and both exponentials inside the original tower. See `COUPLED_CONTACT_CAPTURE.md`.
3. **The minimal-tower descent closes without an algebraic-direction assumption.** Anchoring pi in the base allows the logarithmic final step to descend by a nonzero area coefficient. In the exponential final step, the frequency reconstructs the direction algebraically, and a coprime rational graph with a genuine nonzero pole excludes every nonconstant monomial substitution. Both cases contradict minimality.
4. **A finite-rank refinement is explicit.** An expression with at most m exp/log operations over Qbar and pi is excluded assuming Schanuel for ranks up to m+5. This bounds the required conjectural hypothesis for a proposed expression, not a proved case of Schanuel.
5. **The switching parameters also lie outside L conditionally.** `SCHANUEL_AUXILIARY_NON_ELEMENTARITY.md` treats T, alpha, the hyperbolic argument, and the reverse phase, as well as their exponential coordinates. The proof uses relative rank over conjugation-invariant finite towers and the nonsquare rational function X^2+5/4.

## What did not change

No unconditional proof of irrationality or non-elementarity was obtained. Schanuel is still an assumption. No new decimal digits, PSLQ search, Farey bound, geometric optimum range, or identification of beta_model with the unrestricted beta_c is asserted. The older numerical and geometric records were not rerun.

The new conclusion is qualitatively stronger than the preceding Schanuel-conditional irrationality theorem, but remains conditional. In particular the proof must not be summarized as an unconditional resolution of the original closed-form request.

## Validation

- Fourteen supporting rational identities were checked symbolically, including the contact normal form, resultant, nonconstant forward fraction, reverse fractional-linear inversion, area coefficients, and direction reconstruction.
- All 15 new local tests passed, none skipped. The tests include exact elementary counterexamples when a monomial-graph hypothesis is dropped.
- The first run had one expression-tree equality failure; it was fixed by comparing the cancelled difference with zero. No mathematical formula changed.
- The final combined runner checked the two committed source Git blob hashes and reproduced the successful 15-test run. The record is `results/elementary-descent-checks.json`.
- The local environment was Python 3.13.5 and SymPy 1.14.0. These tests do not formally verify the field arguments or Schanuel.
- No CI, workflow execution, or Lean build was attempted. All commits use `[skip ci]`.

A raw-source download was attempted and failed at DNS resolution. Repository reads and writes used the working GitHub connector. Newly written code ran locally and its Git blob hashes were matched to the committed files.

## Reading and reproduction

Read `SCHANUEL_NON_ELEMENTARITY.md`, `COUPLED_CONTACT_CAPTURE.md`, and `SCHANUEL_AUXILIARY_NON_ELEMENTARITY.md`. `ELEMENTARY_DESCENT_LIMITS.md` records the exact scope and failed shortcuts. `CLOSED_FORM_STATUS.md` is updated to distinguish the new conditional result from the retained finite unconditional bounds.

From this directory, using the optional packages in `requirements-closed-form.txt`:

    python elementary_descent_algebra.py
    python -m unittest -v test_elementary_descent
    python run_elementary_descent_checks.py --output results/elementary-descent-checks.json

## Sources and review

Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448, Sections 2–3: https://arxiv.org/html/math/9805045 . The source distinguishes the expression fields and explains reduced-tower methods; the coupled-system theorem is explicitly derived in this branch, not quoted from Chow.

Independent mathematical scrutiny should focus on capture, the rational-span saturation argument, descent in the two last-step cases, and the auxiliary relative-rank reductions. Symbolic algebra checks do not referee these logical steps. No publication-priority claim or automatic transfer to the unrestricted geometric transition is made.
