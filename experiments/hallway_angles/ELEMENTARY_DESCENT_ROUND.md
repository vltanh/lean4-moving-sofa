# Elementary-descent round: replace finite denominator growth by a structural theorem

Starting checkpoint: `e5b064b6d6986580252ed5f58dc7d14eb0b77bb6` (143 commits in PR #7). The branch contains work beyond the preceding conversation's 138-commit checkpoint; the existing algebraic-direction and elementary-tower lemmas are reused explicitly, not presented as newly discovered here.

## Target

Try to prove, conditional on Schanuel's conjecture, that the analytic contact-model crossing is outside the smallest algebraically closed field containing the algebraic numbers and closed under exp and all complex logarithms. This would exclude finite elementary expressions, rather than only rational multiples of pi or algebraic directions. No new claim of proving Schanuel or an unconditional non-elementarity theorem is intended.

The route to audit is: an elementary bend gives a finite tower containing the reverse expression; the area equation makes exp(iT) algebraic over that tower with T adjoined; the contact equation and the two-argument capture lemma then force T into the tower. A final exponential/logarithmic step should descend using the actual coefficient identities. This must be checked separately for both types of last step; transcendence alone is insufficient.

## Validation and scope

- Recheck the rational forms, nonconstant and coprimality conditions, and every field-membership step.
- Run local exact-symbolic/algebraic tests where meaningful; tests are not a formal verification of a Schanuel-conditional argument.
- Retain any failed descent or excluded shortcut instead of replacing the goal with more decimal digits.
- Keep the contact-model crossing distinct from the unrestricted geometric transition.
- No CI, workflow execution, or Lean build will be attempted. Commits use `[skip ci]`.

## Primary source

Timothy Y. Chow, *What is a closed-form number?*, American Mathematical Monthly 106 (1999), 440–448, especially Sections 2–3 and the discussion of Liouvillian numbers, Lin's result, and reduced towers: https://arxiv.org/html/math/9805045 . The descent for these particular equations will be proved in full rather than attributed to that paper.
