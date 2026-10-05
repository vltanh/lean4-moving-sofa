# Fourth round: audit, stronger ranges, and global comparisons

Starting checkpoint: `69d0b5f15b4497c4ef4bcac265acb80706083b4f` (55 commits in PR #7).

The task is to strengthen the mathematical results, not only to increase the numerical search resolution. Earlier analytic statements are proof drafts and will be audited before they are used as premises. No CI, workflow action, or Lean build will be attempted. New work stays within this experiment.

## Priorities

1. Audit the cap-area, canonical-corner, width, and alignment steps for hidden geometric assumptions. A counterexample or proof gap takes priority over extending a claim.
2. Try to extend the reverse-class theorem from bends at least 120 degrees to all obtuse bends, using a sharper crossing argument rather than assuming it.
3. Seek stronger unrestricted statements: quantitative alignment, stability, limiting shape, or exact optimality on a nontrivial parameter interval.
4. Investigate the forward/reverse comparison without equating a crossing of local numerical candidates with a global phase transition.
5. Keep exact analytic arguments, exact-arithmetic certificates, and floating-point experiments separate. Commit successful and failed routes as individual checkpoints.

## Initial source check

The current primary-source search reconfirms that Xingyi He's arXiv:2608.11206 reports a numerical crossing of local motion branches, not a proved global transition. Hexagon 2610.00011 describes Guttesen's conjectural generalized Gerver family for bends at most 90 degrees. Neither abstract supplies a global theorem for the middle-angle regime. No claim of novelty is inferred merely from these searches.

A direct clone failed because the runtime could not resolve github.com. The GitHub connector is working and is used for repository reads/writes. This is not a CI attempt.
