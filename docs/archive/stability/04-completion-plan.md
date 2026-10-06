# Completing unrestricted quantitative stability: working route

Base of this continuation: d61ef490455b04e9aa97d80ddef5bd30343b736b (PR #8).
No CI or Lean build is attempted. This entry records a research plan, not a completed theorem.

## Why the previous reduction cannot simply be asserted

Hausdorff closeness to Gerver does not imply membership in Ki: polygonal approximations already violate the absolute-continuity condition on curvature. Exact maximality in the selection/variation proof cannot be substituted for near-maximality without an estimate. A proof must either quantitatively repair the cap or avoid this regularity requirement.

## Route being checked

1. Enlarge the algebraic triple domain from Ki to normalized right-angle convex caps, retaining the linear body-inclusion and wall constraints. Audit the Q = affine minus six squares identity and the first-variation certificate at Gerver on this larger domain. The source's final derivative cancellation uses the competing support constraints, not regularity of the competing cap; this needs an explicit justification, not a change of hypothesis by fiat.
2. Prove the geometric upper bound locally near Gerver for nonsmooth caps. Core monotonicity is robust on the compact angular interval [phi,pi/2-phi], even though full injectivity near the endpoint angles is not. Tail separation and canonical-body contact must be checked independently.
3. For a sofa with rotation omega close to pi/2, form the downward right-angle cap from all upper supports of the sofa. Compare the missing final hallway constraints with the part removed by the tilted terminal strip. The proposed useful inequality is area(S) <= A(K) - c*(pi/2-omega), locally near Gerver. A fixed floor rectangle in the left wing gives a linear loss; missing end-angle wedges should be confined to an arbitrarily thin neighborhood of the opposite niche endpoint. Neither estimate is assumed proved in this entry.
4. If these lemmas hold, the existing qualitative theorem supplies the local neighborhood, the cap energy gives a square-root cap estimate, and the nonconvex/missing-area argument recovers the original sofa.

## Validation policy

Each lemma will be committed separately with its hypotheses. Counterexamples, invalid shortcuts and failed checks will remain in the history. Numerical tests are diagnostic only; the requested result requires a continuous analytic argument. The existing manuscript's kernel-verification claims are not changed.
