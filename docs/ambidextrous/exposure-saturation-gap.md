# Exposure balance does not assert saturation of a local bound

Baseline: `03280a04151b0cf1a15c24b705f9aad4e12b28a0`. This corrects an inference in the preceding conversational plan. It does not retract EB1 or supply the missing optimality theorem. The current target remains the optimal value, with uniqueness deferred.

## 1. The exact logical distinction

For a selected polygon, write ell_j for an outer facet length, tau_j for its actual exposed niche-wall length, and L_j for a valid local upper bound obtained by ignoring distant quadrants. Then

$$
0\le\tau_j\le L_j,
\qquad \sum_j|\tau_j-\ell_j|\longrightarrow0
$$

is what the local estimate and EB.10 provide. Define hidden length H_j=L_j-tau_j. The exact identity is

$$
\sum_j H_j
=\sum_j(L_j-\ell_j)-\sum_j(\tau_j-\ell_j).
$$

Thus EB.10 identifies the limit of the hidden-length sum with the limit of the **local-bound slack**, if that limit exists. It does not make either limit zero. For example, on a mesh of an interval of length one, ell_j=tau_j=delta/2 and L_j=delta have zero balance defect and hidden-length sum one half. This is a logical numerical array, not a claimed realizable cap or a counterexample to optimality.

In particular, the proposed implication

`a positive amount is hidden -> the summed balance defect stays positive`

is invalid without an additional comparison between L_j and ell_j. The correct implication would need that missing comparison as a separate geometric theorem. Bounded support curvature does not supply it by itself.

## 2. What remains available

EB1 and EB.10 still establish exact limiting **actual** exposure balance for weighted maximizing caps, subject to their written WP/WR/PT dependencies. SP1 still solves the stated saturated ODE. Applying SP1 to a maximizing cap still requires proving that its actual exposure obeys that ODE, with the required initial and first-passage conditions.

There is no justification for treating all locally possible tangent or corner segments as globally exposed merely because the actual exposure balances the outer facets. A proof must either establish that additional fact or avoid it.

The next argument instead tests a weaker geometric conclusion directly from the established differential inequalities and endpoint bounds: nonnegativity of the vertical coordinates of the two single-wall tangencies. This is not the assertion that those tangencies are globally exposed or that curvature is bounded by one.

## 3. Current computational limits

Following the user's latest instruction, new computer use is restricted to small diagnostics or exact finite algebra with a 30-second wall-clock cap per invocation. A timeout is a failed/unfinished check, not permission for an unannounced long retry. Large certificate searches, multistart optimization campaigns, and refinement loops are deferred. New positive mathematical claims should have pen-and-paper proofs independent of sampled computations.

No CI, Lean/Lake compilation, dependency installation, or manuscript build is used. Substantive findings, including corrections and failed deductions, are committed with `[skip ci]`. The mathematical optimality proof remains unfinished; closing a PR is not a substitute for closing its hypotheses.
