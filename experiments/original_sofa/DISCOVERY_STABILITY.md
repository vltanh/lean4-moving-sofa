# Cut/contact discovery and cap stability: follow-up research

This continues PR #6, from a72e4cae3b0bd96447158209e8d1a0fe9702004f.
Only local numerical validation is intended; no CI or Lean build is requested.
Positive and negative results will be recorded without rewriting the earlier log.

## Correction before computing: the outer optimization is a minimization

Let M be the true optimum. Wherever the continuous geometric reduction establishes
A(K) <= Q_phi(xi_K), define U(phi) = sup_{xi in T_phi} Q_phi(xi).
Then M <= U(phi). At a tight cut, U(phi) = M. Therefore the appropriate search
for a sharp cut is **min_phi sup_xi Q_phi(xi)**, not max_phi sup_xi Q_phi(xi).
The earlier conversational suggestion to maximize over phi was incorrect.
An upper-bound parameter is not a physical shape parameter to maximize jointly.

This observation alone does not prove uniqueness of the minimizing cut, numerical
convergence, or an upper-bound property of the finite polygon program. The source's
geometric reduction is justified on [0.039, 0.04]; scans outside that range remain
exploratory unless the reduction hypotheses are established separately.

## Questions to test

1. Does minimization of the discrete optimal value identify a cut consistently
   under mesh refinement, or is the observed minimum set by mesh artifacts?
2. Can complementary slackness/contact changes identify phase boundaries without
   supplying Gerver's theta or a five-phase ansatz to the optimization?
3. After projecting away auxiliary-body null directions, does the Mamikon energy
   control the cap support function with a mesh-independent constant?
4. Can the continuum tangent identities yield a quantitative cap estimate, and
   precisely which hypotheses prevent claiming it for all near-optimal sofas?

## Methodological guardrails

- Reference constants and the analytic Gerver path are permitted only for
  post-solve comparisons, not for initializing or constraining the search.
- Raw Mamikon terms at Gerver need not vanish. The uniqueness identities concern
  **differences of tangent displacements**, not the individual squares.
- A numerical Hessian eigenvalue is not a continuum coercivity proof.
- A cap estimate inside Baek's injective class is not automatically a stability
  theorem for arbitrary moving sofas: the exact-maximizer regularity reduction
  needs a quantitative analogue before extending such a claim.
- Every finite solve must retain feasibility and stopping diagnostics. Neither
  mesh-restricted Q values nor sampled sofa areas are certified bounds.

## Status at this commit

Source audit and experiment design only. No new numerical or formal theorem is
claimed in this commit. The existing PR remains open on the same research branch.
