# Research log: stationarity, deficit, and rigidity

Date: 2026-10-03.

This paper branch starts from main at cf4fefff35971554e635d84a7ef5593c66e5c6e4. It does not change the proof branch or use CI, Lean, Lake, or a proof-source generator. The existing uniqueness source at 36dec2efe72f3a75ea1fb6bd99578dc956530b14 is an uncompiled research input, not a verified theorem.

The reading entry point is now [paper.md](paper.md), with four detailed mathematical sections and a [dependency ledger](DEPENDENCIES.md). PR #2 is separate from the earlier uniqueness PR.

## 1. Negative result: the proposed balance-free outline omitted feasibility

An unrestricted cap K need not contain its niche N(K), and K minus N(K) need not satisfy the connectedness required of a moving sofa. The exact area identity is

    |K minus N(K)| = A(K) + |N(K) minus K|,
    A(K) = |K| - |N(K)|.

Thus selecting an ordinary maximizer of A does not by itself supply the connected sofa needed for the next reduction. A theorem of feasible attainment is necessary. The manuscript gives the concrete warning K=[0,4] times [0,1]: its niche removes a whole central cross-section, although both bottom endpoints survive.

This corrects the earlier conversational outline. It does not prove that a maximizing cap is infeasible, and it does not disprove Baek's theorem or the equality-case research.

The manuscript distinguishes:

1. the local replacement of the arm iteration;
2. the integrated stationarity/deficit route retaining Baek's independently proved feasible-attainment theorem;
3. a genuinely balance-free route, for which an independent feasibility proof is not supplied.

## 2. Positive result: an error-tolerant, noniterative scalar lemma

Section 01 proves the coupled arm bound directly for every interval length L<5/3:

    f(t)>=1+t/2,   g(t)>=1+(L-t)/2.

There is no assumption of reflection symmetry. The proof takes the largest deficit below one and evaluates one triangular-envelope integral. This replaces a finite iteration count.

The new robust extension allows the two integral inequalities to have a uniform additive error epsilon. With

    c_L=min(1/3,5/3-L),
    (1+3L/2)*epsilon<c_L,

the deficits are at most epsilon and the linear bounds have slope 1/2-3epsilon/2. No optimality is asserted for this sufficient error threshold.

A separate exact counterexample at L=5pi/9 shows that the interval-length hypothesis cannot be discarded. The two explicit nonnegative trigonometric functions satisfy the integral equations with equality and each vanishes somewhere. They are scalar test functions, not alternative sofas.

## 3. Positive result: fixed persistent samples simplify the variation bookkeeping

Section 02 selects a specified maximizer with a fixed squared penalty on persistent support samples. It needs a one-sided limsup inequality and recovery, not uniform objective convergence or a tuned vanishing penalty weight.

For a floating outward facet move, all unchanged sampled supports remain fixed by containment and the unchanged defining bounds. Only one grouped penalty summand changes. The stationarity errors are therefore bounded by 2*eta_n*w_n(t), with total at most 2*eta_n -> 0. Large persistent coarse weights are harmless because the error is summed as a measure, not divided by the mesh.

The argument still explicitly retains the finite geometric derivative/feasibility lemmas and the positive-superlevel width bound. A fixed-angle interior-ball estimate handles the pins; the signed boundary identity controls their negative defects. The weak-limit argument tests across normal zero before concluding that its atom vanishes.

Two negative examples are retained: exact unpenalized maximizers need not select a specified continuum maximizer, and an arbitrarily weakened penalty can also fail to select it.

## 4. Positive result: one exact identity packages the final bound and equality

Section 03 writes Q as an affine functional minus six squared L2 norms and expands it exactly:

    Q(G)-Q(X) = -DQ_G(X-G) + (1/2)*sum_j ||z_j(X)-z_j(G)||^2.

Adding the geometric slack Q(X_K)-A(K) gives a sum of three nonnegative deficits. Four first-order equality equations then identify the cap modulo horizontal translation. The quantitative calculation gives the cap bound

    inf_a d_H(K,C(G)+(a,0))^2 <= 6*(|G|-A(K))

for K already in the injective domain. No global quantitative stability statement for arbitrary sofas is inferred.

The calculation treats the singular last tangent endpoint by the exact factor sin(pi-t)cos(pi-t)<=1/2. It does not assert strict concavity of the entire triple domain or uniqueness of both auxiliary tail bodies.

## 5. Positive result: the new global order is noncircular

Theorem 5.1 first proves the sofa-area upper bound using feasible fixed-angle maxima, stationarity, injectivity and Baek's local Q toolkit. Only afterward does Corollary 5.2 bound every cap objective by |G|. The equality proof can then recognize the OWN cap of a specified maximizing sofa as a cap maximizer and preserve the actual set through both monotonizations.

The existing library helper cap_area_le_gerver calls theorem1_1_1. It is consequently unsuitable as an input to a new proof of theorem1_1_1. The proposed migration order records this explicitly.

This is a modular reorganization relative to retained inputs, not a claim to have removed Baek's Chapter 3 or Chapters 7-8.

## 6. Correction found during the paper audit: envelope endpoints

The first formulation of the general continuous-envelope lemma omitted its zero endpoint heights. They are necessary when the niche is declared empty outside its horizontal interval. For a constant positive height on that interval, points approaching from outside can converge to an excluded endpoint point, so the complement need not be closed.

Commit 22ebc91 adds H(a)=H(b)=0, proves that extending H by zero is continuous, and records the explicit counterexample. The concrete Gerver envelope has those endpoint values; no new assumption on a competitor is introduced.

## 7. What was checked, and what was not

The written checks include the two cases in the maximum-deficit integral, the exact trigonometric scalar counterexample, the single-sample penalty expansion, the actual-versus-assigned niche inequality, the endpoint measure tests, the tangent-kernel integrating factor, the two positive-coefficient angular polynomials, and the corrected envelope closure argument.

These are mathematical calculations written in the manuscript, not results of an executed proof checker. The new stationarity extensions, their use of the local geometric inputs, and the global manuscript still need independent mathematical review. No claim of successful Lean elaboration, source-wide policy audit, transitive axiom closure, publication acceptance, formal-conjectures acceptance, or Palomar certification is made.

A genuinely balance-free feasible-attainment theorem and a global quantitative sofa-stability theorem remain unproved here. They are not hidden among the main theorem's hypotheses as new unexplained facts.

## 8. Sources consulted

- J. Baek, Optimality of Gerver's Sofa, arXiv:2411.19826v1, especially Sections 1.3.2, 2.5, 3.4-3.5, 6.5, and 8.3-8.5. The arXiv HTML display has a regenerated date; the stable citation is the versioned arXiv identifier, not that display date.
- D. Romik, Differential Equations and Exact Solutions in the Moving Sofa Problem, arXiv:1606.08111.
- Y. Kallus and D. Romik, Improved Upper Bounds in the Moving Sofa Problem, arXiv:1706.06630, as background rather than a computational proof input.
- Repository uniqueness research at commit 36dec2efe72f3a75ea1fb6bd99578dc956530b14, especially SelectedCaps, PinnedVariation, PaperReductions, ShapeUniqueness, and notes 11, 17, 19, 20 and 22.

## 9. Commit trail

| Commit | Result |
| --- | --- |
| 82b3743 | Initial feasibility obstruction and independent paper scope |
| 75b66b2 | One-step and robust arm lemmas; exact long-interval counterexample |
| fbff766 | Persistent sampled selection and stationarity, with endpoint-safe limits |
| f85ae8b | Exact deficit, cap equality kernel and quantitative coercivity |
| ab55b3f | Same-sofa angle extension and set-recovery arguments |
| 2d3f3a1 | Main noncircular optimality/uniqueness manuscript |
| 6344330 | Dependency ledger and source-only migration plan |
| 22ebc91 | Corrected envelope endpoint premise and counterexample |

Commits are intentionally not squashed: the mathematical corrections and failed approaches are part of the research record. All commits in this paper continuation use [skip ci].
