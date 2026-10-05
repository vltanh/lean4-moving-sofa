# Stability of Gerver's sofa: proof development

**Status:** written analytic proofs with local formula checks; not Lean-checked or independently reviewed. This work starts from `paper/uniqueness-arxiv` at `51c9be18d5b50d45561bfb93cb82d1aabca549bc`, preserving the alternative optimality route incorporated there. It is separate from the floating-point discovery experiments in PR #6.

No CI or Lean build was run. All commits carry `[skip ci]`; no existing Lean library, audit, workflow, or manuscript verification claim is changed.

Write M=|G|, K_G for Gerver's cap, A(K)=|K|-|N(K)|, and d_rig for Hausdorff distance modulo rotations and translations.

## Results and their precise scope

| Result | Hypotheses | Conclusion | Proof |
| --- | --- | --- | --- |
| Explicit cap estimate | A continuous feasible triple xi=(K,B,D) in Baek's domain T | d_H(K,K_G+(s,0)) <= 2 sec(phi) sqrt(M-Q(xi)), with s=-(h_K(pi)-h_G(pi)) | [Residual calculation](01-cap-coercivity.md), [manuscript theorem](paper-section.tex) |
| Area-deficit cap estimate | K in the normalized injective class Ki | The same bound with sqrt(M-A(K)) | [Cap coercivity](01-cap-coercivity.md) |
| Local stability of the nonconvex shape map | Any normalized right-angle cap K sufficiently close to K_G | d_H(K minus N(K),G) <= C0 d_H(K,K_G) | [Geometric recovery](03-nonconvex-recovery.md) |
| Square-root stability of actual sofas | A rigid image of S is contained in a monotone right-angle sofa whose cap lies in Ki; M-|S| sufficiently small | d_rig(S,G) <= C sqrt(M-|S|) | [Envelope theorem](03-nonconvex-recovery.md) |
| Global qualitative stability | S is any moving sofa | For every eta>0 there is epsilon>0 such that |S|>=M-epsilon implies d_rig(S,G)<eta | [Compactness proof](02-global-qualitative.md) |

The global qualitative result also gives convergence in symmetric-difference area after suitable rigid motions. It has no injectivity hypothesis, but no effective modulus or power-law rate is obtained.

## What is new relative to the previous stability draft

The previous estimate used repeated triangle and Cauchy-Schwarz inequalities to obtain 12/5. Here the four residual equations are solved as an exact Green operator. The squared norm of evaluation at t is computed explicitly on all four angular intervals. Its maximum is 2 sec(phi)^2, attained at t=0, giving

    ||f||_infinity <= 2 sec(phi) sqrt(E_cap).

This constant is sharp in the pinned ambient residual space. It is not claimed sharp for feasible cap perturbations or after minimizing the translation. For phi in [0.039,0.04], elementary rational bounds give

    2 sec(phi) <= 2500/1249 < 1001/500 = 2.002.

No numerical fitting or spectral extrapolation enters this result.

The Q deficit controls the six difference-square terms by applying the concavity identity to the segment from Gerver's maximizing triple and letting its parameter tend to zero. Discarding the two nonnegative auxiliary-body terms leaves the four cap terms. Thus the flat B,D directions do not need to be regularized. The argument works for every continuous feasible triple, not just the canonical one.

**The earlier numerical polygon outputs are not automatically such triples.** Their continuous feasibility and Ki regularity were not certified. Substituting a discrete Q value into this theorem without bridging those hypotheses remains invalid.

## From caps to sofas

The geometric recovery proof addresses an additional gap left by the previous draft. At Gerver, the nonconvex shape map is locally Lipschitz. Two estimates establish this:

- A point below Gerver's niche roof by more than O(delta) still violates a perturbed supporting hallway when the cap support error is delta. Strict tail slack and an outer-boundary margin control the endpoint regions.
- The erosion G_{-sqrt(2)delta} lies in K minus N(K). A uniform interior-ball property of G turns this inclusion into the other directed Hausdorff estimate.

The interior-ball property is proved directly from two convex wings and a positive-height Lipschitz epigraph strip, rather than inferred from a plot or from a generic assertion about piecewise smooth boundaries. A small missing-area argument then transfers the square-root cap estimate to any smaller closed sofa inside an eligible envelope.

For arbitrary sofas, a different argument applies. Connectedness bounds the height of a supporting inner corner. Using the pi/4 hallway gives a uniform containing rectangle of width 2+2sqrt(2) for every large sofa, after translation. In a Hausdorff limit, closed supporting-hallway inequalities and the endpoint width pass to the limit. They explicitly construct a movement of the limiting sofa. Area is upper semicontinuous; optimality and uniqueness then identify the limit as Gerver.

## What is not proved

The fully unrestricted quantitative assertion

    d_rig(S,G) <= C sqrt(M-|S|)

is not proved here. Exact maximizers have the right-angle and injectivity properties used in the paper, but the present work does not quantitatively transport those properties to arbitrary near-maximizers. Qualitative compactness does not supply a rate. This is the remaining mathematical gap, not a missing numerical optimization run.

No theorem is claimed about Hausdorff distance between boundaries: the distances above compare the closed sets themselves. Small holes can behave differently at the boundary level.

## Manuscript integration

[paper-section.tex](paper-section.tex) is a proposed section after recovery. It contains the explicit cap theorem, the exact residual lemma with proof, and unrestricted qualitative sofa stability. It is deliberately **not included** by `docs/paper/main.tex`. Its opening comments and final remark mark the formalization status. The conditional nonconvex recovery theorem is documented separately and can be integrated after its geometric hypotheses are reviewed.

Before including any new theorem in the paper, either formalize it or revise the abstract and formalization-scope claims so that they do not assert kernel verification for these written additions. The existing alternative optimality argument has not been altered.

## Local checks and negative findings

    python docs/stability/check_stability.py

All 17 tests pass in the recorded Python 3.13.5 / SciPy 1.17.0 environment. The tests compare exact formulas with independent quadrature, reconstruct an independently differentiated smooth function, test endpoint and translation behavior, verify rational inequalities, and exercise the geometric estimates. They are not proof certificates.

[CHECK_LOG.md](CHECK_LOG.md) preserves the initial 16/17 run: a zero-tolerance endpoint comparison failed by approximately 2.62e-16. It was committed before the roundoff-tolerance correction. The log also records invalid mathematical shortcuts: unpinned translation coercivity, continuity of nonconvex area, convergence of arbitrary motion paths, and automatic injectivity of near-maximizers. [checks-summary.json](checks-summary.json) records final errors and the locally tested source hash, which was matched to the committed Git blob.

## Source dependencies

All sofa-specific inputs come from the paper and formalization already present at the starting commit: the Mamikon and Q decomposition, the support and canonical-hallway definitions, the rotation-angle reduction for area at least 11/5, Gerver's boundary/arm facts, optimality, and uniqueness. The additional ODE, elementary geometric, compactness, and measure arguments are written out here. [RESEARCH_LOG.md](RESEARCH_LOG.md) records the initial scope and environment limitations.
