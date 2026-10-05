# Ambidextrous sofa research

**The unrestricted optimality and uniqueness proof is not closed. The width-at-most-two gate now is.** An exact computer-assisted covering proves an ordinary-area bound below Romik's candidate for every normalized narrow body, without curvature or contact assumptions. The remaining sufficient route is a global maximizing-hull curvature theorem or an equality-preserving comparison replacing it.

The analytic arguments are written and self-reviewed. The new computation has an executed complete exact-integer replay, an arbitrary-precision reference evaluator, independent rational geometry checks, and a written correctness/overflow argument. It is not Lean-verified or independently refereed. No novelty or best-known-bound claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Original base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`; the base branch has since advanced. The existing manuscript, Lean sources, dependencies and workflow definitions are unchanged. This directory now contains Python and JSON as well as the earlier Markdown notes, following explicit authorization to explore computer-assisted proofs.

## New result: a complete width-two certificate

[Theorem CA-W and its correctness argument](computer-assisted/THEORY.md) prove:

$$
\boxed{W\leq2\quad\Longrightarrow\quad |S|\leq411/250=1.644<M_A,}
$$

for a compact connected ambidextrous body S in a common incoming unit-span normalization, where W is its horizontal width and

$$
M_A=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.
$$

No curvature bound, symmetry, contact order, full-quarter endpoint, or adaptive-functional enclosure hypothesis is imposed. A separate exact rational comparison proves 411/250 is strictly below M_A.

The certificate uses two rational directions for each turn, with sine/cosine pairs (3/5,4/5) and (600/769,481/769). Every body large enough to challenge the bound must actually visit those angles, by the two-strip bound and the correct-sign reduction. Eight independent placement parameters cover both motions. The envelope bound counts actual ordinary area and does not subtract overlapping niches incorrectly.

The complete binary covering has **11,697,975 nodes**, with 5,448,929 exact spatial leaves and 400,059 rational-quadratic leaves. There are **no unresolved boxes**. A stateless verifier reconstructs every box and rechecks every leaf; it does not trust the search checkpoint or numerical optimizer. The maximum individual coordinate depth is eight. Full counts, hashes, source versions, execution details and negative controls are in [RESULT.json](computer-assisted/RESULT.json).

The full tree was replayed using guarded int64 arithmetic. The arbitrary-precision Python evaluator was cross-checked on 1,200 boxes and independent rational polygon clipping on 500 boxes; the whole tree was not replayed in pure Python. THEORY.md establishes the fixed-width arithmetic bounds explicitly. [Reproduction instructions](computer-assisted/README.md) include both modes. The generated binary tree is provided in the conversation's certificate bundle and is deterministically reproducible from the committed generator; the binary itself is not checked into Git.

The numerical search returned finite-position values around 1.628313908. Those values are **not** the certified global bound and are not continuous-motion witnesses. [DISCOVERY.md](computer-assisted/DISCOVERY.md) preserves the unfinished floating searches and the rejected contact-order shortcut separately from the exact proof.

## Updated closure roadmap

The general reductions give an attained global maximum and an incoming unit-span representative of every competitive body. CA-W now forces **W>2 for every global maximizer**. Thus the previous narrow-width work is no longer an unresolved gate.

The existing [wide curvature theorem CW4](curvature-only-wide-hulls.md) states that a unit-span ambidextrous common hull with W>=2 and

$$
\sigma_K=h_K+h_K''\leq d\theta
\quad\text{on all four open coordinate quarters}
$$

has area at most M_A, with equality exactly for Romik's candidate up to congruence. It assumes neither contact order, full turns nor aligned horizontal faces; its proof supplies or bypasses those requirements.

Consequently the following is now a sufficient noncircular route:

```text
an arbitrary attained global maximizer
  -> common incoming unit-span normalization
  -> W > 2                                  [CA-W, completed]
  -> curvature domination or a valid sharp replacement
                                              [NOT PROVED]
  -> CW4 and exact equality recovery
  -> Romik optimal and uniquely optimal
```

A curvature/enclosure result for only one attained maximizer identifies the value. Uniqueness requires the structural result for every maximizer or a comparison with an equality-preserving recovery. The remaining step is a substantive global geometric/variational theorem, not a compilation task or a consequence of the numerical search.

The present pass should not be read as proving curvature domination by narrowing width. It only removes the entire width-at-most-two case by a different, independently checkable finite-position argument.

## Why the ordinary-area comparison is still separate

[AF3](adaptive-functional-global-calibration.md) proves the auxiliary bound on every normalized real H^1 profile of width at least one, with its exact equality kernel. For an actual hull support h, however,

$$
M_A-|S|=[M_A-\widetilde{\mathcal Q}(h)]
       -[|S|-\widetilde{\mathcal Q}(h)].
$$

The second bracket can be positive, even near the candidate. [AF4](adaptive-functional-enclosure-counterexample.md) proves this on feasible high-curvature examples, and [the narrow convex example](narrow-curvature-enclosure-counterexample.md) records a distinct clipping obstruction. Their conclusions remain valid; CA-W bypasses the latter narrow case rather than turning its false enclosure inequality into a true one.

The global curvature task still includes obstructed outer/inner-corner contacts, hidden or coincident edge atoms, and the sharp bound on absolutely continuous curvature. The existing singular-contact exclusions and coupled repair estimates have explicit admissibility hypotheses; they do not already supply the missing global theorem. Vanishing selection penalties do not eliminate the contact normal-cone terms.

## Prior stability and structural work retained

The [PR #8 transfer audit](stability-pr8-transfer-audit.md) explains why Gerver's one-turn stability theorem cannot be invoked as Romik near-optimal localization: it has a different reference deficit and uses already established Gerver uniqueness. Its useful methodological separation led here to the [fixed-width energy estimate](stability-fixed-width-deficit.md), [narrow-profile deficit](stability-width-gap-certificate.md), and [error absorption on a proved repair family](stability-error-absorption-check.md).

The [ordered-face hull estimate](narrow-separated-face-area-bound.md) directly bounds the whole curvature-dominated hull by pi/2 in that configuration. These analytic narrow-case results remain correct with their hypotheses but are no longer needed to assert the universal width exclusion, which now follows from CA-W.

[Corollary WG4](31-closed-curvature-class-theorem.md) retains the alternative curvature-plus-contact route. The [signed-roof calculation](curvature-only-signed-roof.md) identifies exact clipping and negative-roof terms. The [coupled repair identity](ordinary-area-repair-coercivity.md) gives a coercive area gain under its explicitly verified geometric conditions.

Earlier foundations include canonicalization, unit-span normalization, correct turning signs, connected niche separation, a uniform bounding box, attainment and quantitative selection of any prescribed maximizing hull. The historical [structural ledger](57-focused-structural-status.md) records the contact-measure analysis. No independent audit of every earlier proof is claimed by the new certificate.

## Reading map

| Source | Role |
|---|---|
| [Computer-assisted README](computer-assisted/README.md) | Exact commands, trust boundary and binary-certificate reproduction. |
| [CA-W theory](computer-assisted/THEORY.md) | Complete geometric coverage, integer bounds, polynomial leaves and candidate comparison. |
| [Executed result](computer-assisted/RESULT.json) | Counts, hashes, source versions and full-replay record. |
| [Discovery log](computer-assisted/DISCOVERY.md) | Non-certifying numerical values and failed/unfinished approaches. |
| [CW4](curvature-only-wide-hulls.md) | Sharp theorem applicable after a global curvature reduction. |
| [AF3](adaptive-functional-global-calibration.md), [AF4](adaptive-functional-enclosure-counterexample.md) | Auxiliary maximum and an exact failure of universal ordinary-area enclosure. |
| [PR #8 audit](stability-pr8-transfer-audit.md), [width deficit](stability-width-gap-certificate.md) | Stability-transfer scope and analytic deficit tools. |
| [Notes 1–24](24-current-proof-ledger.md), [25–51](51-current-proof-status.md), [52–67](57-focused-structural-status.md) | Historical proofs, partial reductions, corrections and negative findings. |

## Execution and provenance

The current user request explicitly authorized a computer-assisted approach. Local Python, SciPy numerical discovery, NumPy and Numba compilation of bounded-integer code were used. Exact proof decisions do not use SciPy or floating-point output. Earlier statements that no computations had been performed apply to their earlier passes, not this one.

**No CI was requested or used, and no Lean/Lake compilation was attempted.** No dependency installation or manuscript build was performed. All commits include `[skip ci]`. The PR remains open and draft because unrestricted closure and independent review are unfinished.

The finite hallway-intersection / exact-rational branch-and-bound viewpoint is used in Kallus and Romik, [*Improved upper bounds in the moving sofa problem*](https://arxiv.org/html/1706.06630v2). The candidate is Romik's [explicit construction](https://arxiv.org/html/1606.08111v3); Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826), the repository's uniqueness manuscript and the inspected PR #8 notes motivate the analytic route. No best-known or priority claim is made for this new implementation.
