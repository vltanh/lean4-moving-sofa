# Ambidextrous sofa research

**Start with [HANDOFF.md](HANDOFF.md), then [ROADMAP.md](ROADMAP.md).** The unrestricted optimal value is **not proved**. The signed weighted one-turn subproblem is now proved in the written WV chain, and FL/LF give an ordinary-area bound for the long-face class. Unrestricted uniqueness remains deferred.

Branch: `research/ambidextrous-pen-and-paper`; draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3). Its live base at this update is `main`, not the historical paper branch. All research changes remain under this directory. The complete written dependency chain is self-reviewed, not independently refereed or kernel-verified.

## Current theorem: the signed weighted one-turn value

[Theorem WV2](one-turn-weighted-value.md) gives

$$\boxed{\sup_U\{|U|-|N(U)|-W(U)/2\}=M/2,}$$

where U ranges over normalized full-right-angle caps and N(U) is the **whole** positive-height niche. The reference constant is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The proof first establishes unit curvature at an attained weighted maximizer. The new [CG](one-turn-curvature-guard.md) arm criterion, [SE](one-turn-single-excess-quarter.md) chord/Gerver bound and [VE](one-turn-visible-exposure-bound.md) source-flux lower bound combine in WV's energy contradiction. Only then are the existing SR1 and AF3 calibrated comparisons applied.

VE is the main new continuum review point: one globally good quarter and a good future make both a tangency and a corner globally visible. Their actual finite source fluxes survive the limit, including alternating edges. The proof does not assume convergence of ordinary niche perimeter or invoke the rejected maximal-local-exposure inference. The proposed saturated ODE is not needed.

Read [weighted-value-proof-review.md](weighted-value-proof-review.md) for the dependency audit, exact rational constants, failed approaches, and short execution record.

## Actual two-turn payoff

[FL1](aligned-face-optimality.md) proves |S|<=M for compact connected ambidextrous bodies whose top and bottom common-hull faces coincide in an interval of length at least one. It needs no curvature bound or assumed full turn: the contained unit square forces full turns, and retained face endpoints confine the two positive niches, eliminating clipping.

[LF1](long-faces-force-alignment.md) proves that two horizontal face lengths strictly greater than one force that alignment. Therefore

$$\boxed{\text{both horizontal hull faces have length}>1\Longrightarrow |S|\le M.}$$

A possible counterexample of area greater than M must have at least one face of length at most one. This remaining class includes the near-candidate point-face examples. No theorem here excludes it or proves that a global maximizer has two long faces.

For general full-turn pairs with nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

Writing Delta(U)=M/2-Psi(U), the remaining exact full-turn target is G<=Delta(U)+Delta(V). It is not asserted without proof. Partial-angle bodies still require actual angle coverage. The symmetric body from a weighted maximizer has zero clipping but is not known to dominate every competitor.

## Additional valid data and an exact negative control

[MW1/MW2](weighted-maximizer-canonical-wings.md) give full-height canonical wings with complete outward-support agreement for the symmetric weighted-maximizer construction. Truncated wings and all-angle surviving wings are kept distinct.

[AO1](all-angle-wing-reference-obstruction.md) proves that substituting the all-angle wings into the old fixed-cut core functional undercounts even the reference, by at least

$$2(1-\cos\beta)^2/(\sin\beta\cos\beta)>0.$$

Thus data admission to SQ1 does not by itself establish the needed core-area enclosure. The successful WV proof avoids this substitution.

## Earlier infrastructure and provenance

| Reading | Role |
|---|---|
| [PA](one-turn-penalized-attainment.md), [WP](one-turn-weighted-selection.md), [WR](one-turn-weighted-regularity.md) | Attainment, selection, finite variation inequalities and regularity for the signed objective. |
| [PT](one-turn-positive-top-face.md), [TS](one-turn-top-shortening.md), [EB](one-turn-exposure-balance.md) | Positive top face, finite shortening and exact limiting exposure balance. |
| [TF](one-turn-tangency-floor-bound.md), [HF](one-turn-half-width-top-face.md) | Niche confinement, zero symmetric clipping, half-width top face and stationary convex core. |
| [Original one-turn proposal audit](one-turn-proposal-audit.md) | Preserved upload, cap-pair accounting, signed/clipped numerical mismatch and qualifications. |
| [Arm-package review](one-turn-arm-package-review.md) | Preserved arm reduction, finite shortening and the separate assumed-ODE theorem. |
| [Canonical winding accounting](canonical-wing-winding-accounting.md) | Negative winding, uncovered material and overlap deductions retained explicitly. |
| [AW-W](analytic-width-theorem.md), [AL1](anchor-width-localization.md) | Analytic competitive-width restrictions. |
| [AM2](matching-tilted-exclusion.md), [TE1](terminal-angle-exclusion.md) | Complete but restricted ordinary-area computer certificates, not a global sharp covering. |
| [PR #9 audit](coercive-pr9-transfer-audit.md) | Useful deficit organization without importing the wrong maximizing-cap premise. |

Original user-supplied packages remain preserved with attribution and hashes in their audits. Author-generated numerical records are not overwritten by local runs. Historical negative controls AF4, GR1, AX1/SAT1, SAC2, SC3 and TR1 remain relevant: repair, saturation, shared anchors and proximity did not justify those universal enclosures.

## Execution policy

The user prioritizes pen-and-paper proofs and short checks. New invocations are capped at 30 seconds; the current arithmetic and diagnostic runs used five/ten-second external limits. The [latest exact checker](computer-assisted/check_core_arm_reduction.py) and [record](computer-assisted/core-arm-checks.json) contain 19 named tests, source hashes and explicit limits of verification. No numerical output is a premise of the new continuum proof.

No CI, Lean/Lake compilation, dependency installation or manuscript build was used. All substantive commits include `[skip ci]`. The remaining task is the unrestricted ordinary-area comparison, not another weighted optimization or a premature uniqueness proof. PR #3 stays open and draft.
