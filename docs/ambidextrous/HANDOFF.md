# Ambidextrous sofa research — start a new session here

**Primary milestone:** prove only the optimal value first. Defer uniqueness and full equality classification. Use [optimality-only-computer-plan.md](optimality-only-computer-plan.md) for the exact computer-assisted global/local strategy.

**Unrestricted optimality and uniqueness are not proved.** This is the active cross-session handoff for PR #3, not a certificate that all historical arguments have been independently verified.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base: `paper/uniqueness-arxiv`.
Last substantive checkpoint before this handoff update: `ac76e9a7f6490cb3f44ce3808be8befab1a76f48`.
Always query the live branch head and inspect intervening changes before continuing.

## 1. User instructions

Continue toward a mathematical proof; commit substantial positive and negative findings frequently with `[skip ci]`. Computer assistance is allowed, but a sampled optimizer or an unexecuted checker is not a certificate. **Do not run CI or compile Lean/Lake.** Do not change the manuscript, Lean libraries, dependencies, or workflows without a new instruction. Keep the PR draft until the mathematical theorem and its equality recovery are genuinely complete.

The target is Romik's candidate of area

$$
M=1+4Y^2+\arctan Y,\qquad 4Y^3+3Y-1=0,\quad Y>0.
$$

A result for one attained maximizer proves the optimal value; uniqueness requires every maximizer or an equality-preserving comparison recovering each original nonconvex body.

## 2. New user-supplied proposal: read the audit before using it

The user uploaded `ambidextrous-one-turn-reduction-draft.zip`, attributing it to Claude Opus 5.5 Max. The original nine files are preserved byte-for-byte at `7c2cb37b55ebd00d7c9d7717f170f6205101a946`:

- [one-turn-reduction.md](one-turn-reduction.md): the imported OT1–OT8 proposal;
- [computer-assisted/one-turn/](computer-assisted/one-turn/): its original scripts and reported diagnostic table.

The attribution is as supplied by the user, not independent verification of the generating model. Original numerical claims have not been independently reproduced in full.

**Read [one-turn-proposal-audit.md](one-turn-proposal-audit.md) first.** It records the source hash, imported blob hashes, verified reductions, necessary qualifications, and numerical mismatches. Do not silently promote every claim in the imported draft to an established branch theorem.

### Accepted geometric content and qualifications

For two full right-angle caps with the same projection and nonempty two-turn fibers, OT1 gives the exact identity

$$
|E|=\Psi(U)+\Psi(V)+G,\qquad
\Psi(U)=|U|-|N(U)|-W/2,
$$

where G is a nonnegative clipping correction. The audit also supplies the positive empty-fiber correction when the nonempty-fiber assumption is absent. **The sign of G cannot be dropped.** Full-turn caps do not automatically contain an original partial-turn body in their two-turn envelope.

OT3–OT4 use initial floor traces and retained extreme points to classify horizontal faces without a curvature assumption. A main case has a shared unit-height rectangle. The audit strengthens its full-turn test: if `|S|>q>1` and that rectangle has width d, then

$$
d\ge q-\sqrt{q^2-1}
\quad\Longrightarrow\quad\text{both reduced turns are full}.
$$

For competitive bodies one may use q=41/25, giving d at least `(41-4 sqrt(66))/25`. This does not exclude point faces or the other exceptional configurations.

OT5 removes clipping when the horizontal faces align and the corner-height positivity holds for **both** turns. A common face length at least one supplies both positivities. The one-turn maximality conclusion still applies only to variations that preserve a feasible connected two-turn intersection; it is not maximality against every unpenalized one-turn cap.

### New independent result: existence for the weighted one-turn objective

[Theorem PA2](one-turn-penalized-attainment.md) proves that the signed objective Psi attains its maximum over all normalized full-right-angle caps. It uses only compactness, niche-area lower semicontinuity and

$$
\Psi(U)\le\min\{W/2,\ 2\sqrt2-W/2\}.
$$

A cap with a semicircular upper boundary gives Psi=pi/8>0, so maximizing sequences have widths in a fixed compact positive interval. No Gerver sharp theorem or conjectured Romik maximum is used.

**PA2 does not prove `max Psi = M/2` or uniqueness.** It also does not prove niche containment or curvature/arm bounds for the maximizing cap. Full turns are built into this auxiliary domain; getting an arbitrary ambidextrous body into it remains a separate geometric task.

### Numerical issue that must not be reintroduced

The imported `polycap.psi` uses the integral of `(a-alpha)_+`, whereas the proposed W-Gerver problem uses the integral of `a-alpha`. Their difference is `|N(U) minus U|`, potentially positive. The imported top-profile interpolator also fails to consolidate repeated abscissae despite its comment; an exact rectangle exposes the error at its right endpoint.

The separate [review_checks.py](computer-assisted/one-turn/review_checks.py) keeps signed cap area, surviving area, leakage, and empty-fiber corrections distinct and fixes that interpolation in its own utility. The original code remains preserved. [review-results.json](computer-assisted/one-turn/review-results.json) records an executed run: 2,025 rational fiber checks, 1,296 interval pairs (476 meeting the initial floor tests), two rejected sign omissions, and small rectangle/candidate diagnostics. The executed source matches its committed blob.

These are finite identity checks and floating-point diagnostics, **not** a continuum covering or a proof of global optimality. The original multistart searches were not rerun. Finite hallway sampling alone does not give a certified bound after spatial quadrature and support interpolation.

## 3. Infrastructure retained from the earlier branch

The following are written arguments with stated hypotheses; the full chain still needs independent review.

**General reductions.** The earlier notes give common-hull canonicalization, correctly signed motion intervals for competitive bodies, same-hull saturation, attainment, and selection of any prescribed maximizing hull. They do not prove full turns or curvature domination universally.

**Analytic width exclusion.** [AW-W](analytic-width-theorem.md) gives `W<=2 => |S|<41/25<M` without curvature or symmetry. [DU1](diagonal-width-upper-bound.md) gives the upper width restriction. Thus normalized maximizing hulls have

$$
2<W\le1+2\sqrt2<4.
$$

The older exact computer-assisted width certificate is historical; AW-W no longer needs it.

**Conditional geometric theorem.** [CW4](curvature-only-wide-hulls.md) proves the sharp ordinary-area bound and exact uniqueness on the wide class if the actual hull has open-quarter curvature measure bounded by angular measure. Deriving that condition for every maximizer remains open.

**Functional calibration.** [AF3](adaptive-functional-global-calibration.md) gives a sharp auxiliary maximum, not universal ordinary-area enclosure. [AF4](adaptive-functional-enclosure-counterexample.md) provides genuine counterexamples to that enclosure.

**PR #8 and PR #9.** Their deficit/coercivity organization is useful. The [PR #9 transfer audit](coercive-pr9-transfer-audit.md) uses pinned snapshots, not a claim about its current tip. Its one-turn maximality-to-curvature premise does not transfer automatically to an ambidextrous maximizer. No uncompiled Lean source is treated as kernel verification.

## 4. Two-wing route: still available, not silently superseded

Read the domain and calibration chain only when using this route:

1. [two-wing-domain.md](two-wing-domain.md), [two-wing-strip-quadratic.md](two-wing-strip-quadratic.md), [two-wing-calibration.md](two-wing-calibration.md);
2. [two-wing-cut-slack.md](two-wing-cut-slack.md), [two-wing-slack-quadratic.md](two-wing-slack-quadratic.md);
3. [two-wing-near-full-height.md](two-wing-near-full-height.md).

WC2 treats its original cut-point domain. SQ1 allows arbitrary cut slack for full-height wings. NH1 allows arbitrary cut slack and unequal heights **when the wings share a bottom line and both heights are at least `1-sin(beta)/2`**. Arbitrary-maximizer admission, the needed heights, terminal-angle coverage and ordinary-area core are not established.

The CS/SQ checker has a committed execution record. The NH checker source was added at `9207937`; no execution record for it was established in this pass. Verify before claiming a run. Do not infer joint concavity from the strip-cone or first-order slack arguments.

## 5. Failed shortcuts: mandatory stress tests

Retain these distinctions in every new comparison:

- [GR1](global-repair-counterexample.md): least curvature repair can lower actual sofa area despite increasing hull area.
- [AX1](axis-cut-repair-budget-obstruction.md), [SAT1](saturation-does-not-rescue-repair.md): corrected energy budgets fail, even after full canonical saturation.
- [SAC2](saturated-axis-cut-area.md): saturated axis cuts are strictly suboptimal, but their true deficit has a different order from the proposed derivative-energy charge.
- [SC3](repair-shadow-clipping-obstruction.md): a fully saturated, shared-anchor, near-candidate family still defeats the derivative-free repair enclosure through positive clipping. It has a point top face.
- [TR1](repair-invariant-tail-regions.md): one-wall safe regions are repair-invariant, but clipped tail bodies and mixed-wall core are not thereby controlled. Repair followed by saturation can remain at a suboptimal fixed point.

No fixed high-area threshold below M excludes all the known point-face examples. No new proposal is accepted merely because it matches the candidate.

## 6. Next-session priorities and stopping criteria

Read [ROADMAP.md](ROADMAP.md), then choose **one** unresolved comparison to attack.

For the new one-turn route, the concrete next target is the sharp signed inequality `Psi<=M/2` for its attained maximizing cap. Interior fixed-axis variations leave the width penalty unchanged, but the new endpoint conditions, curvature/arm bounds, and admissibility need proofs. Alternatively, target a specific exceptional face class from OT4 with an actual area-improving operation. Do not call the point-face exclusion an elementary consequence of high area.

For the two-wing route, the unresolved gates are required angles, canonical safe pieces with the stated height/width properties, and containment in a correctly accounted ordinary-area core. A calibrated signed curve expression is not that containment theorem.

Both routes need actual-body equality recovery. A short conditional final implication is not evidence that the missing geometry is routine.

Every new mathematical statement should say which gate it closes and for what class. Record negative results. Avoid another unconnected calibration, coarse bound or local regularity refinement without a demonstrated role on the critical path.

## 7. Fresh-session procedure

Query PR #3, inspect new commits, and check for repository instructions. Read this handoff and the roadmap, then the relevant theorem definitions and counterexamples. Pin every imported PR result to a commit. Verify original/source hashes before reporting numerical reproduction. Use the GitHub API for edits; refresh blob SHAs and use branch leases when building multi-file commits. Keep all changes under `docs/ambidextrous/` unless instructed otherwise.

The current proposal's original files remain available at the provenance checkpoint above. The new audit and PA2 are separate from that author's draft. This handoff update also replaces malformed mathematical escapes in the prior version with valid Markdown/TeX; no historical theorem is made stronger by that editorial repair.

No CI or Lean/Lake compilation was used. The mathematical proof, not the PR state, is what remains to be closed.
