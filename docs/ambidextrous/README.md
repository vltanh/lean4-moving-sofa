# Ambidextrous sofa research

**Start new sessions with [HANDOFF.md](HANDOFF.md), then [ROADMAP.md](ROADMAP.md).** The unrestricted optimality and uniqueness proof is **not closed**. Written arguments, source imports, executed diagnostics, and geometric admission hypotheses are distinguished below. The entire historical chain has not been independently refereed or Lean-verified.

Research branch: `research/ambidextrous-pen-and-paper`; draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3), based on `paper/uniqueness-arxiv`. No existing manuscript, Lean library, dependency or workflow file is changed by this research pass.

## New: user-supplied one-turn reduction

The user supplied a draft attributed to **Claude Opus 5.5 Max**, together with numerical scripts. All nine original files are preserved at `7c2cb37b55ebd00d7c9d7717f170f6205101a946`; the [audit](one-turn-proposal-audit.md) records archive and Git blob hashes. The attribution is as supplied, not independent verification of the generating model.

Read the [audit](one-turn-proposal-audit.md) before relying on the original [one-turn-reduction.md](one-turn-reduction.md). The proposal supplies a useful exact organization:

$$
|E|=\bigl[\mathcal A(U)-W/2\bigr]
    +\bigl[\mathcal A(V)-W/2\bigr]+G,
$$

for two full-angle caps with nonempty surviving fibers. Here A is cap area minus the **entire** niche and G is a positive clipping correction. For general cap pairs the audit adds the empty-fiber correction explicitly. Neither correction is silently discarded.

The proposal's initial floor traces classify the horizontal faces without a curvature bound. In its main case a common unit-height rectangle forces full turns. The audit strengthens that criterion to rectangle width `d >= q-sqrt(q^2-1)` for a body of area greater than q. Aligned faces of length at least one then supply the two corner-height positivities used to remove clipping. The exceptional cases, particularly point faces, remain unresolved for global maximizers.

### An existence obligation is now discharged

[Theorem PA2](one-turn-penalized-attainment.md) proves that

$$
\Psi(U)=|U|-|N(U)|-W(U)/2
$$

attains a maximum on the full-right-angle cap class. It uses compactness and niche lower semicontinuity, with the elementary coercive bound

$$
\Psi(U)\le\min\{W/2,\ 2\sqrt2-W/2\}.
$$

It does not use Gerver's sharp theorem or assumed ambidextrous optimality. **The value of that maximum and its uniqueness are not determined.** In particular, the proposed inequality `Psi<=M/2` is still a proof target, not an imported theorem.

### Numerical review: two objectives must be distinguished

The imported polygon optimizer uses the positive-part surviving area, not signed A. Their difference is `|N(U) minus U|`, and an explicit rectangle makes it positive. Its top-profile interpolator also mishandles repeated endpoint abscissae. Therefore the original optimization table is not verification of the proposed signed problem.

The original scripts remain intact. The separate [review utility](computer-assisted/one-turn/review_checks.py) keeps both objectives and all corrections distinct. Its [executed results](computer-assisted/one-turn/review-results.json) record exact finite identity checks and small floating-point diagnostics, with matching source hashes. They explicitly do not claim a continuum certificate or reproduction of the original multistart optimization runs.

## Existing two-wing route

The two-wing domain retains actual convex tail-body areas rather than a repaired full-hull area. Its calibration chain is:

| Result | Actual scope |
|---|---|
| [TW/WS/WC](two-wing-calibration.md) | Sharp bound on the original cut-vertex domain; common-strip quadratic sign, not unrestricted affine concavity. |
| [CS/SQ1](two-wing-slack-quadratic.md) | Actual inward supporting-line intersections and arbitrary cut-width slack, with each wing spanning the full strip. |
| [NH1](two-wing-near-full-height.md) | Arbitrary cut slack and unequal heights sharing a bottom, with both heights at least `1-sin(beta)/2`. |

All give sharp equality statements on their stated auxiliary domains. None proves that every maximizing sofa supplies the required wings, angular coverage and ordinary-area core. The new one-turn proposal is a complementary strategy for those geometric difficulties, not an assertion that the two-wing admission has been completed.

## The width gate remains analytic

[AW-W](analytic-width-theorem.md) proves

$$
W\le2\quad\Longrightarrow\quad |S|<41/25<M
$$

without curvature, contact-order, symmetry or full-angle assumptions. Its disjoint loss partition, mixed-area overlap estimate and explicit localization are pen-and-paper arguments. The earlier [computer certificate](computer-assisted/README.md) is retained historically but is no longer needed for that gate.

[DU1](diagonal-width-upper-bound.md) supplies the complementary width bound. The earlier attainment/normalization arguments therefore put every maximizing hull in

$$
2<W\le1+2\sqrt2<4.
$$

This does not place its shape in a candidate neighborhood.

## Known failed comparisons are mandatory tests

[AF3](adaptive-functional-global-calibration.md) gives a sharp auxiliary maximum, while [AF4](adaptive-functional-enclosure-counterexample.md) shows that the ordinary area can exceed that auxiliary expression. [GM2](global-curvature-majorant.md) increases hull area, but [GR1](global-repair-counterexample.md) shows actual sofa area can decrease.

[AX1](axis-cut-repair-budget-obstruction.md) and [SAT1](saturation-does-not-rescue-repair.md) defeat corrected derivative-energy budgets even after canonical saturation. [SAC2](saturated-axis-cut-area.md) computes the actual smaller deficit of that family. [SC3](repair-shadow-clipping-obstruction.md) defeats the derivative-free shared-anchor enclosure through positive clipping, even arbitrarily near the candidate in area. [TR1](repair-invariant-tail-regions.md) identifies exactly invariant one-wall regions, but does not control the entire mixed-wall core.

Do not call a new auxiliary maximum a global area theorem until it survives those tests and its geometric comparison has been proved.

## The remaining sufficient routes

The existing [CW4](curvature-only-wide-hulls.md) gives optimality and exact uniqueness for wide actual common hulls with open-quarter curvature measure dominated by angular measure. Deriving that property for arbitrary maximizers remains open; [the historical structural ledger](57-focused-structural-status.md) states the partial contact results and their limits.

Alternatively, prove the two-wing geometric admission and use the appropriate calibrated domain, or prove the new signed one-turn sharp bound **and** handle the face/clipping configurations needed to apply it. The latter is not simply two applications of Gerver optimality. The [PR #8](stability-pr8-transfer-audit.md) and [PR #9](coercive-pr9-transfer-audit.md) audits explain the missing premises in those transfers.

For the optimal value one attained maximizer suffices. For uniqueness every maximizer must be treated, or an equality-preserving recovery must identify each original body. Equal hulls alone do not identify nonconvex bodies.

## Execution and continuation

All commits carry `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. New diagnostics use already installed Python libraries and have explicitly limited scope. The imported scripts' original claims and runtimes are not promises or independently reproduced verification records.

The [handoff](HANDOFF.md) records the latest checkpoint, source provenance, proof boundaries and restart procedure. The [roadmap](ROADMAP.md) retains the existing gates and the new one-turn alternative. Historical findings remain in their notes and Git history; this index replaces stale progress descriptions rather than deleting mathematical results. PR #3 remains open and draft.
