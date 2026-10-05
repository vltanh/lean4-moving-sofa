# Ambidextrous sofa: pen-and-paper research

**The unrestricted optimality and uniqueness proof is not closed.** The branch has a sharp auxiliary-functional calibration, geometric theorems on stated classes, and explicit failures of universal functional enclosure. The latest pass uses the method in PR #8 to quantify the auxiliary deficit and its ordinary-area error, and proves a direct area exclusion for one narrow-hull configuration.

These are written, self-reviewed arguments, not independently refereed or Lean-verified results. The earlier proof chain has not been independently audited in full. No novelty or best-known-bound claim is made.

Research branch: `research/ambidextrous-pen-and-paper`.
Draft PR: [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3).
Original base: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`; that base branch may since have advanced. All edits here are Markdown. Existing manuscript files, Lean sources, dependencies, and workflows are unchanged.

## Current proof boundary

For a normalized actual hull support h, keep two different quantities:

$$
D(h)=M_A-\widetilde{\mathcal Q}(h)\geq0,
\qquad E(S)=|S|-\widetilde{\mathcal Q}(h),
$$

so

$$
\boxed{M_A-|S|=D(h)-E(S).}
$$

[AF3](adaptive-functional-global-calibration.md) controls D and identifies its zero set. It does not control the sign or size of E. [AF4](adaptive-functional-enclosure-counterexample.md) constructs genuine near-candidate bodies with E>0. [The narrow convex example](narrow-curvature-enclosure-counterexample.md) has positive E even with open-quarter curvature domination.

A completion must prove an ordinary-area comparison or an improving repair for arbitrary relevant maximizers, with enough equality control to recover every maximizing body. Merely proving functional stability does not supply this comparison.

## What PR #8 contributes

The [transfer audit](stability-pr8-transfer-audit.md) pins PR #8 at `1a97bc70782652f29c29dd4866115bd288c53e86` and reads both its paper argument and its formalization target. That branch concerns stability of **Gerver's one-turn sofa**, measured using |G|-|S|, not the Romik deficit M_A-|S|.

Its entry into a local neighborhood uses existing Gerver optimality and uniqueness. Repeating that step for Romik would be circular. The inspected `UnrestrictedStability` Lean declaration is a proposition to be proved, and the formalization policy identifies the new files as uncompiled proof source. No completed kernel-verified stability theorem is being imported here.

The useful transfer is methodological: separate a nonsmooth exact energy identity from geometric enclosure, terminal-angle bookkeeping, and actual-body recovery. The following results derive ambidextrous constants independently.

### Exact nonsmooth fixed-width deficit

[Theorem SD1](stability-fixed-width-deficit.md) writes the half-functional deficit as a positive gauge energy plus two nonnegative Bregman remainders. It is valid for arbitrary H^1 competitors, including moving or degenerate contact sets.

For centered profiles of half-width a, let H_a be the unique fixed-width optimizer and Phi(a) its full functional value. Then

$$
\boxed{\|h-H_a\|_\infty^2\leq
\frac{4\pi}{7}\,[\Phi(a)-\widetilde{\mathcal Q}(h)].}
$$

This is a profile estimate, not automatically a Hausdorff estimate for the original nonconvex sofa. The width deficit M_A-Phi(a) is retained separately.

### A quantified narrow-width error budget

[SW1–SW3](stability-width-gap-certificate.md) construct and verify the exact fixed-width optimizers on

$$
1/\sqrt2<a<\tfrac23\cot(\pi/8).
$$

Their scalar value satisfies -Phi''>=4/3, giving M_A-Phi(a)>=(2/3)(a-a_*)². More concretely, throughout 4/5<=a<=1,

$$
\boxed{\widetilde{\mathcal Q}(h)<M_A-11/768.}
$$

Thus any hypothetical sofa of area at least M_A and normalized width 8/5<W<=2 would need **ordinary-area error E(S)>11/768**. This is a proved necessary condition, not a proved bound on E. Widths W<=8/5 are already excluded by the containing rectangle's area.

### A direct ordinary-area exclusion, independent of enclosure

[Theorem DF1](narrow-separated-face-area-bound.md) assumes open-quarter curvature domination and **ordered** top/bottom face intervals: r_b<=ell_t or r_t<=ell_b. It permits touching endpoints, but does not include a point face lying strictly inside the other interval.

Two containing unit-circle flank estimates imply W<=2 and

$$
\boxed{|K|\leq\frac W2\sqrt{1-W^2/4}+\arcsin(W/2)
\leq\pi/2<M_A.}
$$

This bounds the whole hull, so it excludes every body inside it without any motion, full-turn, or contact-order assumption. It disposes of the geometry of the earlier narrow enclosure counterexample without pretending its false enclosure inequality is true.

### A verified error-absorption test

On the already proved reflected protected-repair family, [EA1](stability-error-absorption-check.md) uses the actual area gain and AF4's exact error to obtain

$$
0\leq E(S)\leq\varepsilon:=M_A-|S|,
\qquad D(h)\leq2\varepsilon.
$$

Hence its actual convex hull satisfies

$$
d_H(K,K_*)\leq\sqrt{8\pi/7}\sqrt{\varepsilon}.
$$

The positive error is paid for, not dropped. This is a quantitative consequence on the existing family, not a new global neighborhood or a comparison of the original nonconvex bodies.

## Strongest earlier geometric routes, retained

[Theorem CW4](curvature-only-wide-hulls.md) gives sharp ordinary-area optimality and exact uniqueness for unit-span hulls with curvature dominated by dtheta and horizontal width W>=2. It does not assume contact order, full turns, or aligned faces; those geometric requirements are supplied or bypassed in its proof.

[Corollary WG4](31-closed-curvature-class-theorem.md) is an alternative sufficient route using curvature domination and both contact inequalities p<=q in a common incoming unit-span normalization. Its [width gate](64-width-gate-from-curvature-and-contact.md) derives full turns from those hypotheses.

The [signed-roof formula](curvature-only-signed-roof.md) computes the exact clipping-minus-negative-roof correction without contact order, once curvature domination and full turns are available. [The coupled repair identity](ordinary-area-repair-coercivity.md) has a coercive remainder but retains the geometric feasibility and contact-work hypotheses of the proposed repair.

None of these results asserts curvature domination for every unrestricted maximizing hull.

## Roadmap with explicit unresolved comparisons

The narrow-width task is not merely to improve a coarse global constant. In the curvature-dominated class, CW4 settles W>=2 and DF1 settles ordered faces. Remaining narrow configurations can have overlapping or nested face intervals and partial endpoints. The explicit 11/768 profile gap supplies an error budget, but **no uniform ordinary-error estimate within that budget has been proved**.

The global curvature task still needs a maximizing-body theorem or a genuinely area-improving comparison handling all excess curvature, including obstructed contacts and atoms. [Note 67](67-removing-the-fiber-clearance-hypothesis.md) excludes singular-continuous curvature at strictly clear exposed points; its residual outer-point/inner-corner coincidence set is not proved null. Hidden/coincident atoms and the sharp bound on absolutely continuous density remain unresolved.

An area comparison for one attained maximizer would determine the optimal value. Exact uniqueness needs the result for every maximizer or an equality-preserving recovery. A bound E<=D alone proves a value bound but does not force D=0; its equality case must also be controlled. The current work does not call that step routine or completed.

## Foundations, negative controls, and history

The earlier notes contain common-hull canonicalization, unit-span normalization, correct-angle reduction, connected niche separation, a uniform bounding box, attainment, quantitative finite-angle completion, and selection of any prescribed maximizing hull. They do not identify that hull with the candidate. The finite selection penalties vanish; contact normal-cone terms have not been shown to vanish.

Failed routes are retained: frozen switches, adaptive ordinary-area enclosure, signed area outside the hull, raw-partition nonconcavity, freezing a moving max-min contact, substituting full edges for visible edges, and silently deleting contact multipliers. High-area feasible hulls can violate curvature domination; the dominated class is closed, so smoothing cannot impose it on an arbitrarily close approximation of a fixed violating hull.

The detailed previous structural inventory is [Note 57](57-focused-structural-status.md); earlier ledgers are chronological snapshots. This README records the later AF/CW supplements and the PR #8 transfer, rather than adding another numbered status note.

## Reading map

| Source | Role |
|---|---|
| [PR #8 audit](stability-pr8-transfer-audit.md) | Pinned dependencies, formalization scope, and the noncircular transfer boundary. |
| [Fixed-width deficit](stability-fixed-width-deficit.md) | Exact nonsmooth energy, explicit profile coercivity, and ordinary-error bookkeeping. |
| [Width certificate](stability-width-gap-certificate.md) | Exact optimizer family, scalar curvature, and the narrow-profile gap. |
| [Ordered faces](narrow-separated-face-area-bound.md) | A direct ordinary-area exclusion using unit-circle flank bounds. |
| [Error-absorption check](stability-error-absorption-check.md) | A valid stability consequence on the already verified repair family. |
| [AF3](adaptive-functional-global-calibration.md) and [AF4](adaptive-functional-enclosure-counterexample.md) | Global auxiliary calibration and a concrete failure of ordinary enclosure. |
| [CW4](curvature-only-wide-hulls.md), [signed roof](curvature-only-signed-roof.md), [narrow example](narrow-curvature-enclosure-counterexample.md) | Geometric curvature-class comparisons and their exact limitations. |
| [Notes 1–24](24-current-proof-ledger.md) | Initial foundations, exact functional, restricted geometry and early counterexamples. |
| [Notes 25–51](51-current-proof-status.md) | Attainment, weak curvature class, selection, repairs and coarse unrestricted bounds. |
| [Notes 52–67](57-focused-structural-status.md) | Constrained variations, singular improvements and contact-measure analysis. |

## Sources and execution

Romik's [explicit construction](https://arxiv.org/html/1606.08111v3) identifies the candidate. Baek's [sharp-majorant approach](https://arxiv.org/abs/2411.19826), the repository's [uniqueness manuscript](../paper/), and the pinned [PR #8 stability notes](https://github.com/vltanh/lean4-moving-sofa/tree/1a97bc70782652f29c29dd4866115bd288c53e86/docs/stability) motivate the methods. Standard measure and analytic inputs are cited where used. This is not a comprehensive literature or priority review.

No CI was requested or used. No Lean/Lake compilation, dependency installation, numerical experiment, computer algebra, or manuscript build was performed in this continuation. Every research commit includes `[skip ci]`. No files from PR #8 were merged or cherry-picked; the transfer consists of attributed pen-and-paper arguments. Keep PR #3 open and draft while the unrestricted ordinary-area comparison and independent review remain unfinished.
