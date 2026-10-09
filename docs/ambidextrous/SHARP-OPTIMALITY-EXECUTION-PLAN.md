# Sharp ambidextrous moving-sofa optimality — controlling execution plan

**ACTIVE plan · October 9, 2026.** This document, not the historical [ROADMAP.md](ROADMAP.md), sets the priorities for draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3). The [CONSOLIDATED-RESEARCH-HANDOFF.md](CONSOLIDATED-RESEARCH-HANDOFF.md) remains the authoritative record of what has and has not been proved.

**Honest baseline.** Romik's construction has proven area
\[
M=1+4Y^2+\arctan Y\approx1.64495521842544,\qquad 4Y^3+3Y-1=0.
\]
Unrestricted optimality, uniqueness, and exclusion of above-M bodies **are not proved** by the branch. Local stability, convex-only bounds, support classifications and numerical screens are not global sharp progress. The externally established bound \(353/200=1.765\) remains stronger than the branch's own coarse global bound.

## One non-negotiable final theorem

We must prove the sharp bound for **one connected physical shape** negotiating the *two distinct unit right-angle corridors*, from a common incoming orientation, with arbitrary continuous rotations including backtracking, subunit vertical height and **two independently partially completed turns**, using the actual outgoing straight-arm strips. No assumed reflection symmetry, contact pattern, curvature cap or full-turn completion.

The [OS1 original-motion signed formulation](original-motion-signed-convex-domain.md), *subject to Gate 0's independent audit*, converts that task to a single compact parameter domain. For every compact convex \(K\subset B=[-5/2,5/2]\times[0,1]\), write its projection \(I=[l,r]\), width \(W=r-l\), its two downward cap upper roofs \(A_U,A_V\), their outer deficits \(d_U=1-A_U,\ d_V=1-A_V\), and the exact positive swept-niche roofs \(n_{K;\alpha},n_{\rho K;\gamma}\) at independently visited angles \(\alpha,\gamma\). The true lower/upper whole-body outgoing strip barriers are \(e_{K;\alpha},e_{\rho K;\gamma}\).

Define the **complete joint ordinary-loss charge**
\[
\boxed{
\mathcal L(K,\alpha,\gamma)=
\int_I\left[
\max\{d_V,n_{K;\alpha},e_{K;\alpha}\}
+\max\{d_U,n_{\rho K;\gamma},e_{\rho K;\gamma}\}
\right]\,dx.
}\tag{PLAN.1}
\]
The exact **signed** envelope area is
\[
\boxed{\mathscr V(K,\alpha,\gamma)=W-\mathcal L(K,\alpha,\gamma).}\tag{PLAN.2}
\]
For auxiliary hulls with empty fibers, ordinary envelope area is the integral of the **positive part** of the fiber length, not the signed expression. For an actual connected feasible sofa its canonical envelope has every projected fiber nonempty, so the signed and ordinary expressions agree.

**The sole target theorem**, for all \(K\subset B\) and independently \(\alpha,\gamma\in[\pi/4,\pi/2]\), is
\[
\boxed{\mathcal L(K,\alpha,\gamma)\ge W-M.}\tag{PLAN.3 — UNPROVED}
\]
Given a fully audited OS1 equivalence, this proves unrestricted \(\mu_{\rm amb}\le M\); Romik supplies the reverse inequality, hence equality. A direct bound for every physically admissible sofa is an equally acceptable substitute, but must actually cover arbitrary original motions rather than a named subclass.

**No shortcut is presumed.** General signed Minkowski concavity has a rigorous counterexample even with height one, one-turn weighted concavity fails on known rectangular families, unrestricted curvature domination is not established, and no reference perturbation theorem controls distant opposite-end hulls. Do not use those false or unproved global premises.

## Gate 0 — independently audit the bridge to original motions

**Status: PASS (October 9, 2026; written mathematical audit, externally unrefereed).** The standalone [Gate 0 end-to-end proof](original-motion-global-bridge-gate0-audit.md) rederives the genuine wrong-way angular reach, exact two outgoing strips, common-hull tightening, empty-fiber signed correction, width-five compact box, and area-preserving horizontal gap compression for **both independent partial turns**. It proves the complete supremum equality \(\mu_{\mathrm{amb}}=\sup_{K,\alpha,\gamma}\mathscr V(K,\alpha,\gamma)\) on the planned parameter domain. It also gives a genuine unit-height high-area tilted top-cut family with **positive ambient clipping**, confirming the max/min accounting is indispensable. Note 9's older niche subtraction was **correct** because it had already defined both niches as **\(K\)-clipped** sets; an earlier suspicion of an error in that identity was a notation misunderstanding, not a discovered counterexample. The new independent proof is self-reviewed and open to external mathematical scrutiny.

**Gate 0 is no longer the active workstream. The next active proof obligation is Gate 1, the global full-turn sharp ordinary-area charge.** Before invoking the global variational target as a final proof, independently rederive and check:

- the correct-handed and terminal-angle reduction for arbitrary motions with area near or above M, including **the two actual outgoing strip normals** (GH / Note 10);
- canonical supporting-hallway tightening and both positive niche envelopes, including all end-angle conventions (OS1);
- the **max/min vertical fiber identities**, sign of the empty-fiber correction, and why a connected actual body has no empty projected fiber (OS1);
- area-preserving **horizontal-gap compression** for arbitrary auxiliary disconnected envelopes while retaining BOTH turning families AND outgoing strips (GC4);
- the fixed compact hull box, and exact reference equality \( \mathscr V(K_*,\pi/2,\pi/2)=M\).

**Adversarial checks, not proofs by sampling:** test the formulas against an auxiliary rectangle with empty central fibers, a disconnected full-turn envelope, a nonsymmetric opposite-end-face polygon, a genuine partial-turn triangle with its outgoing strip, and Romik. If a dependency fails, **repair the target and prove the correction** before continuing. No claim that a long self-reviewed chain was independently audited when it was only cited.

**Gate 0 PASS:** short, stand-alone checked proof of the actual-geometry-to-PLAN.3 value implication, or an exact counterexample and corrected theorem. **Gate 0 FAIL:** an essential implication is false and no valid replacement exists. This becomes the immediate research priority, not an invitation to switch to another local sofa class.

## Gate 1 — global sharp FULL-TURN area, using one joint loss mechanism

**Status: ACTIVE (October 9, 2026).** Gate 0's original-motion bridge has passed written audit. The full-turn global charge remains **UNPROVED**, with the actual clipped union of both inner-ray sweeps the key mathematical barrier. First prove PLAN.3 with \(\alpha=\gamma=\pi/2\) (outgoing barriers redundant):
\[
\boxed{
\int_I\big[\max(d_V,n_-)+\max(d_U,n_+)\big]\,dx
\ge W-M.
}\tag{PLAN.4 — UNPROVED}
\]

**One chosen mechanism:** construct a **joint spatial charge/transport certificate** for the *actual max of the entire moving inner-ray sweeps and outer-wall deficits*. Every piece of material removed from a horizontal fiber must be paid once; any clipped or overlapping niche must stay inside the max. Seek a global inequality connecting these actual disjoint area losses to the outer support geometry. The whole continuum of actual corner positions, stationary ray envelopes and switches is in scope. An allocation that assumes candidate contact phases, single-peak corners or positive-width central rectangles in every competitor is inadmissible.

**One decisive reduction to audit:** [PD3](full-turn-positive-face-density.md) says unit-height full-turn sofas with positive top/bottom faces at **opposite ends** are area-value dense. If its whole rounding/shaving/strip-reorientation chain passes audit, a uniform sharp inequality on that class plus a legitimate limiting argument would settle the complete-turn value. This is the most relevant adversarial class, **not** something to exclude by a fixed positive gap: it already contains bodies approaching M from below. If PD3 fails, use the original full hull domain rather than treating the class as exhaustive.

**Falsification protocol:** Before promoting *any* proposed area-transfer lemma, test it on exact polygonal opposite-end shapes, nonsmooth high-curvature cases, the reference (must admit equality), arbitrarily near-reference cut caps, pinched/disconnected auxiliary envelopes and the known unit-height rectangular signed-concavity counterexamples. A false lemma is discarded with an **exact mathematical counterexample**, not rescued by adding endless special hypotheses.

**Gate 1 PASS:** a real global full-turn sharp upper bound with exact ordinary/signed corrections and verified class coverage. **NOT PASS:** another near-Romik no-gain family, a small quantitative nonconvexity statement, a better convex-only bound, new contact classification, random numerical Jensen tests, or conditional star-concavity.

## Gate 2 — original PARTIAL turns with their two outgoing strips

**Status: BLOCKED.** Extend the **same joint charge** to all independent \((\alpha,\gamma)\) in the original OS1 domain, including any subunit height; alternatively prove a valid no-loss reduction from *every* original partial motion to a class controlled by Gate 1.

**Must not assume** a partial turn can always be extended to \(90^\circ\) in the same orientation. Exact counterexamples show zero-loss in-place completion fails. Saved early or late niche area must be compared with actual outgoing-strip losses in the **joint max**, not as independent signed deficits.

**Gate 2 PASS:** PLAN.3 or equivalent for the entire original motion domain and a complete deduction \(\mu_{\rm amb}\le M\). **NOT PASS:** only turns near \(90^\circ\), the known rough endpoint-angle exclusions, or results requiring a Romik-neighborhood support chart.

## Gate 3 — equality, uniqueness and independent review

**Status: UNSTARTED.** Only after the unrestricted sharp value is proved, analyze whether every equality sofa has Romik's hull, complete terminal angles and actual area. Equality in any signed/support interpolation is not enough without connectedness and actual-hull retention. Prove uniqueness **separately**, if it is true.

Compile one self-contained manuscript, with all key equations and reduction proofs exposed for independent mathematical review. No claim of Lean verification, automated kernel proof, or externally accepted publication.

## Rules for every subsequent research turn

1. **One active gate, one active global lemma.** Work Gate 0, then Gate 1, then Gate 2, then Gate 3. Do not start a new local deformation program when blocked.
2. **Report truthfully:** exact claim tested; what would settle it; proof or counterexample; remaining obstruction; **whether the unrestricted bound actually improved**.
3. **Strict commit filter:** commit only corrections to an indispensable global dependency, globally quantified proof steps, rigorous falsification of a needed global lemma, a certified *unrestricted* area improvement stronger than the known public upper bound, or a complete sharp proof. No paper padding, repeated convex estimates, or random-search artifacts.
4. **No made-up progress:** a negative result or failed attack can be useful, but is not presented as making the sharp bound closer. Count *passed gates*, not commits.
5. **Fixed stopping rule:** if the active inequality remains unproved after targeted falsification, report its exact missing measure or geometry estimate. Any change of mechanism must give a specific mathematical reason for abandoning the prior one, while preserving PLAN.3 as the north-star theorem.
6. **No deferred work promise:** perform current-session work and report the result; never assert background progress or promise a delivery date.
7. **Repository discipline:** [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3), branch research/ambidextrous-pen-and-paper; all research commits marked [skip ci]; no CI, Lean/Lake, or original Lean library changes.

## Current gate status (updated October 9, 2026)

| Gate | Status | Concrete missing step |
|---|---|---|
| 0 — original-motion bridge | **PASS** (written audit) | End-to-end audit in original-motion-global-bridge-gate0-audit.md; still subject to external review |
| 1 — coupled full-turn loss | **ACTIVE** | Need global transport from arbitrary outer-support area to complete union of two swept inner-ray losses, especially opposite-end faces |
| 2 — complete original partial motions | **BLOCKED** | No sharp charge for both independent outgoing strips together with visited partial niches |
| 3 — equality/uniqueness | **UNSTARTED** | Requires unrestricted area theorem first |

**Definition of meaningful progress:** a passed gate, a global theorem that removes an indispensable gap, or a correct falsification requiring a documented change in the global strategy. Everything else is supporting research.
