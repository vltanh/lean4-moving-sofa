# Active roadmap: a sharp background comparison still needs global admission

**Unrestricted optimality remains unproved.** The fixed-middle clipping theorem now extends to variable curvature-controlled middles with an explicit quantitative deficit, and to inward tail changes of more general backgrounds without exact reference collars. No theorem produces those backgrounds from every competitor. The uncovered partial-turn problem also remains separate. Unrestricted uniqueness is deferred.

Read [HANDOFF.md](HANDOFF.md) and [middle-tail-transfer-review.md](middle-tail-transfer-review.md). All proofs are written and self-reviewed, not independently refereed or kernel-verified.

## 1. Target and execution policy

For one attained unrestricted ambidextrous maximizer S, establish

$$|S|\le M,\qquad M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0,\quad Y>0.$$

Do not add unrestricted equality classification as a prerequisite. Prefer hand proofs; short computations are for checking identities and rejecting unsupported premises. At most 30 seconds per invocation, preferably external five/ten-second limits. No long search or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`, under docs/ambidextrous, while preserving concurrent edits.

## 2. The positive comparison now proved

The exact full-turn identity is

$$|E|=\Psi(U)+\Psi(V)+G,\qquad
\Psi(U)=|U|-|N(U)|-W(U)/2,\qquad G\ge0,$$

for nonempty surviving fibers and the stated cap definitions. The full niche is subtracted. Empty fibers outside this class require their separate correction.

The new approach distinguishes a regular background cap B from its possibly rough altered cap U. It proves

$$\Psi(B)-\Psi(U)\ge L(U),\qquad L(U)=\int_a^b(1-A_U)dx,$$

on the admitted domains below. For two backgrounds with a common face interval, L(U)+L(V) pays the actual cross-clipping. An already proved sharp bound on the regular backgrounds then gives an ordinary-area bound on the rough envelope. This is not a universal hull repair or a presumption that the altered caps maximize Psi.

| Domain | Proved statement | Still required |
|---|---|---|
| MT/ME | Variable middle supports; independent signed rough-tail changes; `area(E)<=M-(7/50) sum integral |z_i'|^2`. | Three exact reference collars, unit background curvature, half-height rectangle/niche, top-window support barriers. |
| CT | No exact reference collars; arbitrary independent inward top-window changes; `area(E)<=Psi(B_1)+Psi(B_2)-sum J_i<=M`. | Unit background curvature, common projection and face interval, half-height geometry, specified tail signs and lower density one half. |

MT's signed pairing checks the unchanged companion wall instead of assuming the changed parameter remains globally active. ME's derivative energy applies only to the regular middle, not the rough tail that defeated the earlier energy budgets.

CT's surplus is

$$J_B(U)=\int_{late}e_f(2\rho_f-1)+\int_{early}e_g(2\rho_g-1)\ge0.$$

It comes from the two exact area Jacobians rho and 1-rho. Exact circular collars are not needed for inward changes. The analytic SR/AF bound applies to the backgrounds; these new results do not need WV's maximizing-cap selection/exposure chain or Gerver's upper bound.

## 3. One lower-bound premise cannot be deleted

[HC](tail-half-curvature-obstruction.md) is a genuine feasible background with quarter density 1/4 and a small inward support cut that increases signed objective and actual symmetric surviving area. Its exact gain is

$$\frac\varepsilon2\int\phi-\varepsilon^2\int(\phi'^2-\phi^2)>0.$$

Thus unit upper curvature alone does not guarantee monotone tail transfer. A proposed extension below density one half must retain and pay the adverse term; it cannot round the density up to one half or infer the sign from numerical agreement on the reference. The same CT surplus can have the wrong sign for outward defects when rho>1/2.

The counterexample is not above M. It rejects a stronger intermediate comparison, not the goal of optimality.

## 4. The next actual admission gate

A sufficient new theorem would construct admitted background pairs for the remaining actual-body class, with a proved ordinary-area comparison. It must justify rather than assume:

- background unit curvature and the permitted tail density/sign regime;
- a common background face interval and the correct cap widths;
- that changing the middle, if necessary, does not lose the required upper comparison for the original body;
- actual full-turn coverage, or the appropriate correction for partial turns.

The new MT theorem does not supply this construction just because its middle supports are variable. CT does not supply it merely because exact reference collars are no longer required. Middle facets and arbitrary cap curvature remain outside the stated regular background domains.

A different sharp ordinary-area inequality may bypass this gate. In either case an auxiliary deficit or data membership alone is insufficient: retain clipping, winding, uncovered material and the original body containment.

Do not spend another pass re-maximizing the background functional F. The unresolved task is the geometric transfer for arbitrary competitors, not its already known sharp value.

## 5. Full-turn supremum and partial turns

RR/PD/PS prove

$$\sup_{full\ turns}|S|=\sup_{saturated\ positive\ opposite\ faces}|S|.$$

The reduction permits approximation and change of incoming orientation. The positive-face subclass need not attain its supremum. A local improvement theorem only for attained maxima inside that subclass does not automatically prove the value.

Reference approximants show there is no uniform strict gap below M for the entire positive opposite-face class, including after saturation. A long search for such a gap is not an appropriate strategy.

SI completes partial turns when the whole required interval of straight-strip normals has width at most one. An unsafe width bump is not removed by RR, which preserves the unshaved safe-strip set. The present background transfer does not create the missing angles.

Thus both the sharp full-turn admission and the uncovered partial-turn comparison remain substantive obligations.

## 6. Earlier inputs and case bounds

WV2 gives the signed weighted one-turn maximum M/2 in the current written chain; its VE limiting source-flux argument and historical inputs remain independent-review points. Do not assign weighted maximality to an arbitrary two-turn cap.

FAS covers every full-turn aligned positive-face body. SCG/CSF give additional six-point conditions forcing full turns. RS covers the left-right reflection-symmetric common incoming class without requiring symmetric original motions. No symmetry-reduction theorem for unrestricted maximizers is known in this work.

TC/RB/STW retain their earlier exact-reference-middle results, including arbitrary boundary-layer shavings and signed tail changes. MT/ME and CT enlarge those admitted domains but do not turn them into a global neighborhood theorem.

AW-W/SW/AL are analytic competitive-width restrictions. AM and TE are restricted exact computer certificates; they are not premises of the new MT/ME/CT/HC proofs and do not provide a complete sharp covering.

## 7. Checks and failure controls

The new exact checker ran under five seconds in about 0.105 seconds internally. It checks 578 scalar remainders, 768 integrand expansions, 420 pruning samples, 100 signed pairings, 25 Jacobian cases and nine finite gains, with three stronger-claim controls. Its record matches the executed Git blob. These finite regressions do not prove geometric admission or verify the continuum SR/AF dependency chain.

A single 48-cut exploratory run took about 1.079 seconds under a five-second cap. Its reference approximation already has a small positive bias, so no raw sampled excess was accepted as a counterexample and no universal inequality was inferred. The analytic HC counterexample does not rely on this run.

Retain the earlier negative controls RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1 and FF. Saturation, averaging, face filling and support-energy admission did not automatically preserve actual sofa area. The old occupancy LP's fractional barriers cannot be removed just by resolution.

## 8. Next-session discipline

Read the new proofs with their review. If an implication is wrong, state and repair that exact point. Otherwise attack a specified background-admission or partial-turn comparison. Do not replace a stated curvature or support constraint by a claim of closeness to the reference. Keep scripts bounded, preserve all correction signs, and commit negative findings. PR #3 remains open and draft; unrestricted closure and independent verification are unfinished.
