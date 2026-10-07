# Active roadmap: hand proofs of the optimal value

**Unrestricted optimality remains unproved. Uniqueness is deferred.** Read [HANDOFF.md](HANDOFF.md) for the live-checkpoint procedure, provenance and detailed proof boundaries. All written results remain self-reviewed, with historical dependencies awaiting independent review.

## 1. Target and current execution limits

For one attained global ambidextrous maximizer S, establish |S|<=M, where

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The candidate already supplies the opposite inequality. It is unnecessary to classify all equality cases before proving the value.

The user's latest instruction prioritizes pen-and-paper arguments and short computer checks. New diagnostic invocations have a maximum 30-second wall-clock limit; the latest exact and exploratory checks used five and ten seconds respectively. No new long searches, multistart campaigns, dependency installation, CI or Lean/Lake compilation. A timeout or an unfinished covering is not a theorem. All substantial findings use `[skip ci]` commits under `docs/ambidextrous/`.

## 2. Completed weighted reductions and their exact domain

The signed cap problem is

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

subtracting the full positive-height niche, not clipped surviving area. Let P=max Psi, attained by PA2. The following apply to weighted global maximizers U, not automatically to arbitrary ambidextrous maxima.

| Step | Result and scope |
|---|---|
| PA2, ST1, HV | Attainment, height one, upper roof at least one half, niche-area continuity and uniform finite-angle approximation. |
| WP, WR | Selection of any prescribed weighted maximizer; summable facet defects; bounded open-quarter curvature; vertical end edges exactly one half. |
| AR7/AR5' | Same-sign curvature improvements and propagation of endpoint-arm information. |
| PT3 | Every weighted maximizer has a positive top face. The older T=0 exception is removed. |
| TS1--TS2 | Full niche height at most one half and both endpoint arms at most 9/4, now for every weighted maximizer. |
| EB1/EB.10 | Finite actual exposure measures converge to curvature; the sum of absolute interior facet defects tends to zero. |
| TF2--TF3 | Both single-wall tangencies have positive height; the niche lies strictly beneath the horizontal top-face interval. |
| HF1 | Top-face length T equals W/2, with W>2. |
| HF2--HF3 | Actual convex core V with U=V+([0,T] times [0,1/2]), width(V)=T, height(V)=1/2 and 2 Psi(U)=Per(V)-T. |

The newest proofs are [TF](one-turn-tangency-floor-bound.md) and [HF](one-turn-half-width-top-face.md), with their [review](tangency-floor-review.md). They use an elementary differential-inequality comparison, baseline wall intercepts, and exact finite projection/area identities. Their claims do not depend on numerical integration or a solver's status.

For the reflected two-turn body constructed from U, TF now gives

$$\boxed{|S_U|=2\Psi(U),}$$

with no clipping correction. It is an actual compact connected body, and its hull has aligned horizontal faces. This is a theorem for the construction from a weighted maximizer; it is not an upper domination theorem for every ambidextrous body.

## 3. What the exposure result does not prove

The previously proposed no-hiding argument is corrected in [exposure-saturation-gap.md](exposure-saturation-gap.md). Actual exposure tau_j can equal ell_j while remaining below a larger local upper bound L_j. The unaccounted slack L_j-ell_j is precisely what prevents inferring that the hidden contribution vanishes.

SP1 solves the proposed saturated ODE analytically. EB does not establish that actual maximizing caps follow it. TF/HF avoid this assumption. Do not reinstate it merely because the ODE has the candidate solution.

## 4. Remaining weighted sharp-value gate

With cap projection [x_L,x_R] and top face [x_tl,x_tr], write

$$d_R=x_R-x_{tl}=1+q(0),\qquad d_L=x_{tr}-x_L=1-p(\pi/2).$$

The sufficient endpoint condition **EA2** is d_R,d_L<=2. The present bound is 9/4. EA2 for one attained weighted maximizer would give unit curvature and the sharp value P=M/2 via the signed-roof identity SR1 and AF3. It has not been proved for one.

HF supplies the additional exact face moment T=W/2; this must be retained in any further endpoint comparison. An alternative sufficient target is Per(V)-T<=M for the **stationary cores** arising in HF. The stationary identity is not true for arbitrary convex half-height cores, so relaxing to all such V without another inequality is invalid.

A successful next lemma must actually prove one of these sharp comparisons or furnish a different valid weighted upper bound. More regularity, another detached functional maximum, or a fixed-sign sampled control experiment is not completion of this gate.

## 5. The remaining unrestricted two-turn gate

For general full-turn cap pairs with common projection and nonempty two-turn fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

An empty-fiber correction is also needed if that hypothesis is omitted. TF sets G to zero for S_U only. Even after a proof of P=M/2, the general upper bound does not follow while G is uncontrolled.

Possible sufficient approaches remain: an actual area-dominating reduction to the symmetric weighted construction; an ordinary-area estimate paying the exceptional clipping/face corrections; or a sharp direct two-turn inequality. These are open geometric obligations, not consequences of the new cap face ratio.

Full turns also cannot be assumed for every original body. OT/OA provide stated face and strip subcases. CW4 supplies a sharp bound for wide actual hulls under unit curvature, but a general maximizing-hull curvature theorem is still missing.

The two-wing alternative retains

$$|S|-\widehat{\mathcal W}=N+U-B,$$

where N is multiplicity-weighted negative winding, U is uncovered surviving material, and B>=0. Neither positive correction has a general paid budget. The calibrated height/cut domains, actual coverage of angles, and ordinary-area admission remain necessary.

## 6. Direct-area results retained without new long searches

AW-W excludes W<=2 analytically. The published AL1 narrows competitive widths to W<=2999/1020<3. AM2 supplies a complete width covering for a stated steep extreme-height rectangle; TE1 proves both competitive endpoint magnitudes exceed 2 arctan(29/50)>pi/3. They are restricted theorems, not a complete global certificate or a local candidate-neighborhood theorem.

The earlier [computer plan](optimality-only-computer-plan.md) must be read with the [fractional-barrier audit](occupancy-relaxation-audit.md). A triple-only occupancy LP admits z=2/3, and pairs still admit z=1/2. Arbitrary resolution does not overcome that obstruction. Anchors and exact pair certificates help only in their actually covered regions.

Under the current user instruction, do not launch a large computation simply to pursue those remaining boxes. Prefer a proved geometric reduction and use only bounded diagnostic checks.

## 7. Validation, unsuccessful tests and change log

The exact TF checker ran under an external five-second cap, with internal checks under one millisecond. It checked 18 named rational identities/inequalities including 54 area-algebra instances, and rejected two overstrong claims. Its [record](computer-assisted/tangency-floor-checks.json) matches the committed source. These checks are not independent verification of the continuum proof.

Three small midpoint control experiments with prescribed transition indices ran under ten-second caps. No continuous coverage, verified infeasibility certificate or cap realizability was obtained. A crude rectangle-niche bound was too weak and was abandoned. The [review](tangency-floor-review.md) records these limits; no sampled result is used in TF/HF.

Recent decisions:

- Corrected balance-versus-local-saturation inference; retained valid EB.
- Used the proved 9/4 endpoint bounds in a controlled oscillator comparison instead of assuming the saturated ODE.
- Proved niche confinement to the top face and removed clipping in S_U.
- Proved projection-length convergence with explicit derivative control, then T=W/2 from finite balance.
- Retained the actual rectangular core and stationary perimeter identity, without asserting the still-missing sharp perimeter bound.
- Kept the weighted sharp value and the unrestricted two-turn upper comparison as two separate unfinished gates.

Mandatory negative controls remain AF4, GR1, AX1/SAT1, SAC2, SC3 and TR1. Weighted maximality cannot be substituted for two-turn maximality; small |a-b| does not imply midpoint heights; finite support proximity is not a C1 neighborhood. Commit counts are not a progress metric. The PR remains open and draft.
