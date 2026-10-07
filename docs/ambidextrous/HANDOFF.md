# Ambidextrous sofa research — start a new session here

**Primary milestone: optimal value only. Unrestricted optimality remains unproved.** Uniqueness is deferred. Written results are self-reviewed; their historical dependencies have not all been independently audited.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3. Its live base was **main** at this update; do not reset it to the historical paper branch.
Last substantive checkpoint before this update: `eca44a3cb46df2016791d0b922e3a060607251be`.
Always query the live branch tip and read intervening changes first.

## 1. Current user instructions

Prefer pen-and-paper proofs. Computer assistance is restricted to short checks: new diagnostic invocations are capped at 30 seconds, and the latest checks used stricter five/ten-second external limits. Do not launch large searches, multistart campaigns or repeated refinements without new user authorization. A timeout is an unfinished check, not evidence of a theorem.

Commit substantive positive and negative findings frequently with `[skip ci]`. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Keep changes under `docs/ambidextrous/`, preserve concurrent edits, and keep the PR draft while the theorem is unfinished.

The known feasible candidate has

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

For optimal value, a valid bound on one attained global ambidextrous maximizer suffices. Do not make proving uniqueness an additional prerequisite.

## 2. Most recent analytic results: TF and HF

Read [tangency-floor-review.md](tangency-floor-review.md), then [one-turn-tangency-floor-bound.md](one-turn-tangency-floor-bound.md) and [one-turn-half-width-top-face.md](one-turn-half-width-top-face.md).

The optimization domain here is the signed one-turn cap problem

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

where the full positive-height niche N(U) is subtracted without clipping. These results concern **weighted global maximizers**, not arbitrary ambidextrous maximizing bodies.

### Inputs already available before TF

PA2 supplies attainment. ST1 gives upper roof at least one half. WP1--WP2 select any prescribed weighted maximizer with summable polygon facet errors. WR1 gives bounded open-quarter curvature and half-height vertical end edges. AR7 gives stronger same-sign inequalities. PT3 proves the top face has positive length, removing the T=0 exception from TS1; hence every weighted maximizer has niche height at most one half and both endpoint arms at most 9/4. EB1/EB.10 identify the limiting **actual** exposure with curvature and give a vanishing sum of absolute finite facet defects.

### TF: niche confinement and zero symmetric clipping

With L=pi/2, f(t)=h_U(t), g(t)=h_U(t+L), p=f'-g+1, q=g'+f-1, TF proves

$$
(f-1)\sin t+f'\cos t>0,\qquad
(g-1)\cos t-g'\sin t>0\quad(0<t<L).
$$

The proof is a controlled differential-inequality comparison with bounded measurable coefficients and explicit rational trigonometric bounds. It does not assert the saturated ODE or unit curvature.

The baseline wall intercepts are therefore strictly monotone. If the top face is [a,b] at height one,

$$N(U)\subset(a,b)\times[0,1/2].$$

The reflected surviving intersection S_U is an actual connected ambidextrous body through height one half. Its previously positive clipping correction now vanishes:

$$\boxed{|S_U|=2\Psi(U).}$$

Its actual hull is U intersect rho(U), with aligned top and bottom faces. This removes clipping for this **specific construction** only, not for all two-turn cap pairs.

### HF: exact half-width top face and convex core

AR3's candidate value and the actual construction above give |S_U|>=M. AW-W then forces W>2. The initial and final quadrant tests imply that the positive niche projection is exactly (a,b).

HF proves convergence of the selected finite niche projection lengths using WR's uniform non-axis curvature estimates; it does not infer this from niche-area continuity. Combining it with EB and the finite projection identities yields

$$\boxed{T=b-a=W/2>1.}$$

There is a genuine convex core V such that

$$\boxed{U=V+([0,T]\times[0,1/2]),\quad W(V)=T,\quad H(V)=1/2,}$$

and V has a point top and no vertical end edges. A finite Green-area identity, passed using EB, gives the stationary identity

$$\boxed{2\Psi(U)=\operatorname{Per}(V)-T.}$$

This identity is only proved for weighted maximizing caps. It is not a universal perimeter objective on arbitrary convex cores, and its right side has not been sharply bounded by M.

## 3. Important correction: balance does not imply maximum local exposure

Read [exposure-saturation-gap.md](exposure-saturation-gap.md). The old proposed no-hiding contradiction was invalid. From actual exposure tau_j approximately equal to outer length ell_j and tau_j<=L_j, one cannot conclude tau_j=L_j. Hidden length L_j-tau_j can persist while the actual balance defect is zero.

SP1 remains an analytic theorem for the proposed saturated ODE. It cannot be applied to an actual maximizing cap merely by citing EB. A further exposure identification or a different comparison is required. TF and HF avoid that inference.

## 4. The exact unresolved weighted target

Let [x_L,x_R] be the cap projection and [x_tl,x_tr] its top face. The endpoint arms are

$$d_R=x_R-x_{tl}=1+q(0),\qquad d_L=x_{tr}-x_L=1-p(L).$$

[AR6'](one-turn-arm-reduction.md), with its [review](one-turn-arm-package-review.md), shows that **EA2: d_R,d_L<=2 for one attained weighted maximizer** would give the sharp weighted value max Psi=M/2 through unit curvature, SR1 and AF3. The existing bound remains 9/4, not two. TF/HF do not establish EA2.

A different possible sufficient statement is a sharp perimeter comparison on the stationary rectangular cores in HF, retaining all their maximizing-body conditions. No such comparison is proved. Avoid maximizing over arbitrary half-height cores and assuming the stationary identity still holds there.

## 5. The global two-turn comparison is still separate

For general full-turn caps with common projection and nonempty two-turn fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

Empty fibers add another correction. TF only eliminates G for the symmetric body constructed from a weighted maximizer. It does not prove every ambidextrous body is dominated by such a body. Even a sharp weighted value would still require a valid unrestricted ordinary-area comparison.

OT3--OT4 and OA.3 provide scoped face and angle reductions. OT5 supplies zero clipping under its actual aligned-face and two-sided positivity assumptions. CW4 gives a sharp geometric theorem when the actual wide hull has unit open-quarter curvature; deriving that for an arbitrary maximizing hull remains open.

The canonical-wing bookkeeping remains

$$|S|-\widehat{\mathcal W}=N+U-B,$$

with multiplicity-weighted negative winding N, uncovered material U, and nonnegative deductions B. Neither positive term has a global paid budget. A simple-looking signed curve is not automatically ordinary area.

## 6. Direct-area results retained, but no long new computations

[AW-W](analytic-width-theorem.md) proves W<=2 implies area<41/25<M. The now-published [AL1](anchor-width-localization.md) proves competitive width at most 2999/1020<3. Its earlier local bundle is no longer the sole source of this width argument.

[AM2](matching-tilted-exclusion.md) has an executed all-width certificate for a specified steep extreme-height rectangle. [TE1](terminal-angle-exclusion.md) has an executed endpoint covering proving competitive turns exceed 2 arctan(29/50)>pi/3. They do not cover balanced configurations or prove full turns. The matching/triple frameworks and their proof-data policies remain in their own notes.

Read the [occupancy audit](occupancy-relaxation-audit.md) before any future use of the computer plan: the unconditioned triple LP has a 2/3 fractional barrier; pairs retain a 1/2 barrier. More resolution alone does not solve that problem. The user's new preference is for short checks and hand proofs, not another large certificate search.

## 7. Reproduction and short exploratory work

The latest exact checker is [check_tangency_floor.py](computer-assisted/check_tangency_floor.py). Run it under an external short cap:

```sh
timeout 5s python docs/ambidextrous/computer-assisted/check_tangency_floor.py
```

Its [record](computer-assisted/tangency-floor-checks.json) contains 18 named rational checks, including 54 rational area-identity cases and two negative controls. Internal checks took under one millisecond. Its executed bytes match Git blob `c526fa787c63dc234f8a66e3dfc7c249d2b5fedc`. It checks constants/algebra, not the continuum proof or historical geometry.

The review records several tiny prescribed-transition linear-control experiments. Their solver-loop times were under 0.1 seconds and their external caps ten seconds. They produced no exact infeasibility certificate, no coverage of arbitrary transitions and no validated cap counterexample. A crude rectangle bound was also too weak and was abandoned. Sources and outputs are retained in the bounded-check session bundle. These observations are not proof inputs.

## 8. Provenance and negative controls

The original one-turn proposal is preserved at `7c2cb37...`, with [its audit](one-turn-proposal-audit.md). Its numerical optimizer used clipped area rather than signed area and had a repeated-abscissa bug. The original arm package is preserved at `0b187ac...`, with [the arm review](one-turn-arm-package-review.md). Its full replay and earlier 23 symbolic checks are historical diagnostics, not permission for renewed long runs. The canonical-admission package and exact height checks likewise keep their stated domains.

Mandatory failed shortcuts: AF4 disproves universal adaptive enclosure; GR1 disproves unconditional ordinary-area increase under curvature repair; AX1/SAT1 and SC3 defeat corrected budgets even with saturation/shared anchors; TR1 permits suboptimal repair-saturation fixed points. SC3 point-face examples approach M, so a fixed threshold below M cannot exclude that face type. Small extreme-height difference does not force both endpoints near height one half. Weighted one-turn maximality cannot be applied to arbitrary two-turn caps.

## 9. Restart procedure

Query the live PR and inspect new commits. Read this handoff and [ROADMAP.md](ROADMAP.md), then the precise hypotheses of whichever proof step is pursued. The current analytic reduction is TF/HF, not an established no-hiding theorem. Work on one remaining sharp comparison and record a failed premise if encountered. Do not add unrelated calibrations or describe an auxiliary theorem as the unrestricted result.

Refresh file SHAs before updates and preserve other sessions' changes. Keep the computation limits explicit and do not claim unexecuted source is verification. No CI or Lean/Lake compilation was used; the PR stays draft and optimality remains open in this work.
