# Fixed net rotation angle: proof-exploration memo (PEM)

## Current status

**The full interval `0 <= omega <= pi/2` is covered by the assembled paper-and-interval-certificate argument.** There is no remaining angle interval delegated to an unproved continuation assumption in this draft.

This is a **computer-assisted research proof draft**, not an independently refereed or Lean-checked theorem. The final continuation uses an executed outward-rounded interval verifier. The analytic arguments, implementation and arithmetic model remain explicit review dependencies.

Start with [all-angle-optimality-uniqueness.tex](all-angle-optimality-uniqueness.tex). It states the full theorem, exact contact-system definition of the optimizer, optimal-area formula, uniqueness of the admissible contact parameters, and qualitative stability at each fixed open angle.

| Angle range | Optimizer and proof route |
| --- | --- |
| `omega = 0` | The unit square, unique after normalization; area one. |
| `0 < omega <= 1` | Baek's relaxed-cap sofa is the unique normalized optimum; `m(omega)=1+omega^2/2`. Analytic proof. |
| `1 < omega <= 1.01` | Exact exposed-wall contact sofa. The analytic bridge supplies roots and admissibility throughout this explicit interval. |
| `1.01 <= omega <= 1.5706` | The same order-independent contact system, with parameter-uniform root and geometry verification in 750 interval boxes. |
| `1.5706 <= omega < pi/2` | A regular branch parameterized by `h=omega-c`; 16 parameter boxes and 15 joining boxes, followed by an analytic angle-coverage argument. |
| `omega = pi/2` | The companion Gerver optimality/uniqueness theorem. This is a separate endpoint input; horizontal translation is not fixed by the coincident endpoint support directions. |

All 781 contact records were replayed from their coordinates and preconditioners, without trusting their stored success flags. Exact rational coverage and endpoint joining containment were checked. The final verifier source hashes and record hashes are in [checks/CERTIFICATE_REPORT.json](checks/CERTIFICATE_REPORT.json). The standard-library builder and replay program are committed, and the full reference records are supplied in the verification attachment.

No CI, workflow dispatch, Lean compilation, axiom audit, or TeX compilation was run. Every research commit uses `[skip ci]`. Changes remain in `docs/fixed-angle/`; Lean sources, workflows and the original uniqueness manuscript are unchanged. Starting reference: `paper/uniqueness-arxiv` at `1ade045936f32cf76572ee668ed8aa1627772bde`. Here PEM means proof-exploration memo.

## Problem and normalization

The hallway remains `L = ((-infinity,1] x [0,1]) union ([0,1] x (-infinity,1])`. A motion's angular lift starts at zero and ends at `-omega`; backtracking is permitted. This is a prescribed **net rotation angle**, not a changed hallway angle or the minimum rotation intrinsic to a shape.

For `0 < omega < pi/2`, the two upper endpoint supports uniquely translate a sofa into

`P_omega = { (x,y) : 0 <= y <= 1, 0 <= x cos(omega)+y sin(omega) <= 1 }`.

Write `u_t=(cos t,sin t)`, `v_t=(-sin t,cos t)`, and `F_omega={y>=0, z dot u_omega>=0}`. The niche is defined using the **fan**, and the cap functional is `A_omega(K)=|K|-|N_omega(K)|`. Cap-minus-niche feasibility is proved for the constructed candidates, not assumed for arbitrary caps.

## Exact candidate above one radian

For `1 < omega < pi/2`, choose the unique admissible triple

`0 < phi <= 1/12`, `phi < b < min(c,omega-phi)`, `c < omega`.

Set `C=1_(phi,omega-phi)`, `B=1_(b,c)`, and `D(t)=B(omega-t)`. The piecewise elementary shooting equations are

`r_p=(C(g-1)+B)/(1+B)`, `r_k=(C(f-1)+D)/(1+D)`,

`f'=g-r_p`, `g'=r_k-f`, `p'=k-f`, `k'=g-p`.

Use `f(0)=k(0)=1` and the midpoint conditions `f(omega/2)=g(omega/2)`, `p(omega/2)=k(omega/2)`. The two linear shooting unknowns are uniquely determined in every contact ordering.

With

`gamma(t)=(p(t)-1)u_t+(k(t)-1)v_t`,
`e(t)=(p(t)-1)u_t+p'(t)v_t`,

the three nonlinear contacts are

`e(b)=gamma(phi)`, `e(c)_y=0`.

The sufficient admissibility tests are `p''<0` on every open coefficient interval, `p(0)<5/3`, and `g(0)-p(0)<1`. They imply positive thresholds, valid normal-gap atoms, a niche strictly inside the unit fan sector, and feasibility. The optimal sofa is the resulting cap minus its niche. Its area is the explicit boundary integral in the main paper; it is **not** `1+omega^2/2` above one radian.

The unique admissible root is an exact implicit definition, not a claim that the unconstrained shooting equations have no other roots. Global uniqueness first identifies the cap. The first onset of positive curvature then determines `phi`, and the balance equations recover the wall indicator and hence `b,c`.

## Non-circular proof chain

1. **Attainment and access to every maximizer.** Cap compactness and upper semicontinuity give a positive global cap maximizer. The companion's fixed-angle penalized selection and floating first variation reach any prescribed such maximizer.
2. **All-maximizer geometry.** The fixed-angle curvature proof includes the two outer endpoints, ruling out their atoms. The arm certificate, pinned endpoint estimates and global cut geometry yield strict arms, fan containment and separated cuts for every maximizing cap. No symmetry of the unknown maximizer is assumed.
3. **A valid universal lift on maximizers.** [vertical-core-lifting.tex](vertical-core-lifting.tex) replaces radial core contractions by vertical slices. It removes the unproved requirement that an unknown maximizing cap have all interior thresholds positive. The hypotheses now match exactly what the global geometry proves.
4. **Strict global comparison.** The lifted functional `Q` is strictly concave on a convex obstacle domain. The contact balance equations and exposed-wall geometry provide its global equality certificate. This applies against every original maximizing cap, not just candidates with the same contact pattern.
5. **A candidate for every angle.** The analytic bridge, compact interval cover and regular endpoint branch establish the existence of parameters satisfying the certificate's geometric hypotheses over the whole open interval.
6. **Recover the original sofa.** The candidate is regular closed. A closed subset of a regular-closed finite-area set with equal area is the entire set. Equality in monotonization therefore recovers arbitrary original compact sofas, not merely their caps or envelopes.

The computation only discharges root existence and finite admissibility inequalities. It does not replace the global majorization, equality rigidity, or regular-closedness arguments with a numerical optimization claim.

## What closed the continuation problem

[order-independent-shooting.tex](order-independent-shooting.tex) rewrites the arm boundary-value problem as a positive affine contraction on `L2 x L2`, with norm at most `2omega/pi<1`. This proves nonsingularity and strict arms independently of the ordering of reflected wall intervals.

[order-independent-contact-certificate.tex](order-independent-contact-certificate.tex) replaces near-transition expansions by exact projection and sine-kernel inequalities. It proves that the proposed arcs are exactly the niche boundary through the later contact crossings as well. Only explicit root and support tests remain.

[explicit-first-regime.tex](explicit-first-regime.tex) removes the existential interval near one: a parameter `L=b-phi` explicitly solves two contacts, brackets the remaining scalar contact, and covers `(1,1.01]` by continuity with rational admissibility bounds.

[validated-contact-cover.tex](validated-contact-cover.tex) explains the finite interval proof. The verifier encloses every actual event ordering, uses exact elementary propagation rather than an ODE solver, and checks strict support inequalities on whole coefficient intervals. It certifies `[101/100,7853/5000]` with no missed angle or contact crossing.

[endpoint-bridge.tex](endpoint-bridge.tex) uses `h=omega-c` to regularize the last interval. Its exact floor equation is

`cot(omega)=(1-cos h)/(d-sin h)`, where `d=g(0)-p(0)`.

The verified bounds `1/2<d<1` give `omega(0)=pi/2`, `omega(h)<pi/2` for positive h, and `omega(1/32)<pi/2-1/4096<1.5706`. Verified joining boxes produce a continuous branch, so the intermediate value theorem covers the entire remaining tail. No sampled monotonicity or extrapolation is used.

## Negative results retained

The earlier failures remain part of the argument, not discarded history.

- [negative-results.tex](negative-results.tex) gives a feasible convex monotone quadrilateral with empty niche and `A_1=1-omega < sec(omega)-tan(omega)=A_omega`. Universal majorization on all feasible caps is false; its endpoint atoms explain why the curvature endpoint audit matters.
- [beyond-one-radian.tex](beyond-one-radian.tex) proves `m(omega)<1+omega^2/2` for every `1<omega<pi/2` by attainment and strict relaxation rigidity.
- [redundant-angle-improvement.tex](redundant-angle-improvement.tex) proves the actual relaxed-cap sofa strictly suboptimal above one radian. A smooth outward support bump in a redundant-angle interval leaves the niche exactly unchanged and increases area.
- Assuming convexity of the raw niche correction, replacing the niche by its convex hull, or invoking right-angle rigidity after merely extending a motion are not used as shortcuts.
- A fixed numerical root or a finite angle sample does not prove continuation. The new records certify intervals, and the coverage check is exact.

The intermediate fifth-order transition and unique endpoint-profile results remain in their separate notes. The complete angle theorem does not erase those finer asymptotic results.

## Reproduction and validation boundary

The complete builder and verifier use only the Python standard library. From `checks/`:

```sh
python check_verifier_primitives.py
python build_contact_cover.py --part all --output-dir certificates
python verify_contact_cover.py certificates/*.json --report replay.json
```

Floating Newton steps and approximate inverses only propose data. Outward interval checks determine acceptance. The verifier uses Taylor enclosures for trigonometric functions, includes all compatible reflected event orderings, and recomputes every record before exact coverage checks. It does not trust stored booleans or approximate residuals.

A final audit corrected an unused mixed interval/second-derivative division dispatch. The primitive regression passed, and all 781 records were replayed again against the final sources. Source and data hashes are frozen in the report. This is not an independent implementation or a proof-assistant kernel verification.

The remaining work is independent review, consolidation of the research notes, and any later formalization. No unproved angle-continuation interval remains in the assembled argument. The different-hallway-angle and ambidextrous problems are outside this theorem's scope.
