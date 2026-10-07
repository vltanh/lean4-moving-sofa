# Ambidextrous sofa research — start a new session here

**Unrestricted optimality is not proved.** The newest hand proofs allow variable middle supporting data in the clipping comparison and retain a quantitative middle deficit after rough tail changes. A second transfer theorem no longer needs exact reference collars for inward changes. Both still require curvature-controlled backgrounds whose admission from arbitrary competitors is unproved. Unrestricted uniqueness remains deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base: `main`.
Latest substantive review before this update: `e0915bcc07e5485a2d628ac0aefe1c1736b37a35`.
Always query the live branch and read intervening commits. Do not reset to the historical paper branch.

## 1. Instructions and verification boundary

Prefer pen-and-paper proofs. Use short computations to check explicit algebra or reject a proposed step: at most 30 seconds per invocation, preferably external five/ten-second limits. No long optimization or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`, under docs/ambidextrous. Refresh blob SHAs and preserve concurrent work.

All mathematical results are written and self-reviewed, not independently refereed or kernel-verified. Read [middle-tail-transfer-review.md](middle-tail-transfer-review.md), then the proofs actually used. The earlier full-turn supremum reduction is reviewed in [positive-face-density-review.md](positive-face-density-review.md); the weighted chain in [weighted-value-proof-review.md](weighted-value-proof-review.md).

The explicit reference has

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

An upper bound on one attained unrestricted maximizer proves the value. But the positive opposite-face subclass need not attain its supremum: do not silently choose a maximizing member of that nonclosed class.

## 2. Current exact full-turn target

For the actual full-turn cap pair U,V and nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad
\Psi(U)=|U|-|N(U)|-W(U)/2,\qquad G\ge0.$$

N(U) is the entire positive-height niche, not clipped to U. The written WV2 theorem makes Delta(U)=M/2-Psi(U) nonnegative. A sufficient remaining sharp comparison is

$$G\le\Delta(U)+\Delta(V).$$

The new results prove this on enlarged stated domains. They do not prove it for all saturated positive opposite-face bodies. Partial-turn bodies cannot be inserted into the full envelope without an actual angle-coverage theorem.

## 3. New MT/ME: variable middle supports plus signed rough tails

Read [movable-middle-tail-transfer.md](movable-middle-tail-transfer.md) and [middle-energy-with-rough-tails.md](middle-energy-with-rough-tails.md).

A background B has the reference projection [-m,m], a half-height rectangle, unit open-quarter support-curvature density, and niche height at most one half. It agrees with the reference only in three support collars near 0, pi/2 and pi; its middle supports are free. The collar angle is eta=2 arctan(1/10).

MT proves that the background's niche still has the exact paired circular tails and that all other old niche values have attaining middle parameters. This is proved by monotonicity of the two wall-tangency abscissae and a two-case end-angle pruning inequality, not assumed from reference similarity.

An altered cap U matches that background outside the top-normal window and obeys the explicit baseline barrier inside it. It retains the half-height rectangle. It may have facets, a collapsed top face or permitted outward changes; no curvature bound or unchanged contact pattern is imposed on U. The unchanged companion clearance pays for either sign of the tail defect.

MT1 gives

$$\Psi(B)-\Psi(U)\ge L(U),\qquad L(U)=\int_{-m/2}^{m/2}(1-A_U)dx.$$

ME retains the background's middle deficit. SR1 identifies its actual signed objective with the fixed-width functional. Reference stationarity, nonnegative squared-positive-part remainders and the Dirichlet inequality give

$$M/2-\Psi(B)\ge\frac7{50}\int|z'|^2,$$

where z is the pair of background support differences from the reference. Therefore two independent backgrounds and alterations satisfy

$$\boxed{|E|\le M-\frac7{50}\sum_{i=1}^2\int|z_i'|^2.}$$

The face-loss terms pay the actual clipping; the derivative energy applies only to the regular background middle, not to the rough altered support. This avoids the earlier axis-cut derivative-energy obstruction.

The domain has genuinely nonzero middle changes: small smooth support bumps of either sign where reference curvature is strictly between zero and one are admitted. A uniform support error at most 1/100 keeps corner height below 34/75. However the exact collars and background curvature conditions are real restrictions; this is not a complete neighborhood theorem.

## 4. New CT: no exact reference collars for inward changes

Read [curvature-weighted-tail-transfer.md](curvature-weighted-tail-transfer.md). Its backgrounds are general height-one, width-greater-than-two caps with half-height rectangles and niches, unit open-quarter curvature, positive top faces, suitable early/late signs, and lower density one half on the vertical-adjacent tails. The two backgrounds share their projection and top-face interval but may differ elsewhere.

For an inward tail support defect e, the two abscissa Jacobians are

$$dx_{inner}=(1-\rho)\sin t\,dt,\qquad -dx_{outer}=\rho\sin t\,dt.$$

Thus niche saving is at most integral e(1-rho), while outer loss is at least integral e rho. The retained surplus is integral e(2rho-1)>=0. Monotone absolutely continuous substitution handles bounded measurable densities and inner tangency plateaus.

CT1 proves

$$\Psi(B)-\Psi(U)\ge L(U)+J_B(U),\qquad J_B(U)\ge0.$$

For the two actual altered caps,

$$|E|\le\Psi(B_1)+\Psi(B_2)-J_{B_1}(U_1)-J_{B_2}(U_2)\le M.$$

The last step applies the existing SR/AF analytic bound only to the curvature-controlled backgrounds. Neither CT nor ME uses the weighted-maximizer source-flux chain or Gerver's theorem. CT does not allow outward defects without an additional sign argument; use MT's different domain for those.

## 5. New negative control: the lower half-density hypothesis matters

[HC](tail-half-curvature-obstruction.md) uses the exact downward stadium cap

$$h_B(\theta)=1/4+(4/5)|\cos\theta|+(3/4)\sin\theta.$$

It has width 21/10, top-face length 8/5, end heights 3/4 and quarter density 1/4. Its niche is confined to its top face and has height less than one half, so its symmetric full-turn body is genuinely feasible.

A small inward smooth support cut in a late same-sign interval gives exactly

$$\Psi(U_\varepsilon)-\Psi(B)=
\frac\varepsilon2\int\phi-\varepsilon^2\int(\phi'^2-\phi^2)>0.$$

The actual symmetric surviving area increases too. Thus the CT lower threshold cannot be deleted merely because both curvatures are bounded above by one. This is not a body above M; it rejects a stronger monotonicity claim.

## 6. What remains before unrestricted closure

The missing step is admission of arbitrary competitors to a sharp actual-area comparison, not another maximization of F:

- MT/ME do not produce their backgrounds or exact collars from arbitrary hulls.
- CT does not prove that arbitrary competitors have a global unit-curvature background with common face interval and the required tail lower bound.
- A small middle facet may violate the background density restriction; closeness alone is insufficient.
- PD/PS preserve the supremum in the positive opposite-face class but do not supply these backgrounds.
- No new result completes the uncovered partial turns across an unsafe strip interval.

The full-turn background-admission problem and the uncovered partial-turn comparison are still substantive unresolved obligations. The present notes do not justify saying closure is imminent.

## 7. Earlier geometric reductions retained

**RR/PD/PS.** Motion-preserving shrinking plus disk rounding, connected strip shaving, and safe-strip transport produce positive separated faces with areas converging to any full-turn body's area. Saturation preserves their actual hulls and connectivity. Hence the full-turn supremum equals the supremum over saturated positive opposite-end-face bodies. Reference approximants show there is no uniform strict gap below M for that whole class. Its supremum need not be attained inside the class.

**SI.** A safe strip direction supplies two hallway orientations. Full turns transport along a connected interval of safe strips. Partial turns complete if the entire interval between the relevant outgoing strip normals has width at most one. Three individual safe directions are insufficient. RR preserves the unshaved safe-strip set, so it does not remove a width bump.

**FAS/SCG/CSF/RS.** Full-turn aligned positive faces of any length are covered; additional retained-point tests force full turns in specified cases. Left-right reflection symmetry in a valid common incoming representation also gives an area bound without assuming symmetric or full original motions. No theorem supplies symmetry of an unrestricted maximizer.

**WV2.** The signed weighted one-turn value is M/2 in the written PA/WP/WR/AR/PT/TS/EB/TF/HF/CG/SE/VE/WV chain. VE's source-flux limit and earlier inputs remain independent-review points. SE explicitly uses Gerver's bound on a feasible one-turn body. That earlier dependency is not part of the new MT/ME/CT route, which invokes SR/AF directly on admitted regular backgrounds.

**TC/RB/STW.** The previous fixed-reference-middle budget, its explicit 1/101 boundary-layer saturation theorem and its signed tail extension remain valid stated subcases. They no longer describe the largest admitted variable-middle domain.

**Global restrictions.** AW-W/SW analytically give competitive width >1001/500; AL gives width <=2999/1020. AM/TE are earlier restricted exact computer certificates, not a full sharp covering or premises of the new hand proofs.

## 8. Failed shortcuts and source provenance

Keep RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1 and FF as negative controls. Body averaging, convex-cap averaging, saturation, least repair and unqualified face filling did not prove universal area enclosure. The new HC control is specific to the missing lower tail density. Canonical-wing accounting retains negative winding and uncovered material. Small extreme-height difference does not imply mid-height or C1 localization.

Original uploaded files and author-generated diagnostics remain preserved at their reviewed provenance checkpoints. Do not overwrite them or call an unexecuted source file a verification record. The old occupancy LP has structural fractional barriers; greater resolution alone does not fix it.

## 9. Short checks and next-session procedure

The new `computer-assisted/check_middle_tail_transfer.py` ran under an external five-second cap, taking about 0.105 seconds internally. Its 18 named tests include exact positive-part remainders, deficit expansions, pruning comparisons, signed pairs and Jacobian/gain identities, plus three negative controls. The record matches executed source blob `5f906630534e424f04955485ab5bef633c4afcb6`.

One 48-cut floating-point diagnostic ran under five seconds in about 1.079 seconds. Its finite-grid reference already has positive bias, so the small apparent sample excesses were not treated as counterexamples. No broader inequality was inferred from the absence of a defensible violation. The source and complete output are in the session bundle.

Read the live PR, this handoff, [ROADMAP.md](ROADMAP.md), and the latest review. Check a claimed implication before using it; do not replace exact admission hypotheses by proximity. Continue with a specific global ordinary-area comparison or a proved admissible background construction. No long script, CI, Lean/Lake compilation, dependency installation or manuscript build was used. PR #3 remains open and draft.
