# Active roadmap: the remaining ordinary-area comparison

**Unrestricted optimality is not proved.** The signed weighted one-turn value is now established in the written WV chain. The long-face two-turn class is bounded by M through FL/LF. The primary remaining class has at least one horizontal face of length at most one. Unrestricted uniqueness is deferred.

Read [HANDOFF.md](HANDOFF.md) and [weighted-value-proof-review.md](weighted-value-proof-review.md) before continuing. All written arguments are self-reviewed; independent verification of the complete dependency chain remains outstanding.

## 1. Target and execution policy

For one attained global ambidextrous maximizer S, establish |S|<=M, where the known reference has

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

Do not add equality classification as a prerequisite. Prefer pen-and-paper proofs. Only short diagnostic scripts are authorized: maximum 30 seconds per invocation, preferably external five/ten-second limits. No large search or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantial positive and negative findings frequently with `[skip ci]`, under docs/ambidextrous.

## 2. Weighted subproblem: completed written value proof

The exact objective is

$$\Psi(U)=|U|-|N(U)|-W(U)/2,$$

with the entire positive-height niche subtracted. [WV2](one-turn-weighted-value.md) proves

$$\boxed{\sup_U\Psi(U)=M/2}$$

over the normalized full-right-angle cap domain.

| Step | Result and logical role |
|---|---|
| PA/WP/WR | Attainment, selection of a prescribed weighted maximizer, summable finite defects and bounded open-quarter curvature. |
| AR/PT/TS/EB | Same-sign bounds, a positive top face, half-height niche, and exact limiting actual exposure=curvature. |
| TF/HF | Positive tangency heights, niche confinement, zero symmetric clipping, T=W/2 and the stationary convex-core identity. |
| CG1 | Arm threshold sqrt(17)/2 suffices for a good quarter. It is stronger than the old sufficient criterion d<=2. |
| SE2 | Chords of the stationary core and the established Gerver bound give T<48/35; one arm is below 72/35<sqrt(17)/2. Thus one quarter is good. |
| VE2 | With one globally good quarter and a good future for the other, prove two boundary pieces globally visible and count their source flux. |
| WV1 | A hypothetical bad-quarter episode forces an energy to increase from above five to at most five. Contradiction: both quarters are good. |
| AR4/SR1/AF3 | Apply the admitted sharp comparison at the attained maximizer, obtaining WV2. |

The new proof does not assume that actual exposure is maximal merely because exposure=curvature. It does not require the proposed saturated ODE SP1. VE is the main new continuum review point: it keeps the two alternating source fluxes instead of assuming convergence of ordinary perimeter.

The ordinary Gerver bound in SE is an explicit external theorem applied to the feasible body U minus N. It is not an assertion that the weighted optimizer also maximizes unpenalized cap area. Its rational upper constant is derived from six pinned enclosures with the signs retained.

**Do not reopen weighted maximization or endpoint-arm search unless a specific proof gap is found in review.** The old excessive-curvature windows are intermediate reductions, not the active unresolved target after WV1.

## 3. Actual two-turn result: two long faces suffice

[FL1](aligned-face-optimality.md) proves |S|<=M for a compact connected ambidextrous body whose top and bottom common-hull faces coincide in an interval of length at least one. Its proof derives full turns from the contained unit square and confines both positive niches by connectedness of their baseline interval family and retained extreme face endpoints. Clipping vanishes, and the two WV2 inequalities add.

[LF1](long-faces-force-alignment.md) derives alignment when both horizontal face lengths are strictly greater than one. Small initial angles force the left endpoints to agree; the common square forces full turns; terminal angles force the right endpoints to agree. Hence

$$\boxed{\text{both face lengths}>1\Longrightarrow |S|\le M.}$$

This is an ordinary-area theorem, not merely an auxiliary maximum. It has no curvature, smoothness, symmetry or pre-assumed full-turn hypothesis. Its face-length condition remains a real restriction.

## 4. The remaining unrestricted cases

A possible counterexample with area greater than M must have at least one horizontal exposed face of length at most one. The class includes point faces, unequal short faces, shifted face intervals and partial endpoints not forced to a quarter turn.

The exact full-turn accounting remains

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0,$$

for nonempty surviving fibers and the actual cap definitions in OA. Empty fibers need an additional positive correction. Writing

$$\Delta(U)=M/2-\Psi(U)\ge0,$$

WV2 now gives the exact sharp form of the remaining full-turn comparison:

$$|E|\le M\quad\Longleftrightarrow\quad G\le\Delta(U)+\Delta(V).$$

This is a correctly signed target, not a theorem that its right side is always large enough. No positive clipping is discarded. A valid area-improving operation at a short-face global maximizer or a different ordinary-area inequality could replace this target.

| Remaining obligation | What counts as completion |
|---|---|
| Short-face maximality or area comparison | Prove a maximizing short-face body can be improved, or bound its actual area by M; include point-face cases. |
| Actual angular coverage | Use only orientations visited by the body's two motions, or retain the correction for missing intervals. |
| Positive clipping / winding corrections | Bound all positive terms by a proved deficit or avoid the decomposition with a valid ordinary-area upper bound. |
| Global assembly | Apply a proved case covering to an attained maximizer. Do not assume every maximizer has long faces. |

These are substantive geometric obligations. The new one-turn theorem does not by itself solve them. The known SC3 point-face examples approach M from below, so a fixed strict gap for the entire short-face class is not an available shortcut.

## 5. Alternatives and failure controls

The two-wing functional remains calibrated on its stated domains. [MW1](weighted-maximizer-canonical-wings.md) supplies full-height canonical wing data and outward-support agreement for the symmetric weighted construction, but not its core enclosure. All-angle wings are actual surviving material, yet [AO1](all-angle-wing-reference-obstruction.md) proves the old fixed-cut functional undercounts even the reference on that choice of wings. That substitution is ruled out analytically.

The ordinary-area winding identity is `|S|-widehat W=N+U-B`; negative winding N and uncovered surviving material U both matter. No universal correction budget has been proved. Do not replace it by a signed curve calculation with unexplained orientation or coverage.

Earlier controls remain AF4, GR1, AX1/SAT1, SAC2, SC3 and TR1. Repair, saturation, shared anchors and candidate proximity did not rescue those failed enclosures. A weighted-cap maximizing premise cannot be supplied by an arbitrary two-turn maximizer. Small extreme-height difference does not imply mid-height or C1 localization.

## 6. Direct ordinary-area certificates retained

AW-W excludes widths<=2 analytically. AL1 bounds competitive widths by 2999/1020. AM2 excludes its specified steep extreme-height rectangle across all widths, and TE1 proves competitive turns exceed 2 arctan(29/50)>pi/3. They do not cover the entire remaining class or supply a sharp local theorem.

The unconditioned occupancy LP has a 2/3 fractional barrier; adding pairs retains a 1/2 barrier. Anchors or other genuine logical strengthening are necessary. Any future certificate must verify all geometric witnesses, angle coverage, strict inequalities and complete parameter coverage independently. The present runtime policy does not authorize launching another large search.

## 7. Review and short checks

The new checker `computer-assisted/check_core_arm_reduction.py` uses only unbounded integers and rational arithmetic and ran under a five-second limit. Its 19 named checks cover rational constants and finite energy/flux/triangle identities; runtime was about 0.0021 seconds. The record matches the committed source blob. These regressions do not verify the continuum VE argument, Gerver's theorem or the entire historical chain.

The current review records the short failed six-anchor diagnostic and the all-angle-wing test that led to AO's exact obstruction. Neither floating-point run is a proof input. Older exact certificate replay records remain distinct from diagnostic output and from their untrusted generators.

## 8. Next-session rule

Read WV and VE with the review before using the new weighted result. If a flaw is found, state and repair that exact implication rather than silently weakening hypotheses. Otherwise move to a specified short-face ordinary-area comparison. No further independent auxiliary calibration is needed merely because it can be proved.

Keep all positive corrections and actual-body hypotheses visible. Commit negative findings. Do not describe a short conditional assembly as evidence that the remaining geometry is routine. The mathematical proof, not the PR state, is the goal; unrestricted optimality remains open in this work.
