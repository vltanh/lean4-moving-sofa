# Active roadmap: geometric admission, with an audited one-turn alternative

Read [HANDOFF.md](HANDOFF.md) first for the live-checkpoint procedure, provenance, validation status and failed routes. **Unrestricted optimality and uniqueness are not proved.** A short conditional assembly is not evidence that its geometric premises are routine. All written results remain subject to independent review.

## 1. Target and quantifiers

For an arbitrary attained maximizer S, establish either a directly sharp ordinary-area inequality or data xi such that

$$
|S|\le Q(\xi)\le M,
\qquad M=1+4Y^2+\arctan Y,
\quad4Y^3+3Y-1=0,\quad Y>0.
$$

Track equality through every comparison to recover S itself up to congruence. A theorem for one attained maximizer gives the value, not automatically uniqueness of every maximizer.

Never infer candidate-neighborhood entry from the optimality or uniqueness being sought. Never substitute a signed curve integral for ordinary area without the required orientation, containment and correction terms.

## 2. Current two-wing results

The domain and base calibration are TW/WS/WC. [CS1–CS2](two-wing-cut-slack.md) retain actual inward supporting-line intersections and the four nonnegative cut-width slacks. Corner completion preserves all core supports and constrained widths while increasing the two counted wing areas. The favorable endpoint first variation has coefficient `tan(beta)/2` times the total slack.

[SQ1](two-wing-slack-quadratic.md) proves the sharp inequality and equality case with arbitrary cut slack when both wings span the common strip. Negative quadratic slack terms are paid by the positive first-order terms; joint concavity on an unrestricted affine space is not claimed.

[NH1](two-wing-near-full-height.md) allows unequal heights when the wings share their bottom supporting line and

$$
\min(H_R,H_D)\ge1-\sin\beta/2.
$$

This is an additional completed subcase of R4, not admission of arbitrary maximizing sofas. That geometric height property is still unproved. The CS/SQ checker has a recorded executed run; the NH checker source has no execution record established in this pass.

## 3. Existing critical-path gates

| Gate | Acceptance criterion | Status |
|---|---|---|
| R0: audit | Derive signs, endpoint terms, reference geometry and equality from definitions; check actual code/source correspondence. | Exact finite CS/SQ checks are recorded. New proposal audit is separate. Neither is independent verification of the whole branch. |
| R1: normalization/coverage | Preserve containment from an arbitrary body through normalization and saturation, with attainment available. | Earlier written reductions and analytic `2<W<4` restrictions; not curvature domination. |
| R2: terminal angles | Prove every angle used by the chosen representation is visited, or pay for missing intervals explicitly. | Open globally. OT4/OA.3 close a specific face-rectangle subcase only. |
| R3: canonical wings | Construct actual convex safe pieces satisfying the calibrated strip, width and height conditions. | Open globally. Shared-bottom and NH1's height threshold cannot be assumed. |
| R4: cut slack | A sharp certificate on a domain covering those actual data, or a proved reason excluding the rest. | WC2, SQ1 and NH1 cover stated subcases. Arbitrary slack with arbitrary relative heights remains unproved. |
| R5: ordinary-area core | Prove containment and a valid area formula/upper bound, retaining clipping and nonsimple-curve effects. | Open globally. Disjointness is unnecessary for an upper bound by subadditivity; the area accounting remains necessary. |
| R6: value | Apply admitted sharp comparison to an attained maximizer. | Conditional on the needed geometric gates. |
| R7: uniqueness | Equality must recover the original closed body, not just auxiliary data. | Conditional recovery exists; unrestricted admission remains open. |

R2–R5 are substantive linked obligations, not one routine lemma.

## 4. New alternative supplied by the user

The user supplied [one-turn-reduction.md](one-turn-reduction.md), attributed to Claude Opus 5.5 Max, with original diagnostic scripts. Read [one-turn-proposal-audit.md](one-turn-proposal-audit.md) before invoking it. The original nine files remain preserved at the audit's provenance checkpoint.

The candidate-based weighted objective is

$$
\Psi(U)=\mathcal A(U)-W(U)/2,
\qquad\mathcal A(U)=|U|-|N(U)|.
$$

A pair of full-angle caps with nonempty two-turn fibers has exact area

$$
|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.
$$

The initial floor traces OT3–OT4 classify horizontal faces without an input curvature cap. In the aligned-long-face case, with both corner-height positivities, OT5 proves G=0. The other configurations still need analysis.

The audit strengthens the sufficient full-turn rectangle width to `q-sqrt(q^2-1)` for area greater than q. It also states the needed full-turn and nonempty-fiber qualifications, and distinguishes constrained one-turn variations from maximality against all caps.

### One-turn gates and their current status

| Gate | Required result | Status |
|---|---|---|
| O0: objective and existence | Fix the signed full-niche objective and prove its maximum is attained. | **PA2 proved in writing** in [one-turn-penalized-attainment.md](one-turn-penalized-attainment.md), without assumed Romik or Gerver optimality. |
| O1: exceptional face placement | Exclude or control OT4's end-face and short-rectangle configurations by ordinary area or a valid improvement. | Open. The R case locates at least one face, not automatically both faces at one end. |
| O2: point faces | Handle actual maximizing point-face configurations, including the SC3 obstruction. | Open. No uniform area threshold below M excludes all known examples. |
| O3: niche topology | Prove the two no-clipping hypotheses outside the common-face-length-at-least-one subcase, or bound G correctly. | Open in the remaining configurations. |
| O4: sharp weighted maximum | Prove `Psi(U)<=M/2` on the stated right-angle cap class and characterize equality. | Open. Attainment does not supply the value, curvature or arm estimates. |

OT.7's full-right-angle cap problem is full-angle by definition. A separate full-angle theorem belongs to the geometric transfer from a partial-turn body, not to existence of that already fixed-domain cap maximum.

Even a completed O4 gives only `|E|<=M+G` while G is positive. A valid assembly must also address O1–O3 or another exact correction. The new route is complementary to the two-wing program, not a proof that its global admission has been solved.

## 5. Next acceptance test

Choose one directly relevant target, record it, and pursue it to a proof or a specific obstruction before creating another auxiliary functional.

The new one-turn target is now well posed by PA2: derive the maximizing cap's finite and limiting balance conditions for `A-W/2`. Fixed-axis interior variations leave the penalty unchanged. Axis variations have an additional minus-one-half derivative. The transfer must still handle domain admissibility, approximation errors, endpoint conditions and the arm bounds needed for a sharp comparison. The existing unpenalized maximality theorem cannot be invoked with a false premise.

Alternatively, attack one of OT4's exceptional face classes with an actual two-turn area comparison. The point-face examples must be included, not dismissed as unsaturated. In the two-wing route, directly constructing the shared-bottom near-full-height wings or proving the core enclosure remains useful.

Do not spend another pass optimizing an already calibrated expression while its geometric area inequality is unproved.

## 6. Mandatory positive and negative tests

Reference data must give the correct area and orientation. A proposed global comparison must handle or exclude by a proved improvement the axis-cut and shadow-clipping families. Repair, saturation and shared anchors did not rescue the earlier failed comparisons.

For cap calculations distinguish

$$
|U|-|N(U)|\quad\text{from}\quad|U\setminus N(U)|.
$$

The difference is `|N(U) minus U|`. The imported polygon optimizer clips negative fibers and therefore optimizes the second expression; that is not the signed W-Gerver objective on arbitrary caps. Its repeated-abscissa interpolation bug is independently reproduced. The new review utility keeps all terms separate without modifying the preserved originals.

A computer-assisted theorem requires exact arithmetic or certified enclosures and complete coverage of its claimed domain. Finite samples and optimizer convergence do not suffice. In the recorded review, 2,025 rational fiber cases and 1,296 interval pairs are finite checks of the algebra/classification; the continuum statements have written proofs and qualifications. Floating-point candidate/rectangle calculations are diagnostics only.

## 7. Decision log and execution

- Established the actual inward-intersection formulation CS and the full-height arbitrary-slack theorem SQ1.
- Added the shared-bottom near-full-height theorem NH1; did not assume its height criterion for actual maximizing wings.
- Imported the user-supplied one-turn draft and all scripts with provenance hashes.
- Accepted OT1's scoped area identity and the initial floor/face classification; strengthened the rectangle full-turn criterion.
- Identified signed-versus-clipped objective mismatch, an endpoint interpolation defect, and the missing error sign for ordinary floating-point quadrature.
- Proved PA2, attainment of the signed weighted cap maximum, independently of the candidate optimum. The sharp value and its structural derivation remain open.
- Retained both approaches and their unresolved geometric comparisons. No unrestricted-completion claim.

Substantive findings, including negative results, are committed with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Existing manuscript, Lean libraries, dependencies and workflows remain unchanged. PR #3 stays draft. Counts of commits or notes do not measure proximity to closure.
