# Review boundary: weighted one-turn value and long-face ordinary-area theorem

**The unrestricted ambidextrous optimal value remains unproved.** The new written chain does establish the signed weighted cap value and an ordinary-area bound for the class with two horizontal faces longer than one. This review separates those conclusions, their proof dependencies, the abandoned all-angle-wing shortcut, and the short computations actually executed.

Baseline: `942c3b85553843c6d7d4ced926c1e73e31394989`. All new work is under docs/ambidextrous. The arguments are self-reviewed, not independently refereed or Lean-verified.

## 1. The completed weighted subproblem

[WV2](one-turn-weighted-value.md) states

$$\sup_U\{|U|-|N(U)|-W(U)/2\}=M/2$$

on the PA.1 full-right-angle cap domain, with the whole niche subtracted. The proof does not assume universal ordinary-area enclosure by an auxiliary support functional. It first proves that an attained weighted maximizer has both curvature densities at most one, then invokes the existing signed-roof and calibration chain on that admitted maximizer.

The new steps are:

1. [CG1](one-turn-curvature-guard.md): a right endpoint arm at most sqrt(17)/2 suffices for the first-quarter curvature bound, and reflection gives the other quarter. The exact energy is `(p-1/2)^2+(q+1)^2`, whose derivative on the initial same-sign regime is `2(q+1)(v-1/2)<=0`.
2. [SE2](one-turn-single-excess-quarter.md): at least one arm satisfies that threshold. HF's core has width T, height one half and upper arc length 2 Psi. The two chords give `2 Psi>=sqrt(T^2+1)`. The actual one-turn body U minus N has area Psi+T, bounded by Gerver's area. The six pinned reference enclosures give G<=22199/10000; therefore T<48/35 and one arm is less than 72/35<sqrt(17)/2.
3. [VE2](one-turn-visible-exposure-bound.md): with the second quarter globally good and the first quarter good on the whole future of an interval, two source pieces are globally visible on its standard-sign regime. Their limiting second-wall contributions add to `(1-v)-p`.
4. [WV1](one-turn-weighted-value.md): a hypothetical first-quarter excess occurs before q decreases through one. After that crossing, all future first-quarter curvature is at most one. VE applies until q reaches zero, forces `v=(1-p)/2` and p>=-1, and makes `(1-p)^2+(1+q)^2` nondecreasing. That quantity starts above five and must end at most five. The contradiction removes the excess.

This is not the formerly proposed saturated-ODE route. SP1 is not needed to compute the maximizing profile in this chain. The existing AR4/SR1/AF3 argument supplies the value after WV1 proves its curvature hypotheses.

## 2. The new source-flux argument: points to review carefully

VE is the principal new continuum argument, and deserves independent scrutiny beyond the short arithmetic tests.

- The second-wall tangency is globally active because v<=1 makes D_x nondecreasing throughout the entire quarter. The strict q>0 companion gap makes its source type unambiguous.
- The standard corner is globally active because every past second wall is strictly lower and every future first wall is strictly lower. This uses a globally good second quarter and a good *entire future* first quarter. Merely local curvature bounds would not suffice.
- Tangency and corner images on a compact parameter interval are separated in x. Their exposure contributions are not counted twice.
- Positive height keeps all finite active angles uniformly away from both axes. Uniform support convergence and dense meshes then give local uniform roof convergence and a uniform slope bound.
- A unique limiting maximizing parameter forces finite source angles to localize. For a tangency, plateau image points are countable and contribute no limiting tangency arc length; removing arbitrarily small x-neighborhoods loses uniformly bounded finite exposure.
- The preserved quantity is oriented tangent flux, not ordinary perimeter. Increasing-x first-wall edges have tangent `-nu_t`, while second-wall edges have tangent `mu_t`. Resolving the limiting vector flux gives the two source weights q and -p on a standard corner, and 0 and 1-v on a second-wall tangency.
- The actual finite source-angle measures converge to u dt,v dt by the separate EB theorem. Positivity of all other exposures then gives the lower bound, rather than assuming that actual exposure attains a local upper bound.

No C2 support, continuous curvature density, stable finite global contact partition, or differentiability formula for the infinite-angle niche is inserted here. VE supplies details of graph convergence and the plateau exceptions instead.

## 3. External and historical dependencies

SE invokes the established ordinary moving-sofa upper bound of Gerver's area. This applies because PT/TS make U minus N a compact connected feasible one-turn body. It does not assume that U is an unpenalized maximizer.

The rational upper constant comes from the six named enclosures in `MovingSofaOptimality/Gerver/AreaBounds.lean`, pinned to baseline blob `2bfae7fc6cd56c35793f18843cc91ed6e1462aa2`. The correct combination is A+C+segment-x+B+D, giving 22199/10000. The area formula and reference-parameter hypotheses remain part of the existing Gerver proof chain. No source file was compiled in this continuation.

The older PA, WP, WR, AR, PT, TS, EB, TF, HF, SR and AF proofs are also dependencies. The new result is not independent verification of every one of those notes. The compact roadmap in WV Section 6 lists the logical order and avoids circular use of the desired ambidextrous result.

## 4. The payoff for actual ambidextrous area

[FL1](aligned-face-optimality.md) bounds ordinary area by M for a compact connected ambidextrous body whose top and bottom hull faces are the same interval of length at least one. Its contained unit square forces full turns. The positive niche triangles form a connected horizontal interval, and retained face endpoints prevent that interval escaping the common face. Thus clipping is zero and the two universal WV2 bounds add.

[LF1](long-faces-force-alignment.md) removes the need to assume alignment when both face lengths are strictly greater than one. Initial floor traces force the left endpoints to agree; a contained unit square then forces full turns; final floor traces force the right endpoints to agree. This is an application of the earlier floor-trace method, not a novelty claim for that classification.

Consequently a possible counterexample of area greater than M must have at least one horizontal face of length at most one. Nothing here excludes that remaining class. Known near-candidate point-face examples forbid a uniform area-gap claim for it.

## 5. A useful bridge and a rejected substitution

[MW1](weighted-maximizer-canonical-wings.md) places the truncated canonical wings of the symmetric weighted-maximizer construction in the full-height SQ1 domain, with complete outward-support agreement. The initial draft mistakenly described those truncated pieces as surviving every angle; the next commit removes that wording. Only the all-angle variant MW2 has that survival conclusion. The corrected statement is the version used in the later notes.

[AO1](all-angle-wing-reference-obstruction.md) shows why the all-angle variant does not immediately give the old core-area comparison. On the actual reference, its extra horizontal safe-wall constraint removes a triangle of area `(1-cos(beta))^2/(sin(beta)cos(beta))` from each wing while leaving the old connector data unchanged. Hence its old functional value is strictly below M even on the candidate. This is an exact hand-proof obstruction, not an optimizer failure.

The successful weighted proof does not use that invalid enclosure. MW/AO remain documented positive admission data and a negative control, respectively.

## 6. Short checks and discovery only

The standard-library [check_core_arm_reduction.py](computer-assisted/check_core_arm_reduction.py) ran under an external five-second limit. Its recorded internal time was about 0.0021 seconds. It passed 19 named checks, comprising rational constants and 48 initial-energy, six triangle, 36 corner-flux, 16 tangent-flux and 36 final-energy regressions, with three sign/threshold controls.

The [record](computer-assisted/core-arm-checks.json) contains versions and hashes. The executed source matches Git blob `9f7b4170304b8409d8819f9941e47c54c9e20a67` and SHA-256 `15b3a504c1849b5164fcf77a2580f4dbc4132f18a7627b592ed38b78e6d87dc0`. These checks do not verify VE's limiting argument, the historical dependency chain, Gerver's theorem or unrestricted optimality.

Two bounded exploratory diagnostics were also performed and are preserved in the session bundle:

- A 240-by-100 point grid with 61 angles tested six retained point witnesses on nine prescribed core shapes. The candidate-width trial returned a sampled value about 1.93458, too weak to prove optimality. Some other anchor sets were numerically incompatible. None of these finite-grid values has a certified error sign. The fresh retained run took about 0.164 seconds under a five-second limit.
- A polygon diagnostic compared truncated and all-angle wings on the reference and horizontal scale factors 0.9 and 1.05. It took about 1.505 seconds under a ten-second limit. Its all-angle reference undercount motivated AO1's exact triangle proof. The non-reference outputs remain diagnostics, not cap realizations or continuum certificates.

A tiny evaluation of the reference corner height was also exploratory only. No long search, optimizer campaign or refinement loop was run. The proof of WV is analytic rather than inferred from these tests.

## 7. Handoff boundary

The weighted value and the two-long-face class are now closed in the written proof chain. The next unresolved ordinary-area target is the remaining short-face class, with actual terminal-angle coverage and clipping retained. Do not reopen weighted maximization or the already rejected no-hiding inference as if they were the remaining gate.

No theorem here says every ambidextrous maximizer has two long faces, is symmetric, or is dominated by the symmetric weighted-maximizer body. That missing global comparison must be proved rather than inferred from the newly solved auxiliary problem.

All substantive findings and corrections were committed with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. PR #3 remains open and draft; independent review and unrestricted optimality remain unfinished.
