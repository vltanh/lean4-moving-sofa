# Ambidextrous sofa research — start a new session here

**Neither unrestricted frontier is closed.** The full-turn upper bound still lacks a comparison covering arbitrary competitors. The partial-turn problem still lacks completion or a sharp area bound when its strip bridge is unsafe. New work constructs tail backgrounds on a testable subclass, supplies finite strip-completion criteria, and proves a direct spatial-partition enclosure whose sharp maximum is unproved. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; base: `main`.
Substantive checkpoint before this update: `eef8882b0130fc5e95fe9512f1ee664c49b855c3`.
Always query the live tip and inspect later changes. Do not reset to the historical paper branch.

## Full-turn-only checkpoint after the latest continuation

**The full-turn optimality theorem is still open.** Work was deliberately restricted to that problem; partial-turn SI/FS remains frozen for now. New proof material:

- [CGA](full-turn-common-background-obstruction.md) gives a completely explicit convex full-turn parallelogram, with actual top and bottom positive faces on opposite ends, whose **canonical saturation equals the body**. The width is \(49/20\) and area \(1/20\). Any height-one cap with full niche height at most one half has top-face length at most \(2\sqrt2-1\) (a single \(45^\circ\) corner test). Hence no pair of containing backgrounds with one common top face can contain the two original caps. This disproves **unconditional** common-face-background admission, even on the saturated positive opposite-face class. The low area is essential: it does not disprove competitive-only admission. A continuum of such examples exists for diagonal rod width \(2<W<\sqrt7\).
- [AS](adaptive-spatial-switching-bound.md) strengthens the direct SPB ordinary-area relaxation without an arbitrary spatial partition:
  \[
  |S|\le\mathscr C(U,V)=W-\int_I\max(n_U+n_V,\ 2-A_U-A_V).
  \]
  Its exact error against the canonical envelope is \(\int[a_++b_+-(a+b)_+]\), with \(a=n_U-(1-A_V)\), \(b=n_V-(1-A_U)\). It is exact on the reference, every convex feasible full-turn body, and vertically symmetric feasible envelopes. For admitted common-face tail-budget domains, existing per-cap deficit inequalities prove even \(\mathscr C\le M\). **The sharp bound \(\mathscr C\le M\) for arbitrary compatible full-turn caps is unproved** and is stronger than the necessary original clipping inequality.
- The bounded [exact checker](computer-assisted/check_full_turn_focus.py) passed 6,561 rational frames per turn and 10,000 exact switching identities, rejecting an overwide parallelogram and a false zero-switching-error assertion. Its executed bytes match Git blob \(ee4843d19f357b315050f84f7f036d568cb61edc\). The finite tests do not verify the continuum theorem or establish sharp area optimality.

**Single remaining active acceptance criterion:** prove the sharp ordinary-area upper bound for every saturated full-turn positive opposite-end-face body. A competitive-only regular-background theorem remains possible, provided it supplies face compatibility and pays all geometry; generic inclusion-based admission is false. An alternative is a direct sharp **coupled** inequality using AS or the exact fibers; do not treat the stronger AS scalar maximum as already established. Do not resume partial turns until the full-turn step closes or a specific flaw forces a rethink.

## 1. Instructions and validation limits

Prioritize pen-and-paper proofs. Short computations may test a proposed inequality or reject an approach; at most 30 seconds per invocation, preferably external five/ten-second limits. Do not launch a large optimizer campaign or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`, under docs/ambidextrous. Refresh blob SHAs and preserve concurrent edits.

All proofs are written and self-reviewed, not independently refereed or kernel-verified. Read [constructed-background-review.md](constructed-background-review.md) and [spatial-half-partition-bound.md](spatial-half-partition-bound.md) for the latest results and exploratory scope. The historical chains have not been independently verified by the new checks.

The reference value is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

An upper bound for one attained unrestricted maximizer suffices for the value. Do not silently assume attainment inside a nonclosed restricted subclass or assign weighted-cap maximality to an arbitrary two-turn cap.

## 2. New constructive tail admission, with its remaining assumptions

[CB](complementary-tail-background.md) starts from an actual input cap U, not an assumed regular background. It requires:

- height one, width W>2, a half-height rectangle and full niche height at most one half;
- curvature at most one outside two sufficiently narrow top-normal tails;
- differentiability without atoms at the two outer cut normals;
- a displayed half-curvature support arc that dominates the input on each tail and matches its outer-end value and derivative.

The last smooth-fit barrier is essential to avoid creating an unallowed middle curvature atom. It is not implied merely by proximity to the reference.

On each tail, a projective lower convex envelope produces a majorant B with tail density at most one half. If e=h_B-h_U, then

$$e\ge0,\qquad e(2\rho_B-1)=0.$$

Where repair occurs, rho_B is exactly one half. Where it is smaller, e=0. The CT surplus is therefore exactly zero; HC's adverse-density example is not contradicted because its preselected background was not this input-dependent obstacle solution.

The construction preserves axis supports and glues without new non-axis atoms. Unit middle curvature, a positive top face, the required tail contact signs, separated tail abscissae and a half-height niche follow from the explicit input bounds. CB proves

$$\Psi(B)-\Psi(U)\ge\int_a^b(1-A_U)dx,$$

where [a,b] is B's top face. For two such constructed backgrounds with identical top-face intervals, the two budgets pay clipping and yield actual envelope area at most M through SR/AF.

**Not proved:** arbitrary competitors satisfy the input hypotheses; independently constructed output faces match; or partial witnesses enclose the body in the full envelope. The regular middle and half-height assumptions remain substantial. CB is constructive conditional admission, not global admission.

## 3. New finite criterion for the partial-turn bridge

[FS](finite-strip-bridge-criterion.md) bounds widths between two normals a,b by positive sine interpolation of their actual width bounds A,B. For c=cos(b-a), s=sin(b-a)>0 and A,B<=1, a sufficient and exhaustive test for that upper envelope to stay at most one is

$$B\le Ac\quad\text{or}\quad A\le Bc\quad\text{or}\quad A^2+B^2-2cAB\le s^2.$$

When the normals and bounds are rational this is an exact rational test. A finite chain passing the test certifies every width in the SI bridge, giving continuous full turns for the same body and preserving area.

A single sufficiently thin intermediate strip suffices:

$$w((\alpha+\pi-\gamma)/2)\le\cos((\pi-\alpha-\gamma)/2).$$

This is a hypothesis, not a result about every maximizer. Failure of this sufficient test does not prove the bridge unsafe. For instance constant width-one data fail every nonzero two-strip interpolation test despite all actual strips being safe. Refinement alone is not a completeness argument. The competitive unsafe-width-bump case remains open.

## 4. A direct spatial alternative with the area linkage already proved

[SPB](spatial-half-partition-bound.md) uses the actual two caps and the niche roofs from their actually visited angular intervals. For I=[l,r], W=r-l and J=[l+W/4,r-W/4], put

$$\mathcal P_J(U)=\int_{I\setminus J}A_U-\int_J n_U.$$

For the actual nonempty-fiber canonical envelope,

$$|S|\le|E|\le\mathcal P_J(U)+\mathcal P_J(V).$$

The exact nonnegative slack is written in SPB.4. On J it discards outer-wall restrictions; off J it discards niche restrictions. There is no hidden clipping or winding correction. The bound is exact at the reference.

**The sharp maximum of P_J is not proved.** For full niches,

$$\mathcal P_J(U)=\Psi(U)+\int_J(1-A_U)+\int_{I\setminus J}n_U,$$

so WV2 does not bound it by M/2. Proving that stronger scalar bound, or a compatible-pair bound on the sum, would close the full-turn value directly without CB admission. This is an alternative direction, not a new completed gate.

For partial turns the enclosure still uses only visited niches. Replacing them by the larger full niches lowers the alleged upper bound and is forbidden without completion. Original outgoing-strip constraints still couple the two hull caps.

The retained short tests found no convincing violation, but the reference discretization itself has a positive bias about 0.000240. A fixed six-iteration numerical run exhausted its budget with a value far below the reference. Neither observation proves a maximum, feasibility of arbitrary proposed pairs or a global certificate. Do not advertise this as a solved replacement for the background route.

## 5. Actual-body variation: a positive necessary result and a negative control

[PV](actual-maximizer-parallel-volume.md) shows `(S+tC)/(1+t)` preserves all existing motions and endpoint strips when C is convex of diameter at most one. Thus every attained unrestricted or full-turn maximizer satisfies

$$|S+tC|\le(1+t)^2|S|.$$

For the unit disk D, `|S+rD|<=(1+2r)^2|S|`. Testing compactly supported deformations and expanding the planar determinant gives finite distributional perimeter with

$$P(S)\le4|S|.$$

This is actual-body regularity, not a hull curvature bound or a sufficient maximum condition.

[RT](convex-template-rounding-obstruction.md) proves from the explicit reference arcs that `4M-P(Sigma)>92/2625`. Its even normal measure then makes every diameter-one convex template lose area to first order, with coefficient less than `-46/2625`. The same negativity persists on sufficiently small asymmetric double-tip cuts. Those cuts are suboptimal, so the whole variation family cannot automatically improve the remaining near-reference examples. No uniform finite step size or exclusion of all larger finite steps is asserted.

## 6. Prior comparison domains and theorem dependencies

**MT/ME:** variable regular middle supports with three exact reference collars, half-height geometry and signed rough-tail changes. Their face-loss budget pays clipping while the background middle retains a deficit `(7/50) sum integral |z_i'|^2`.

**CT:** inward changes of general unit-curvature backgrounds with a common top face and projection, half-height geometry, tail signs and tail density at least one half. The surplus is integral e(2rho-1). CB replaces the lower-density assumption by complementarity on its constructed domain; it does not invalidate CT or make all tails admissible.

**HC:** a density-one-quarter stadium has an inward support cut increasing its signed and symmetric actual area. This disproves unqualified CT monotonicity. The cap is not above M.

**TC/RB/STW:** earlier reference-middle tail pairing, the 1/101 boundary-layer saturation theorem and a signed outward extension remain valid stated subcases.

**WV2:** the signed weighted one-turn value M/2 is proved in the existing written PA/WP/WR/AR/PT/TS/EB/TF/HF/CG/SE/VE/WV/SR/AF chain. VE's continuum source-flux limit remains a principal independent-review point. SE invokes Gerver's bound on a feasible one-turn body. The newer tail-transfer route invokes SR/AF on admitted regular backgrounds instead, without requiring weighted-maximizer regularity of the input.

## 7. Global reductions do not supply admission

RR/PD/PS establish that the full-turn supremum equals that over saturated positive opposite-end-face bodies, allowing area-convergent approximation and changed incoming orientation. The reference has such approximants approaching M. There is no uniform strict area gap on the whole remaining class, and that subclass need not attain its supremum.

SI completes partial turns across an entire safe-strip bridge. Three isolated safe normals do not suffice; the new FS tests are sufficient finite criteria for that bridge, not a universal completion theorem. RR preserves its unshaved safe-strip set.

FAS covers full-turn aligned positive faces. SCG/CSF provide further retained-point completion tests. RS covers left-right reflection symmetry in a valid incoming representation, not existence of an unrestricted symmetric maximizer.

AW-W/SW/AL are analytic competitive-width restrictions. AM/TE are earlier restricted exact computer certificates, not a sharp global covering or premises of the new CB/FS/PV/RT proofs.

## 8. Negative controls and numerical provenance

Retain RA, MCA, AF4, GR1, AX1/SAT1, SAC2, SC3, TR1, AO1, FF and HC. Body averaging, cap averaging, hull repair, saturation and face filling did not automatically preserve actual-area bounds. Any new averaging assertion must state a domain that avoids the existing counterexamples. The old occupancy LP has fractional barriers that resolution does not remove.

The latest standard-library checker ran under a five-second limit in about 0.0216 seconds. It has 44 check calls, some repeated, and its record matches Git blob `41d3aaef44a80b656f39b5bcb3aee2d24d79c9dd`. These checks do not verify continuum admission or the historical chain.

All exploratory runs were bounded by five seconds and retained as noncertifying diagnostics. Some regular-cap pair tests had negative fibers and are not feasible two-turn examples. Small apparent positive area errors on the discretized reference are bias, not counterexamples. The two initial spatial-script helper-name errors produced no result and were corrected before its retained run.

Original user packages and author records remain preserved at their audited checkpoints. Do not overwrite them with fresh results or treat imported claimed checks as newly executed verification.

## 9. Restart boundary

Read the live tip, this handoff, the roadmap and current review. The choices are a specific remaining CB input/face-compatibility proof, a sharp direct spatial inequality with its actual-body linkage retained, or a partial-turn theorem that supplies the missing bridge or an area bound without it. None is already proved globally.

Do not turn these choices into simultaneous indefinite searches or an assumption of imminent closure. State and repair any actual gap before using a historical result. Keep scripts short, commits substantive, all positive corrections visible, and PR #3 open/draft until the unrestricted upper value really is proved.
