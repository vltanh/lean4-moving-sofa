# Ambidextrous sofa research — start a new session here

**Unrestricted optimality is not proved.** The current written chain proves the weighted one-turn value, the full-turn aligned positive-face class at every face length, and the left-right reflection-symmetric incoming class without a full-turn premise. The remaining asymmetric cases are not covered. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; current base: `main`.
Latest mathematical checkpoint before this handoff: `bf2133d9b71afdd9e2fc3e44be82a43ae5b82a3c`.
Always query the live tip and inspect intervening changes. Do not reset the PR to the historical paper branch.

## 1. Instructions and verification boundary

Prefer pen-and-paper proofs. Use short calculations to reject bad ideas and check explicit identities, not long optimizer campaigns. New invocations are capped at 30 seconds, preferably external five/ten-second limits. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`; keep edits under `docs/ambidextrous/`, refresh SHAs, and preserve concurrent work.

All proofs are written and self-reviewed, not independently refereed or kernel-verified. In particular the long weighted-value dependency chain has not been independently audited. The latest review is [short-face-extension-review.md](short-face-extension-review.md); the later UC/RS/RA notes each give their own exact scope. For weighted dependencies read [weighted-value-proof-review.md](weighted-value-proof-review.md).

The reference area is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

An upper bound on one attained global ambidextrous maximizer suffices for the optimal value. Do not add equality classification as a prerequisite or supply weighted-cap maximality to an arbitrary two-turn body.

## 2. What the latest hand proofs cover

### FAS: all full-turn aligned positive faces

[full-turn-aligned-short-faces.md](full-turn-aligned-short-faces.md) proves |S|<=M for both full conventional turns and identical top/bottom exposed hull faces of any positive length T. No curvature, smoothness, symmetry, minimum positive T or endpoint-height premise is used.

The argument uses actual retained face endpoints to bound the two flank widths on `(0,2 arctan T)`. If T<=2-sqrt(3), those tests force W<=2. Otherwise pi/6 is available and bounds each flank by sqrt(3)/2. Failure of either explicit SCG clipping test then forces

$$W\le T+\cos(2\arctan T)+\sqrt3/2<1201/600.$$

An exact polynomial sum-of-nonnegative-terms identity proves that bound. [SW1](scaled-width-margin.md), a uniform-scaling corollary of analytic AW-W, already excludes every W<=1001/500>1201/600. Thus both clipping tests hold, both niches lie between the common face endpoints, and the two WV2 inequalities add.

This removes the old T>=1 restriction for the already-full-turn class. It does not silently complete arbitrary partial turns.

### SCG/CSF: short-face conditions that force full turns too

[SCG1](short-chord-optimality.md) uses four actual points `(a,0),(a,1),(b,0),(b,1)` plus the two actual extreme points `(l,y_L),(r,y_R)`. With T=b-a, R=r-a, B=b-l, m_i=min(y_i,1-y_i), it requires R,B>1 and

$$2TR+m_R(1-T^2)>1+T^2,\qquad2TB+m_L(1-T^2)>1+T^2.$$

A concave trigonometric strip estimate forces both full turns; the retained points then force the two niches between a and b. Hull membership of the rectangle alone is not sufficient: its four corners must be retained.

[CSF1](central-short-face-optimality.md) derives these inequalities in stated central-face width/height regimes. Examples are W>1+sqrt(2) with arbitrary extreme heights, W>7/3 with extremes in [1/4,3/4], and W>sqrt(5) with mid-height extremes, provided both faces span `[l+1,r-1]`. It proves right-endpoint retention only after alignment, not before.

A verified feasible ellipse construction has width 23/10 and common face length 9/10. The initial W=12/5,T=2/5 parameter illustration was not a feasible realization and was replaced in both notes. The review records the correction and a hull-only retention counterexample.

### UC: a central point face is impossible under full turns

[UC1](full-turn-unit-chord-obstruction.md) says a retained pair `(a,0),(a,1)` cannot have actual points at horizontal distances greater than one on both sides if both supporting quarters are available. The two safe-angle sets form a closed cover and must intersect for each motion. The resulting half-angle parameters r,s would have to satisfy both r+s>1 and r+s+3rs<1. This contradiction uses no area constant or weighted theorem.

UC2 uses floor traces to conclude that every point face of a full-turn body with W>2 has abscissa in one of the unit end intervals `[l,l+1]` or `[r-1,r]`. The central point-face possibility is excluded.

### RS: left-right symmetric bodies

[RS2](reflection-symmetric-optimality.md) proves |S|<=M for bodies symmetric about a line perpendicular to their common incoming strip, without assuming that their motions are full or symmetric.

For J(x,y)=(-x,y), reflection exchanges the two normals of a lower supporting hallway at t with those at pi/2-t. A conventional turn reaching past pi/4 therefore supplies the whole quarter for the same symmetric body. The earlier elementary area/angle reduction supplies that initial coverage for a putative counterexample. The upper motion follows independently.

The two horizontal faces are centered. UC forbids a central point face at W>2, and FD's opposite-end positive-face alternatives cannot be centered. Thus the faces are identical and positive, and FAS applies. This closes the stated reflection-symmetric class, not the unrestricted existence of a symmetric optimizer.

## 3. The exact remainder

[FD1](full-turn-face-dichotomy.md) classifies two nondegenerate full-turn faces at W>2: they coincide and span `[l+1,r-1]`, or lie in opposite unit end strips. FAS handles the first case, and UC narrows the point-face case.

An unresolved full-turn counterexample must therefore have either an end-strip point face or two nondegenerate faces in opposite end strips. It must break the left-right symmetry covered by RS. General asymmetric partial-turn bodies not covered by SCG/CSF remain a separate angular/area obligation.

For general full-turn cap pairs with nonempty fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

WV2 makes Delta(U)=M/2-Psi(U) nonnegative; the still-unproved sharp comparison is G<=Delta(U)+Delta(V), or another actual-area bound. None of the new class results makes the symmetric weighted-maximizer body dominate all competitors.

## 4. Do not retry these shortcuts

FD3 rules out an aligned point-face limit of aligned positive-face, full-turn unit-span hulls with widths tending to W>2: the common face lengths are at least W_j-2 and stay positive in the limit. Adding a tiny horizontal segment at fixed height is not a feasible approximation. Shrinking first changes vertical span; a restoration requires proof.

[RA1](reflection-averaging-obstruction.md) proves naive Minkowski averaging of actual bodies with their left-right reflection is not feasible even on the reference. The reference is already symmetric but nonconvex. Its self-average adds the central top/bottom midpoints, retains the same hull and width>2, and contradicts UC after reflection completes the turns. This does not disprove a different cap- or motion-level symmetrization with its own area proof.

Earlier negative controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain relevant. Repair, saturation, data admission or proximity alone did not justify those universal enclosures. Canonical-wing accounting keeps negative winding and uncovered material. Small extreme-height difference is not mid-height or C1 proximity. Point-face examples approach M, so a uniform strict gap on their entire class is not available.

## 5. Weighted and global infrastructure

[WV2](one-turn-weighted-value.md) proves `sup Psi=M/2` on normalized full-right-angle caps, subtracting the whole niche. PA/WP/WR give attainment, selection and regularity; AR/PT/TS/EB give same-sign inequalities, a positive top face, half-height niche and exact limiting exposure. TF/HF give confinement, T=W/2 and a stationary core. CG/SE force one good quarter; VE's actual visible-source lower bound and WV's energy contradiction force the other good. AR4/SR1/AF3 then compute the value.

The main new historical review point remains VE's limiting source-flux argument. SE invokes the established ordinary Gerver area theorem on a feasible one-turn body and six pinned constant enclosures. No source was compiled in this work. The assumed saturated ODE is not a premise of WV2.

AW-W is the analytic width<=2 exclusion. SW1 now strengthens the competitive lower restriction to W>1001/500; AL1 gives W<=2999/1020. AM2 and TE1 retain scoped computer-assisted exclusions, not a complete sharp covering. The latest FAS/UC/RS proofs do not depend on TE's or AM's large certificates. General normalization and attainment remain earlier written dependencies.

Original uploaded packages and author diagnostics remain preserved at their audited provenance checkpoints. The unconditioned occupancy LP's fractional barriers still preclude merely refining the old model. No long search is authorized by the present instruction.

## 6. Short checks actually executed

The standard-library script `computer-assisted/check_short_face_extension.py` checks the complete FAS polynomial coefficient by coefficient, plus 1,805 rational strip tests, 985 flank tests, 27 central-threshold cases and 6,084 interval pairs. It ran in about 0.03 seconds under a five-second cap. Its source blob is `65ab585aa3c29f5596f00bd2569c7103c1030529`; the committed record and a fresh replay agree.

The separate `check_unit_chord.py` checks 1,521 rational switching pairs and 82 strict-flank boundary frames, in about 0.028 seconds under a five-second cap. Its source blob is `ccaf007fa865dd97f1dea08140f73da273154839`. The matching JSON records source hashes and scope. Neither script verifies the continuum proof or the weighted chain.

## 7. Restart priorities

Read the current [ROADMAP.md](ROADMAP.md), FAS, UC and RS. The remaining task is a specified asymmetric end-face area comparison, a legitimate symmetry reduction, or an uncovered partial-turn case. RA shows why the simplest averaging reduction is false; do not silently assume symmetry of an optimizer.

A result on one attained unrestricted maximizer suffices for the value. Keep all motion hypotheses, actual retained points and positive corrections visible. Commit negative findings as well as theorems. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. PR #3 stays open and draft while unrestricted optimality remains unproved.
