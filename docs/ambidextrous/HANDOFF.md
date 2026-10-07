# Ambidextrous sofa research — start a new session here

**Unrestricted optimality is not proved.** The latest result reduces the entire full-turn supremum to canonically saturated bodies with two positive horizontal faces in opposite unit end strips. It does not bound that supremum. In particular this remaining class has reference-area limits, so a uniform strict gap below the reference is impossible. Unrestricted uniqueness is deferred.

Repository: `vltanh/lean4-moving-sofa`.
Branch: `research/ambidextrous-pen-and-paper`.
Draft PR: #3; current base: `main`.
Latest substantive checkpoint before this handoff: `306e9a924787c320617eb0f7d82c86279e057bcc`.
Always query the live tip and inspect intervening changes. Do not reset the PR to the historical paper branch.

## 1. Instructions and verification boundary

Prefer pen-and-paper proofs. Use short calculations to reject faulty premises and check explicit identities. New script invocations are capped at 30 seconds, preferably external five/ten-second limits. No long optimizer campaign or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive positive and negative findings with `[skip ci]`; keep work under `docs/ambidextrous/`, refresh SHAs and preserve concurrent edits.

All proofs are written and self-reviewed, not independently refereed or kernel-verified. The long weighted-value dependency chain has not been independently audited. Read [positive-face-density-review.md](positive-face-density-review.md) for the newest reduction, [short-face-extension-review.md](short-face-extension-review.md) for the case bounds, and [weighted-value-proof-review.md](weighted-value-proof-review.md) for the weighted theorem's dependencies.

The reference area is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

An upper bound on an attained unrestricted maximizer suffices for the value, but the new positive-face subclass need not itself attain its supremum. Do not silently assume a maximizing member exists in that nonclosed subclass.

## 2. Latest reduction: point faces no longer need a separate full-turn value theorem

Read [rounded-strip-regularization.md](rounded-strip-regularization.md), [full-turn-positive-face-density.md](full-turn-positive-face-density.md), and PS1 in the new review.

### RR: preserve the actual motions while rounding and shaving

For 0<lambda<1, let r=(1-lambda)/2 and

$$R_\lambda=\lambda S+rB,$$

where B is the closed unit disk. If an actual point s satisfies one canonical inner-wall depth bound, every point lambda s+r z above it has depth at most lambda+2r=1 in that same wall direction. Thus R_lambda preserves every previously feasible canonical hallway of either handedness. Its width is

$$w_{R_\lambda}=\lambda w_S+1-\lambda,$$

so its safe-strip set is exactly the old one. Rounding does not create a missing strip bridge.

Shave epsilon<r off two opposite supporting planes. Every center lambda s survives the slab. The shaved body is a union of convex disk portions each attached to the connected center set lambda S, hence is connected. At both support extremes, actual disks supply positive-length face chords. Do not replace this argument by the false statement that arbitrary strip clipping preserves connectedness.

### PD: choose the normal and recover full turns in that orientation

At a boundary of the safe-strip component, take a record excursion of width just above one. A semiconvexity estimate gives a short interval of strictly increasing width. Uniform convergence of clipped convex widths preserves a strictly positive left derivative there; a separate record-width gap controls the rest of the bridge.

After shaving sufficiently little and shrinking by the reciprocal of the attained slab width, the whole interval of intermediate strip directions is safe. SI2 transports both full turns to the new incoming normal. The two new positive face segments are strictly separated because the left derivative of width is positive. The two shrinking factors tend to one, and the retained inner copies plus shrinking outer neighborhoods prove area convergence.

**PD2:** every compact connected full-turn body of area greater than one has full-turn unit-span approximants with two positive strictly separated faces and areas tending to its area from below. No reference optimality assumption is used.

For competitive areas, AW-W forces their widths above two and FD1 puts the two faces in opposite unit end strips. Therefore **PD3** gives

$$\boxed{\sup_{\rm full\ turns}|S|=\sup_{\rm positive\ opposite\ faces}|S|.}$$

A full-turn counterexample above M would produce one in the positive opposite-face class. This covers point-face limits without trying to preserve their old hull or old incoming orientation.

### PS: saturation is allowed too

PS1 in [the review](positive-face-density-review.md) proves that each approximant may be replaced by its full same-hull canonical envelope. Its vertical fibers are nonempty intervals, giving connectedness. The hull and face geometry are unchanged, and area can only increase. Consequently the same supremum is obtained on **canonically saturated positive opposite-face bodies**.

If the original body is an actual full-turn maximizer, those saturated approximants converge to its area. For the reference alone, saturation gives only a lower-limit bound at least M; do not claim their areas stay below M without proving optimality.

### Negative conclusion that changes how to judge progress

Apply the from-below construction to the reference itself. It gives actual bodies with two positive opposite-end faces and areas strictly below M tending to M. Thus neither excluding literal point faces nor adding canonical saturation makes the remainder uniformly suboptimal.

A proof of `area <= M-epsilon` with fixed epsilon>0 on the whole remaining positive-face class is impossible. The class carries the entire full-turn supremum. It is not a small exceptional region whose sharpness can be ignored. This reduction streamlines the target but supplies no new sharp upper bound and no rate to closure.

It also does not prove that a full-turn maximizer can be chosen inside the positive-face class. Approximating face lengths can tend to zero. A local improvement theorem restricted to attained positive-face maxima would therefore not by itself finish the value.

## 3. Partial turns: the safe-strip bridge is still a genuine hypothesis

[SI3--SI4](strip-interval-completion.md) transport the same partial-turn body to full turns if every strip direction between its outgoing normals has width at most one. SI2 transports already full turns along any connected safe-strip interval. These are actual continuous motions, not unrelated hallway placements.

An uncovered partial-turn body must have a width bump above one on the required bridge. Three individual safe strip directions do not certify the intervening interval. RR preserves known motion intervals and its unshaved safe-strip set; PD needs full turns already. None of the new results removes that width-bump obstruction.

Thus there are two remaining upper-value obligations: the sharp bound on saturated positive opposite-end full-turn bodies, and an upper comparison or full-turn reduction for the remaining partial-turn bodies.

## 4. Written results retained

**WV2, weighted value.** On normalized full-right-angle caps,

$$\sup_U\Psi(U)=M/2,\qquad\Psi(U)=|U|-|N(U)|-W(U)/2,$$

with the entire positive niche subtracted. PA/WP/WR give attainment, selection and regularity; AR/PT/TS/EB give same-sign bounds, a positive top face, niche height at most one half and exact limiting exposure. TF/HF supply confinement, T=W/2 and a stationary core. CG/SE force one good quarter using the ordinary Gerver bound on an actual feasible one-turn body; VE's visible-source lower bound and WV's energy contradiction force the other quarter good. SR1/AF3 then give the value. VE's source-flux limit remains a principal independent-review point; it does not pass ordinary perimeter or assume maximal local exposure.

**FAS1, aligned positive faces.** Every full-turn unit-span body with identical positive top and bottom faces has area at most M, with no positive-length threshold or curvature/symmetry premise. SCG/CSF provide additional hand criteria forcing full turns themselves. FL/LF cover long faces without a full-turn assumption. Their dependencies include the written WV and analytic AW-W chains.

**FD/UC, face restrictions.** At width greater than two, full-turn positive faces are aligned or in opposite unit end strips. A point face must lie in an end strip: the switching argument forbids a central retained vertical unit chord with actual flanks longer than one on both sides. PD does not contradict FD3, which prohibited aligned positive-face approximants; PD's approximants are separated and reoriented.

**RS2, reflection-symmetric class.** Left-right symmetry in the specified common incoming representation supplies complementary hallway angles. The centered faces then fall into the aligned class, giving area at most M without assuming symmetric or full original motions. This is not a theorem that an unrestricted symmetric maximizer exists.

**Existing global restrictions.** AW-W and its scaling corollary SW1 give competitive width >1001/500; AL1 gives width <=2999/1020. AM2 and TE1 retain scoped exact computer certificates, including a terminal-angle bound beyond sixty degrees. They are not a complete global covering or premises of RR/PD's geometric approximation.

## 5. The exact remaining area comparison and failed shortcuts

For actual full-turn cap pairs with nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

WV2 makes Delta(U)=M/2-Psi(U) nonnegative. The target `G<=Delta(U)+Delta(V)` is still unproved outside admitted classes. Weighted-cap maximality must not be supplied to an arbitrary two-turn cap. Empty fibers, if working beyond same-hull connected envelopes, need their separate correction.

RA1 rules out naive reflection averaging of actual bodies. [MCA1](convex-cap-averaging-obstruction.md) also rules out the corresponding convex-cap averaging enclosure: a feasible double-cut reference family loses only order tau^(3/2) in actual area, while its averaged cap loses first-order weighted value. The new RR operation pays for rounding by shrinking and does not claim finite-step area improvement.

Earlier negative controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain in force. Repair, saturation, data admission and proximity alone did not prove ordinary-area enclosure. Canonical-wing accounting retains negative winding and uncovered material. Small extreme-height difference is not mid-height or C1 localization. More grid resolution does not overcome the old occupancy LP's fractional barriers.

## 6. Checks and provenance

The newest standard-library checker `computer-assisted/check_positive_face_density.py` ran under a five-second limit in about 0.007 seconds internally. It passed 93 named checks, 80 rounding-depth instances and 101 rational convex-strip samples, with four negative controls. Its executed bytes match Git blob `761900d38540215411807cbd7a40c23cd6927b2f`; the committed JSON gives SHA-256 and exact scope.

Those checks do not verify the continuum approximation or historical motion/width proofs. RR/PD/PS are hand arguments. Two exploratory five-second-capped rectangle/parallelogram calculations produced no sharp inequality and are not proof inputs. No long search or new global certificate was run.

Older uploaded packages and author diagnostics remain preserved at their provenance checkpoints. Distinguish fresh runs, original author records, exact arithmetic regression and complete geometric certificates. No CI or Lean/Lake compilation was used.

## 7. Restart procedure

Query the live branch, read this handoff and [ROADMAP.md](ROADMAP.md), then review RR/PD/PS before using the new reduction. A specific gap found in any prerequisite must be stated and repaired rather than hidden by the scope labels.

The full-turn task is now one precisely specified sharp class, saturated positive opposite faces; the point-face upper value follows by approximation if that class is bounded. This does not mean the hard geometry has disappeared. The remaining partial-turn width-bump problem remains separate.

Keep actual motion coverage, retained support points, all positive corrections and supremum-versus-attainment quantifiers visible. Keep scripts short and commits frequent. PR #3 remains open and draft; unrestricted optimality and independent verification remain unfinished.
