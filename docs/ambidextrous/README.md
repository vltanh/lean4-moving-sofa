# Ambidextrous sofa research

**Start with [HANDOFF.md](HANDOFF.md), then [ROADMAP.md](ROADMAP.md). Unrestricted optimality is not proved.** The written chain now covers the weighted one-turn value, all full-turn aligned positive faces, and the left-right reflection-symmetric common incoming unit-span class. The remaining asymmetric end-face and partial-turn cases are open. Unrestricted uniqueness is deferred.

Branch: `research/ambidextrous-pen-and-paper`; draft [PR #3](https://github.com/vltanh/lean4-moving-sofa/pull/3), base `main`. All research changes remain under this directory. The mathematical chain is self-reviewed, not independently refereed or kernel-verified.

## Latest ordinary-area results

**[FAS1](full-turn-aligned-short-faces.md):** a compact connected ambidextrous body with both full conventional turns and identical positive-length top/bottom hull faces has area at most M. The common face no longer needs length at least one. No curvature, smoothness, symmetry or endpoint-height hypothesis is added.

The proof combines retained-point flank inequalities with an exact polynomial identity. A failed no-clipping condition would force width below 1201/600; [SW1](scaled-width-margin.md), obtained by uniformly scaling into the existing analytic width theorem, already excludes widths up to 1001/500. Thus both niches lie over the common face, and the weighted inequalities add without a clipping error.

**[UC1--UC2](full-turn-unit-chord-obstruction.md):** under both full turns, a retained unit vertical column cannot have points more than one unit away on both horizontal sides. The two turns would require incompatible half-angle inequalities `r+s>1` and `r+s+3rs<1`. This places any point face, at width greater than two, in one of the two unit end strips. The argument is independent of weighted optimality and area bounds.

**[RS2](reflection-symmetric-optimality.md):** the reference is optimal among bodies invariant under reflection in a line perpendicular to the common incoming strip, in the unit-span normalization. Symmetric motions and full turns are not assumed. Reflection supplies complementary hallway angles; a competitive body therefore admits both full turns. Centered point faces contradict UC, while centered positive faces are aligned by FD. FAS then gives the area bound.

These are class theorems. The existence of a reflection-symmetric unrestricted maximizer has not been proved.

## The remaining classes and a ruled-out reduction

[FD1](full-turn-face-dichotomy.md) classifies the two nondegenerate faces of a full-turn body of width greater than two. They are either identical and span the central interval, or lie in opposite unit end strips. The first case is now covered by FAS. With UC, a remaining full-turn counterexample must have an end-strip point face or two positive faces in opposite end strips. General asymmetric partial-turn bodies also remain.

[RA1](reflection-averaging-obstruction.md) shows that naive Minkowski averaging of an actual body with its left-right reflection is not a feasibility-preserving reduction. Even on the already symmetric reference, this averaging adds central top and bottom midpoint points and contradicts UC while keeping the same hull. A different cap or motion symmetrization still requires an actual-area proof.

FD3 also rules out the naive limit from aligned positive faces to an aligned point face at fixed unit span and width greater than two. The limiting face length is bounded below by W-2. Shrinking first changes the needed normalization and does not automatically solve that obstruction.

## Further short-face admission criteria

[SCG1](short-chord-optimality.md) gives an explicit six-retained-point certificate for full turns and zero clipping. [CSF1](central-short-face-optimality.md) turns it into width/height conditions when both faces span the central interval. It includes cases with common face length below one and supplies an actual feasible ellipse example with width 23/10 and face length 9/10.

The original parameter-only illustration was not a verified realization and has been replaced. [The review](short-face-extension-review.md) records that correction, the distinction between actual retention and hull membership, the exact FAS proof, and the short checks.

## The weighted value used by the area comparisons

[WV2](one-turn-weighted-value.md) proves in the current written chain

$$\sup_U\{|U|-|N(U)|-W(U)/2\}=M/2,$$

for normalized full-right-angle caps, subtracting the whole niche. The reference constant is

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

The proof first establishes unit curvature at an attained weighted maximizer. It uses the earlier finite-selection and exposure results, the ordinary Gerver area theorem on a feasible one-turn body, and VE's globally visible two-source flux argument. Only then are SR1 and AF3 applied. The [weighted review](weighted-value-proof-review.md) records dependencies and the main continuum verification obligations. No uncompiled source is treated as kernel verification.

For general full-turn cap pairs with nonempty fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

The remaining sharp comparison is G<=Delta(U)+Delta(V), with Delta=M/2-Psi, or another valid ordinary-area bound. The new class results do not establish that comparison universally.

## Retained history and execution

AW-W and AL1 supply analytic width bounds; SW1 strengthens the competitive lower restriction to W>1001/500. AM2 and TE1 retain their restricted exact computer certificates, not a global covering. The latest FAS/UC/RS arguments do not rely on those large certificates. Original uploaded packages and diagnostic outputs remain preserved with provenance in their respective reviews.

Negative controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain relevant. Repair, saturation, auxiliary data admission and candidate proximity did not rescue those failed enclosures. The occupancy relaxation has its documented fractional barriers; more grid resolution alone does not solve them.

Only short checks are used in this continuation. [check_short_face_extension.py](computer-assisted/check_short_face_extension.py) and [check_unit_chord.py](computer-assisted/check_unit_chord.py) use standard-library exact arithmetic, with records in the same directory. Each completed in about 0.03 seconds under a five-second limit. These are algebra and regression checks, not independent verification of the continuum proofs or the weighted chain.

No CI, Lean/Lake compilation, dependency installation or manuscript build was used. Every substantive commit includes `[skip ci]`. Keep PR #3 open and draft while the unrestricted ordinary-area bound remains unproved.
