# Active roadmap: asymmetric end-face geometry and actual area

**Unrestricted optimality remains unproved.** WV2 establishes the signed weighted one-turn value in the written chain. FAS1 now covers every full-turn aligned positive-face body, regardless of face length. RS2 also covers left-right reflection-symmetric bodies in the common incoming representation, without assuming full or symmetric motions. The remaining unrestricted cases are not eliminated by these class theorems. Uniqueness remains deferred.

Read [HANDOFF.md](HANDOFF.md), [short-face-extension-review.md](short-face-extension-review.md), and the latest [switching](full-turn-unit-chord-obstruction.md) and [reflection](reflection-symmetric-optimality.md) notes. All written results are self-reviewed; the historical dependency chain has not been independently refereed or kernel-verified.

## 1. Acceptance criterion and execution limits

For one attained global ambidextrous maximizer S, establish |S|<=M, where

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

Do not impose unrestricted equality classification first. Prefer hand proofs. Use brief computations to reject faulty premises or check explicit algebra: maximum 30 seconds per invocation, preferably external five/ten-second caps. No large search or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantial positive and negative findings with `[skip ci]`, under docs/ambidextrous.

## 2. Weighted value: retained as a written input

[WV2](one-turn-weighted-value.md) proves

$$\sup_U\Psi(U)=M/2,\qquad\Psi(U)=|U|-|N(U)|-W(U)/2,$$

on the normalized full-right-angle cap domain. The entire niche is subtracted. PA/WP/WR establish attainment and selected-polygon regularity. AR/PT/TS/EB establish same-sign bounds, a positive top face, a half-height niche and actual limiting exposure balance. TF/HF supply confinement and the stationary core. CG/SE force one good quarter, using an existing ordinary Gerver area bound on a genuinely feasible one-turn body. VE's globally visible source-flux lower bound and WV's energy contradiction force the other quarter good. AR4/SR1/AF3 then supply the value.

The main independent-review point remains VE's continuum source-flux argument and its historical inputs. No new computation verifies that chain. Do not reopen weighted maximization unless a particular implication is found incorrect; do not give an arbitrary ambidextrous cap the premise of weighted maximality.

## 3. Completed actual-body classes

### Full turns and any aligned positive faces

[FAS1](full-turn-aligned-short-faces.md) proves |S|<=M whenever the common unit-span hull has identical top and bottom exposed faces of positive length and both conventional turns are full. No minimum positive length, curvature, smoothness, reflection symmetry or endpoint-height condition remains.

The proof derives the two SCG no-clipping conditions from retained-point flank bounds. Their failure would force width below 1201/600, while [SW1](scaled-width-margin.md) already excludes every width at most 1001/500>1201/600. SW1 is a uniform-scaling consequence of the analytic AW-W bound, not a new computational certificate. The polynomial estimate in FAS is an explicit sum of nonnegative terms.

The older FL/LF conclusions are retained: aligned faces of length at least one force full turns; two faces longer than one force alignment as well. They require no separate full-turn premise.

### Additional short-face classes force full turns

[SCG1](short-chord-optimality.md) gives two explicit inequalities in six actual retained points. They force every needed angle and zero clipping. [CSF1](central-short-face-optimality.md) gives sufficient central-face width/height regimes, including W>1+sqrt(2) with unrestricted extreme heights, W>7/3 for extreme heights in [1/4,3/4], and W>sqrt(5) for mid-height extremes.

The right-endpoint retention is proved only after alignment; hull-interior face points are not silently treated as actual points of S. A fully verified elliptic example in CSF has face length 9/10, so the admitted positive short-face class is nonempty.

### Left-right reflection symmetry

[RS1--RS2](reflection-symmetric-optimality.md) complete both turns of a competitive body symmetric under J(x,y)=(-x,y). Reflecting a lower hallway at t exchanges its two normals and gives the same body's hallway at pi/2-t. The initial motion beyond pi/4 therefore covers the whole quarter. The upper turn follows independently.

The two horizontal faces are centered. A point face would be central and contradict UC2; opposite-end positive faces cannot be centered. FD1 consequently forces identical positive faces, and FAS1 proves the area bound. Thus the reference is optimal within this stated reflection-symmetric incoming class, without a symmetric-motion premise.

This does not prove existence of a symmetric unrestricted maximizer. Invariance of a nonconvex optimization problem under reflection is insufficient.

## 4. Exact remaining full-turn alternatives

For width W>2 and two full turns, [FD1](full-turn-face-dichotomy.md) classifies positive face intervals: either they coincide and span [l+1,r-1], or they lie in opposite unit end strips [l,l+1] and [r-1,r]. FAS handles the coincident case.

[UC1](full-turn-unit-chord-obstruction.md) proves that a retained unit vertical column cannot have actual points at horizontal distances greater than one on both sides. Each motion supplies an interior angle where both safe-wall alternatives hold; the right flank would require r+s>1 while the left would require r+s+3rs<1, for positive half-angle parameters r,s. This contradiction is independent of weighted optimality or any numerical area bound.

UC2 then places every point face of a full-turn body in one of the two unit end strips. The central common-point case is excluded.

A possible full-turn counterexample must therefore have either:

- a point face in an end strip; or
- two nondegenerate faces in opposite end strips.

These configurations necessarily break the left-right symmetry covered by RS2. They are not proved suboptimal. General partial-turn competitors also remain outside the covered SCG/CSF/RS regimes.

## 5. What a final comparison still needs

For full-turn cap pairs with nonempty surviving fibers,

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

Since Delta(U)=M/2-Psi(U)>=0, one possible remaining theorem is G<=Delta(U)+Delta(V). FAS proves G=0 in its admitted class, not universally. A valid area-improving operation at a maximizing asymmetric end-face body, or another ordinary-area inequality, could replace this deficit comparison.

Partial turns require actual angle coverage or an explicit bound on the missing geometry. A finite support neighborhood is not automatically the topology required by a local analytic theorem. Known end-point-face perturbations approach M, so no fixed strict gap below M can dispose of the whole remaining class.

## 6. Negative approaches already eliminated

[FD3](full-turn-face-dichotomy.md) rules out approximating an aligned point-face hull of width W>2 by aligned positive-face full-turn unit-span hulls: the approximating face lengths are at least W_j-2 and remain positive in the limit. Shrinking first changes the required vertical span; restoring it requires a separate feasible operation.

[RA1](reflection-averaging-obstruction.md) rules out naive Minkowski averaging of actual bodies with their reflection. Applied even to the already symmetric reference, the average fills central top and bottom midpoint points while retaining width greater than two. The same hull forces the incoming orientation, reflection completes the turns, and UC1 makes the resulting body infeasible. This does not rule out a different, proved cap or motion symmetrization.

Earlier controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain in force. Repair, saturation and auxiliary data admission alone do not establish the actual-area inequality. Canonical-wing accounting keeps both negative winding and uncovered material. Small extreme-height difference is not mid-height or C1 localization.

## 7. Checks and existing certificates

The new standard-library short-face checker verifies the FAS polynomial coefficient by coefficient and finite rational regressions; its runtime is about 0.03 seconds under a five-second cap. The separate UC checker verifies the switching identity and strict-boundary examples in about 0.03 seconds. Executed-source hashes and scope are recorded. Neither checks the full continuum proof or the historical WV chain.

AW-W and AL1 are analytic width restrictions; SW1 strengthens the lower competitive restriction to W>1001/500. AM2 and TE1 retain their scoped exact computer exclusions but are not premises of the new hand-proof case closures. No complete global certificate exists. The occupancy model's fractional barriers still prevent simply refining the old unconditioned LP.

## 8. Next work

Choose a specific asymmetric end-face comparison or a rigorously specified partial-turn case. A genuine area-preserving or area-improving symmetry reduction could also finish the value, but RA1 shows the simplest average is not it. Do not assume such a reduction or return to an already disproved enlargement.

Keep actual retained points, full-turn hypotheses, positive clipping corrections and verification limits visible. Commit negative findings. Unrestricted optimality, independent review and global assembly remain unfinished; PR #3 stays open and draft.
